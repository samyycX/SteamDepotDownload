using System.Collections.Concurrent;
using SteamDepotDownload.Steam.Core.Depot;
using SteamDepotDownload.Steam.Core.Diagnostics;
using SteamDepotDownload.Steam.Shared.Auth;
using SteamDepotDownload.Steam.Shared.Depot;
using SteamDepotDownload.Steam.Shared.Session;
using SteamKit2;
using SteamKit2.Authentication;
using SteamKit2.CDN;
using SteamKit2.Internal;

namespace SteamDepotDownload.Steam.Core.Session;

internal sealed class CSteamSession : ISteamSession
{
    private const uint AnonymousDedicatedServerPackage = 17906;

    private readonly SteamClient _client;
    private readonly CallbackManager _manager;
    private readonly SteamUser _user;
    private readonly SteamApps _apps;
    private readonly SteamContent _content;
    private readonly SteamCloud _cloud;
    private readonly SteamUnifiedMessages _unifiedMessages;

    private readonly SteamCredentials _credentials;
    private readonly SteamSessionOptions _options;
    private readonly IAccountSettingsStore _store;

    private readonly CancellationTokenSource _shutdown = new();
    private readonly List<IDisposable> _subscriptions = [];
    private readonly SemaphoreSlim _connectGate = new(1, 1);

    private readonly ConcurrentDictionary<uint, KeyValue?> _appInfo = new();
    private readonly ConcurrentDictionary<uint, KeyValue?> _packageInfo = new();
    private readonly ConcurrentDictionary<uint, byte[]> _depotKeys = new();
    private readonly ConcurrentDictionary<string, byte[]> _branchPasswordHashes = new(StringComparer.OrdinalIgnoreCase);
    private readonly ConcurrentDictionary<(uint DepotId, string Host), string> _cdnAuthTokens = new();
    private readonly Lock _licenseLock = new();

    private Task? _pump;
    private TaskCompletionSource? _connected;
    private TaskCompletionSource<SteamUser.LoggedOnCallback>? _loggedOn;
    private TaskCompletionSource? _licenses;

    private Dictionary<uint, ulong> _packageTokens = [];
    private volatile bool _isLoggedOn;
    private bool _lancacheDetected;
    private bool _disposed;

    internal CSteamSession(SteamCredentials credentials, SteamSessionOptions options)
    {
        _credentials = credentials;
        _options = options;
        _store = options.AccountStore ?? new Auth.CFileAccountSettingsStore();

        var configuration = SteamConfiguration.Create(builder =>
        {
            builder.WithConnectionTimeout(options.ConnectionTimeout);
            builder.WithHttpClientFactory(_ => CHttpFactory.Create());

            if (options.CellIdOverride is { } cellId)
            {
                builder.WithCellID(cellId);
            }
        });

        _client = new SteamClient(configuration);
        _manager = new CallbackManager(_client);

        _user = _client.GetHandler<SteamUser>() ?? throw new DepotDownloadException("SteamKit is missing its SteamUser handler.");
        _apps = _client.GetHandler<SteamApps>() ?? throw new DepotDownloadException("SteamKit is missing its SteamApps handler.");
        _content = _client.GetHandler<SteamContent>() ?? throw new DepotDownloadException("SteamKit is missing its SteamContent handler.");
        _cloud = _client.GetHandler<SteamCloud>() ?? throw new DepotDownloadException("SteamKit is missing its SteamCloud handler.");
        _unifiedMessages = _client.GetHandler<SteamUnifiedMessages>() ?? throw new DepotDownloadException("SteamKit is missing its SteamUnifiedMessages handler.");

        _subscriptions.Add(_manager.Subscribe<SteamClient.ConnectedCallback>(OnConnected));
        _subscriptions.Add(_manager.Subscribe<SteamClient.DisconnectedCallback>(OnDisconnected));
        _subscriptions.Add(_manager.Subscribe<SteamUser.LoggedOnCallback>(OnLoggedOn));
        _subscriptions.Add(_manager.Subscribe<SteamUser.LoggedOffCallback>(OnLoggedOff));
        _subscriptions.Add(_manager.Subscribe<SteamApps.LicenseListCallback>(OnLicenseList));
    }

    public bool IsLoggedOn => _isLoggedOn;

    public string? AccountName { get; private set; }

    public ulong SteamId => _user.SteamID?.ConvertToUInt64() ?? 0;

    public uint CellId { get; private set; }

    public bool IsAnonymous => _user.SteamID?.AccountType == EAccountType.AnonUser;

    internal Client CreateCdnClient() => new(_client);

    internal SteamContent Content => _content;

    internal IAccountSettingsStore Store => _store;

    public IDepotFetcher CreateDownloader(DownloadConfig config) => new CDepotFetcher(this, config);

    internal async Task ConnectAsync(CancellationToken ct)
    {
        await _connectGate.WaitAsync(ct).ConfigureAwait(false);

        try
        {
            if (_isLoggedOn)
            {
                return;
            }

            _pump ??= Task.Factory.StartNew(PumpCallbacks, TaskCreationOptions.LongRunning).Unwrap();

            await DetectLancacheAsync().ConfigureAwait(false);

            Exception? last = null;

            for (var attempt = 1; attempt <= Math.Max(1, _options.MaxReconnectAttempts); attempt++)
            {
                ct.ThrowIfCancellationRequested();

                try
                {
                    await ConnectOnceAsync(ct).ConfigureAwait(false);
                    return;
                }
                catch (Exception ex) when (ex is not OperationCanceledException)
                {
                    last = ex;
                    CSteamLog.Warning(CSteamLog.Steam,
                        $"Connection attempt {attempt} failed: {ex.Message}");

                    _client.Disconnect();
                    await Task.Delay(TimeSpan.FromSeconds(attempt), ct).ConfigureAwait(false);
                }
            }

            throw new DepotDownloadException(
                $"Could not connect to Steam after {Math.Max(1, _options.MaxReconnectAttempts)} attempts.",
                last ?? new InvalidOperationException("no further detail"));
        }
        finally
        {
            _connectGate.Release();
        }
    }

    internal Task EnsureConnectedAsync(CancellationToken ct)
        => _isLoggedOn ? Task.CompletedTask : ConnectAsync(ct);

    public async Task<AppInfo?> GetAppInfoAsync(uint appId, CancellationToken ct = default)
    {
        var info = await GetProductInfoAsync(appId, ct).ConfigureAwait(false);
        if (info == null)
        {
            return null;
        }

        var common = info["common"];
        var depots = info["depots"];

        var branches = new List<BranchInfo>();
        if (depots != KeyValue.Invalid)
        {
            foreach (var branch in depots["branches"].Children)
            {
                branches.Add(new BranchInfo
                {
                    Name = branch.Name ?? string.Empty,
                    BuildId = branch["buildid"].AsUnsignedInteger(),
                    RequiresPassword = branch["pwdrequired"].AsBoolean(),
                    Description = branch["description"].AsString(),
                });
            }
        }

        var depotList = new List<DepotInfo>();
        if (depots != KeyValue.Invalid)
        {
            foreach (var depot in depots.Children)
            {
                if (!uint.TryParse(depot.Name, out var depotId))
                {
                    continue;
                }

                var config = depot["config"];
                var manifests = depot["manifests"];

                if (manifests == KeyValue.Invalid && depot["depotfromapp"] != KeyValue.Invalid)
                {
                    var otherAppId = depot["depotfromapp"].AsUnsignedInteger();

                    if (otherAppId != appId && otherAppId != 0)
                    {
                        var otherInfo = await GetProductInfoAsync(otherAppId, ct).ConfigureAwait(false);
                        var otherDepots = otherInfo?["depots"];

                        if (otherDepots != null && otherDepots != KeyValue.Invalid)
                        {
                            manifests = otherDepots[depot.Name!]["manifests"];
                        }
                    }
                }

                var branchNode = manifests == KeyValue.Invalid
                    ? KeyValue.Invalid
                    : manifests[DepotConstants.PublicBranch];

                depotList.Add(new DepotInfo
                {
                    DepotId = depotId,
                    AppId = depot["depotfromapp"] != KeyValue.Invalid
                        ? depot["depotfromapp"].AsUnsignedInteger()
                        : appId,
                    Name = depot["name"].AsString(),
                    ManifestId = CDepotFields.ReadGid(branchNode),
                    SizeOnDisk = CDepotFields.ReadSize(branchNode, depot),
                    DownloadSize = CDepotFields.ReadDownloadSize(branchNode),
                    Os = config["oslist"].AsString(),
                    Arch = config["osarch"].AsString(),
                    Language = config["language"].AsString(),
                    LowViolence = config["lowviolence"].AsBoolean(),
                    SharedInstall = depot["sharedinstall"].AsBoolean(),
                });
            }
        }

        return new AppInfo
        {
            AppId = appId,
            Name = common["name"].AsString() ?? $"app {appId}",
            Branches = branches,
            Depots = depotList,
        };
    }

    public async Task<IReadOnlyList<uint>> GetLicensedPackagesAsync(CancellationToken ct = default)
    {
        await EnsureConnectedAsync(ct).ConfigureAwait(false);
        await WaitForLicensesAsync(ct).ConfigureAwait(false);

        lock (_licenseLock)
        {
            return [.. _packageTokens.Keys];
        }
    }

    public async Task DisconnectAsync()
    {
        _isLoggedOn = false;

        if (_client.IsConnected)
        {
            _user.LogOff();
        }

        _client.Disconnect();
        await Task.CompletedTask.ConfigureAwait(false);
    }

    public async ValueTask DisposeAsync()
    {
        if (_disposed)
        {
            return;
        }

        _disposed = true;

        await DisconnectAsync().ConfigureAwait(false);

        await _shutdown.CancelAsync().ConfigureAwait(false);

        if (_pump != null)
        {
            try
            {
                await _pump.ConfigureAwait(false);
            }
            catch (OperationCanceledException)
            {
            }
        }

        foreach (var subscription in _subscriptions)
        {
            subscription.Dispose();
        }

        _subscriptions.Clear();
        _shutdown.Dispose();
        _connectGate.Dispose();
    }

    internal async Task<KeyValue?> GetProductInfoAsync(uint appId, CancellationToken ct)
    {
        if (_appInfo.TryGetValue(appId, out var cached))
        {
            return cached;
        }

        await EnsureConnectedAsync(ct).ConfigureAwait(false);

        var tokens = await _apps.PICSGetAccessTokens(appId, null).ToTask().WaitAsync(ct).ConfigureAwait(false);

        var request = new SteamApps.PICSRequest(appId);
        if (tokens.AppTokens.TryGetValue(appId, out var token))
        {
            request.AccessToken = token;
        }

        var result = await _apps.PICSGetProductInfo(request, package: null).ToTask().WaitAsync(ct).ConfigureAwait(false);

        if (result.Failed || result.Results == null)
        {
            throw new DepotDownloadException($"Could not fetch product info for app {appId}.");
        }

        foreach (var response in result.Results)
        {
            if (response.Apps.TryGetValue(appId, out var app))
            {
                _appInfo[appId] = app.KeyValues;
                return app.KeyValues;
            }
        }

        _appInfo[appId] = null;
        return null;
    }

    private async Task RequestPackageInfoAsync(IEnumerable<uint> packageIds, CancellationToken ct)
    {
        var missing = packageIds.Where(id => !_packageInfo.ContainsKey(id)).Distinct().ToList();
        if (missing.Count == 0)
        {
            return;
        }

        await EnsureConnectedAsync(ct).ConfigureAwait(false);

        Dictionary<uint, ulong> tokens;
        lock (_licenseLock)
        {
            tokens = new Dictionary<uint, ulong>(_packageTokens);
        }

        var requests = missing
            .Select(id => new SteamApps.PICSRequest(id, tokens.TryGetValue(id, out var t) ? t : 0))
            .ToList();

        var result = await _apps.PICSGetProductInfo([], requests).ToTask().WaitAsync(ct).ConfigureAwait(false);

        if (result.Failed || result.Results == null)
        {
            return;
        }

        foreach (var response in result.Results)
        {
            foreach (var (id, package) in response.Packages)
            {
                _packageInfo[id] = package.KeyValues;
            }

            foreach (var id in response.UnknownPackages)
            {
                _packageInfo[id] = null;
            }
        }
    }

    internal async Task<bool> HasAccessAsync(uint appId, uint depotId, CancellationToken ct)
    {
        await WaitForLicensesAsync(ct).ConfigureAwait(false);

        List<uint> packages;

        lock (_licenseLock)
        {
            packages = [.. _packageTokens.Keys];
        }

        if (IsAnonymous && !packages.Contains(AnonymousDedicatedServerPackage))
        {
            packages.Add(AnonymousDedicatedServerPackage);
        }

        if (packages.Count == 0)
        {
            return false;
        }

        await RequestPackageInfoAsync(packages, ct).ConfigureAwait(false);

        foreach (var packageId in packages)
        {
            if (!_packageInfo.TryGetValue(packageId, out var package) || package == null)
            {
                continue;
            }

            if (package["appids"].Children.Any(child => child.AsUnsignedInteger() == depotId))
            {
                return true;
            }

            if (package["depotids"].Children.Any(child => child.AsUnsignedInteger() == depotId))
            {
                return true;
            }
        }

        var info = await GetProductInfoAsync(appId, ct).ConfigureAwait(false);
        if (info != null && info["common"]["FreeToDownload"].AsBoolean())
        {
            return true;
        }

        return false;
    }

    internal async Task<bool> RequestFreeLicenseAsync(uint appId, CancellationToken ct)
    {
        await EnsureConnectedAsync(ct).ConfigureAwait(false);

        try
        {
            var result = await _apps.RequestFreeLicense(appId).ToTask().WaitAsync(ct).ConfigureAwait(false);

            if (result.Result != EResult.OK || !result.GrantedApps.Contains(appId))
            {
                return false;
            }

            lock (_licenseLock)
            {
                foreach (var packageId in result.GrantedPackages)
                {
                    _packageTokens.TryAdd(packageId, 0);
                }
            }

            return true;
        }
        catch (Exception ex) when (ex is AsyncJobFailedException or TaskCanceledException)
        {
            return false;
        }
    }

    internal async Task<byte[]?> GetDepotKeyAsync(uint depotId, uint appId, CancellationToken ct)
    {
        if (_depotKeys.TryGetValue(depotId, out var cached))
        {
            return cached;
        }

        await EnsureConnectedAsync(ct).ConfigureAwait(false);

        try
        {
            var result = await _apps.GetDepotDecryptionKey(depotId, appId).ToTask().WaitAsync(ct).ConfigureAwait(false);

            if (result.Result != EResult.OK)
            {
                CSteamLog.Warning(CSteamLog.Depot,
                    $"No decryption key for depot {depotId}: {result.Result}.");
                return null;
            }

            _depotKeys[depotId] = result.DepotKey;
            return result.DepotKey;
        }
        catch (AsyncJobFailedException)
        {
            return null;
        }
    }

    internal async Task<ulong> GetManifestRequestCodeAsync(uint depotId, uint appId, ulong manifestId,
        string branch, CancellationToken ct)
    {
        await EnsureConnectedAsync(ct).ConfigureAwait(false);

        var passwordHash = GetBranchPasswordHash(branch);

        return await _content
            .GetManifestRequestCode(depotId, appId, manifestId, branch, passwordHash)
            .WaitAsync(ct)
            .ConfigureAwait(false);
    }

    internal async Task<string?> GetCdnAuthTokenAsync(uint appId, uint depotId, string host, CancellationToken ct)
    {
        if (_cdnAuthTokens.TryGetValue((depotId, host), out var cached))
        {
            return cached;
        }

        await EnsureConnectedAsync(ct).ConfigureAwait(false);

        var result = await _content.GetCDNAuthToken(appId, depotId, host).WaitAsync(ct).ConfigureAwait(false);

        if (result.Result != EResult.OK)
        {
            CSteamLog.Warning(CSteamLog.Cdn, $"CDN auth token for {host} refused: {result.Result}.");
            return null;
        }

        _cdnAuthTokens[(depotId, host)] = result.Token;
        return result.Token;
    }

    internal async Task<PublishedFileDetails?> GetPublishedFileDetailsAsync(ulong publishedFileId, CancellationToken ct)
    {
        await EnsureConnectedAsync(ct).ConfigureAwait(false);

        var service = _unifiedMessages.CreateService<PublishedFile>();
        var request = new CPublishedFile_GetDetails_Request();
        request.publishedfileids.Add(publishedFileId);

        var response = await service.GetDetails(request).ToTask().WaitAsync(ct).ConfigureAwait(false);

        if (response.Result != EResult.OK)
        {
            throw new DepotDownloadException(
                $"Could not fetch details for published file {publishedFileId}: {response.Result}.");
        }

        var details = response.Body.publishedfiledetails.FirstOrDefault();
        return details?.result == (uint)EResult.OK ? details : null;
    }

    internal async Task<SteamCloud.UGCDetailsCallback> GetUgcDetailsAsync(ulong ugcId, CancellationToken ct)
    {
        await EnsureConnectedAsync(ct).ConfigureAwait(false);
        return await _cloud.RequestUGCDetails(ugcId).ToTask().WaitAsync(ct).ConfigureAwait(false);
    }

    internal async Task<IReadOnlyCollection<Server>> GetContentServersAsync(uint? cellId, CancellationToken ct)
    {
        await EnsureConnectedAsync(ct).ConfigureAwait(false);

        return await _content.GetServersForSteamPipe(cellId ?? CellId).WaitAsync(ct).ConfigureAwait(false);
    }

    internal async Task<KeyValue?> GetPrivateBranchDepotsAsync(uint appId, string branch, string password,
        CancellationToken ct)
    {
        await EnsureConnectedAsync(ct).ConfigureAwait(false);

        var check = await _apps.CheckAppBetaPassword(appId, password).ToTask().WaitAsync(ct).ConfigureAwait(false);

        if (check.Result != EResult.OK)
        {
            throw new DepotDownloadException($"Branch password rejected for app {appId}: {check.Result}.");
        }

        foreach (var (name, hash) in check.BetaPasswords)
        {
            _branchPasswordHashes[name] = hash;
        }

        if (!_branchPasswordHashes.TryGetValue(branch, out var branchHash))
        {
            throw new DepotDownloadException(
                $"The password was accepted but does not unlock branch '{branch}' of app {appId}.");
        }

        var tokens = await _apps.PICSGetAccessTokens(appId, null).ToTask().WaitAsync(ct).ConfigureAwait(false);
        tokens.AppTokens.TryGetValue(appId, out var accessToken);

        var beta = await _apps
            .PICSGetPrivateBeta(appId, accessToken, branch, branchHash)
            .ToTask()
            .WaitAsync(ct)
            .ConfigureAwait(false);

        if (beta.Result != EResult.OK)
        {
            throw new DepotDownloadException(
                $"Could not read the depot list for branch '{branch}' of app {appId}: {beta.Result}.");
        }

        return beta.DepotSection;
    }

    internal string? GetBranchPasswordHash(string branch)
        => _branchPasswordHashes.TryGetValue(branch, out var hash) ? Convert.ToHexStringLower(hash) : null;

    private async Task PumpCallbacks()
    {
        while (!_shutdown.IsCancellationRequested)
        {
            try
            {
                _manager.RunWaitCallbacks(TimeSpan.FromMilliseconds(200));
            }
            catch (Exception ex)
            {
                CSteamLog.Warning(CSteamLog.Steam, $"Callback pump error: {ex.Message}");
            }
        }

        await Task.CompletedTask.ConfigureAwait(false);
    }

    private async Task DetectLancacheAsync()
    {
        if (!_options.UseLancache || _lancacheDetected)
        {
            return;
        }

        try
        {
            await Client.DetectLancacheServerAsync().ConfigureAwait(false);
            _lancacheDetected = true;
            CSteamLog.Msg(CSteamLog.Cdn, "Using the Lancache instance found on this network.");
        }
        catch (Exception ex) when (ex is HttpRequestException or IOException or TaskCanceledException)
        {
            CSteamLog.Warning(CSteamLog.Cdn, $"No Lancache instance found: {ex.Message}");
        }
    }

    private async Task ConnectOnceAsync(CancellationToken ct)
    {
        _connected = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        _loggedOn = new TaskCompletionSource<SteamUser.LoggedOnCallback>(TaskCreationOptions.RunContinuationsAsynchronously);
        _licenses = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);

        _client.Connect();

        await _connected.Task.WaitAsync(_options.ConnectionTimeout, ct).ConfigureAwait(false);

        CSteamLog.Detailed(CSteamLog.Steam, "Connected to Steam, logging on.");

        await LogOnAsync(ct).ConfigureAwait(false);
    }

    private async Task LogOnAsync(CancellationToken ct)
    {
        if (_credentials.IsAnonymous)
        {
            _user.LogOnAnonymous(new SteamUser.AnonymousLogOnDetails
            {
                CellID = _options.CellIdOverride,
            });

            await AwaitLogOnAsync(allowTokenRetry: false, ct).ConfigureAwait(false);
            CSteamLog.Msg(CSteamLog.Steam, "Logged on anonymously.");
            return;
        }

        var details = new SteamUser.LogOnDetails
        {
            LoginID = _credentials.LoginId,
            ShouldRememberPassword = _credentials.RememberPassword,
            CellID = _options.CellIdOverride,
        };

        var storedAccount = _credentials.Username;
        var usingStoredToken = false;

        if (!_credentials.UseQrCode && storedAccount != null &&
            _store.GetRefreshToken(storedAccount) is { } refreshToken)
        {
            details.Username = storedAccount;
            details.AccessToken = refreshToken;
            usingStoredToken = true;

            CSteamLog.Detailed(CSteamLog.Steam, $"Using the remembered login for {storedAccount}.");
        }
        else
        {
            var poll = await BeginAuthSessionAsync(ct).ConfigureAwait(false);

            details.Username = poll.AccountName;
            details.AccessToken = poll.RefreshToken;
            storedAccount = poll.AccountName;

            if (!string.IsNullOrEmpty(poll.NewGuardData))
            {
                _store.SetGuardData(poll.AccountName, poll.NewGuardData);
            }

            if (_credentials.RememberPassword)
            {
                _store.SetRefreshToken(poll.AccountName, poll.RefreshToken);
            }

            _store.Save();
        }

        AccountName = storedAccount;

        _user.LogOn(details);

        try
        {
            await AwaitLogOnAsync(usingStoredToken, ct).ConfigureAwait(false);
        }
        catch (DepotDownloadException) when (usingStoredToken && storedAccount != null)
        {
            _store.RemoveRefreshToken(storedAccount);
            _store.Save();
            throw;
        }

        CSteamLog.Msg(CSteamLog.Steam, $"Logged on as {AccountName}.");
    }

    private async Task<AuthPollResult> BeginAuthSessionAsync(CancellationToken ct)
    {
        var authenticator = _options.Authenticator
            ?? throw new DepotDownloadException(
                "This login needs interactive input but no authenticator was supplied.");

        if (_credentials.UseQrCode)
        {
            var qrSession = await _client.Authentication.BeginAuthSessionViaQRAsync(new AuthSessionDetails
            {
                DeviceFriendlyName = Environment.MachineName,
                IsPersistentSession = _credentials.RememberPassword,
                Authenticator = new CAuthenticatorBridge(authenticator, ct),
            }).ConfigureAwait(false);

            qrSession.ChallengeURLChanged = () =>
                _ = authenticator.OnQrChallengeUrlAsync(qrSession.ChallengeURL, ct);

            await authenticator.OnQrChallengeUrlAsync(qrSession.ChallengeURL, ct).ConfigureAwait(false);

            return await qrSession.PollingWaitForResultAsync(ct).ConfigureAwait(false);
        }

        var username = _credentials.Username
            ?? throw new DepotDownloadException("A username is required for a password login.");

        var password = _credentials.PlainPassword;
        if (string.IsNullOrEmpty(password))
        {
            password = await authenticator.GetPasswordAsync(username, ct).ConfigureAwait(false);
        }

        var session = await _client.Authentication.BeginAuthSessionViaCredentialsAsync(new AuthSessionDetails
        {
            Username = username,
            Password = password,
            IsPersistentSession = _credentials.RememberPassword,
            GuardData = _store.GetGuardData(username),
            Authenticator = new CAuthenticatorBridge(authenticator, ct),
        }).ConfigureAwait(false);

        return await session.PollingWaitForResultAsync(ct).ConfigureAwait(false);
    }

    private async Task AwaitLogOnAsync(bool allowTokenRetry, CancellationToken ct)
    {
        var callback = await (_loggedOn?.Task ?? throw new InvalidOperationException("No logon in flight."))
            .WaitAsync(_options.ConnectionTimeout, ct)
            .ConfigureAwait(false);

        switch (callback.Result)
        {
            case EResult.OK:
                _isLoggedOn = true;
                CellId = callback.CellID;
                return;

            case EResult.InvalidPassword or EResult.Expired or EResult.Revoked when allowTokenRetry:
                throw new DepotDownloadException(
                    $"The remembered login is no longer valid ({callback.Result}); log in again.");

            case EResult.AccountLogonDenied:
                throw new DepotDownloadException("Steam Guard denied this logon.");

            default:
                throw new DepotDownloadException(
                    $"Logon failed: {callback.Result} / {callback.ExtendedResult}.");
        }
    }

    private async Task WaitForLicensesAsync(CancellationToken ct)
    {
        await EnsureConnectedAsync(ct).ConfigureAwait(false);

        if (IsAnonymous)
        {
            return;
        }

        var licenses = _licenses;
        if (licenses == null)
        {
            return;
        }

        try
        {
            await licenses.Task.WaitAsync(TimeSpan.FromSeconds(10), ct).ConfigureAwait(false);
        }
        catch (TimeoutException)
        {
        }
    }

    private void OnConnected(SteamClient.ConnectedCallback callback)
        => _connected?.TrySetResult();

    private void OnDisconnected(SteamClient.DisconnectedCallback callback)
    {
        _isLoggedOn = false;

        _connected?.TrySetException(new DepotDownloadException("Steam closed the connection."));
        _loggedOn?.TrySetException(new DepotDownloadException("Steam closed the connection during logon."));

        if (!callback.UserInitiated && !_shutdown.IsCancellationRequested)
        {
            CSteamLog.Warning(CSteamLog.Steam, "Disconnected from Steam.");
        }
    }

    private void OnLoggedOn(SteamUser.LoggedOnCallback callback)
        => _loggedOn?.TrySetResult(callback);

    private void OnLoggedOff(SteamUser.LoggedOffCallback callback)
    {
        _isLoggedOn = false;
        CSteamLog.Detailed(CSteamLog.Steam, $"Logged off: {callback.Result}.");
    }

    private void OnLicenseList(SteamApps.LicenseListCallback callback)
    {
        if (callback.Result == EResult.OK)
        {
            lock (_licenseLock)
            {
                _packageTokens = callback.LicenseList
                    .GroupBy(license => license.PackageID)
                    .ToDictionary(group => group.Key, group => group.First().AccessToken);
            }
        }

        _licenses?.TrySetResult();
    }
}
