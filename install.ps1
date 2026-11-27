# Install the latest Vineflower Rust release for the current Windows user.
& {
    $ErrorActionPreference = 'Stop'
    $ProgressPreference = 'SilentlyContinue'

    function Get-ReleaseAsset([string] $Architecture) {
        switch ($Architecture) {
            'AMD64' { return 'vineflower-rs-x86_64-pc-windows-msvc.exe' }
            'ARM64' { return 'vineflower-rs-aarch64-pc-windows-msvc.exe' }
            default { throw "Unsupported Windows architecture: $Architecture" }
        }
    }

    function Add-InstallPath([string] $PathValue, [string] $Directory) {
        foreach ($entry in ($PathValue -split ';')) {
            $expanded = [Environment]::ExpandEnvironmentVariables($entry.Trim().Trim('"'))
            if ($expanded.TrimEnd('\') -ieq $Directory.TrimEnd('\')) { return $PathValue }
        }
        if ([string]::IsNullOrEmpty($PathValue)) { return $Directory }
        return "$Directory;$PathValue"
    }

    function Confirm-Download([string] $File, [string] $Manifest, [string] $Asset) {
        $pattern = '^([0-9a-fA-F]{64}) [ *]' + [regex]::Escape($Asset) + '$'
        $entries = @(Select-String -LiteralPath $Manifest -Pattern $pattern -CaseSensitive)
        if ($entries.Count -ne 1) { throw "Expected exactly one SHA256SUMS entry for $Asset." }
        $expected = $entries[0].Matches[0].Groups[1].Value
        if ((Get-FileHash -Algorithm SHA256 -LiteralPath $File).Hash -ine $expected) {
            throw "SHA-256 verification failed for $Asset."
        }
    }

    if ([Environment]::OSVersion.Platform -ne [PlatformID]::Win32NT) {
        throw 'This installer requires Windows.'
    }
    # Read the machine environment before consulting the emulated process.
    $arch = [Environment]::GetEnvironmentVariable('PROCESSOR_ARCHITECTURE', 'Machine')
    if (!$arch) { $arch = $env:PROCESSOR_ARCHITEW6432 }
    if (!$arch) { $arch = $env:PROCESSOR_ARCHITECTURE }
    $asset = Get-ReleaseAsset $arch
    $local = [Environment]::GetFolderPath([Environment+SpecialFolder]::LocalApplicationData)
    if (!$local) { throw 'Cannot locate the current user LocalAppData directory.' }
    $dir = Join-Path $local 'Programs\vineflower-rs'
    $exe = Join-Path $dir 'vineflower-rs.exe'
    $stage = Join-Path $dir ('.install-' + [guid]::NewGuid().ToString('N'))
    $null = [IO.Directory]::CreateDirectory($stage)
    $download = Join-Path $stage $asset
    $manifest = Join-Path $stage 'SHA256SUMS'
    $backup = Join-Path $stage 'previous.exe'
    $origin = 'https://github.com/YinMo19/vineflower-rs/releases/latest/download'
    $registry = $null
    $installed = $false
    $oldTls = [Net.ServicePointManager]::SecurityProtocol
    try {
        if ($PSVersionTable.PSEdition -eq 'Desktop' -and [int]$oldTls -ne 0) {
            [Net.ServicePointManager]::SecurityProtocol = $oldTls -bor [Net.SecurityProtocolType]::Tls12
        }
        Invoke-WebRequest -UseBasicParsing -Uri "$origin/$asset" -OutFile $download
        Invoke-WebRequest -UseBasicParsing -Uri "$origin/SHA256SUMS" -OutFile $manifest
        Confirm-Download $download $manifest $asset

        # Preserve the original registry type and unexpanded %VARIABLE% entries.
        $registry = [Microsoft.Win32.Registry]::CurrentUser.CreateSubKey('Environment')
        $raw = $registry.GetValue('Path', $null, [Microsoft.Win32.RegistryValueOptions]::DoNotExpandEnvironmentNames)
        $kind = if ($null -eq $raw) { [Microsoft.Win32.RegistryValueKind]::ExpandString } else { $registry.GetValueKind('Path') }
        $userPath = Add-InstallPath $raw $dir
        $processPath = $env:Path
        $pathChanged = $false
        try {
            if ($userPath -cne $raw) {
                $registry.SetValue('Path', $userPath, $kind)
                $pathChanged = $true
            }
            $env:Path = Add-InstallPath $processPath $dir
            if ([IO.File]::Exists($exe)) {
                [IO.File]::Replace($download, $exe, $backup)
            } else {
                [IO.File]::Move($download, $exe)
            }
            $installed = $true
        } catch {
            $env:Path = $processPath
            if ($pathChanged -and $registry.GetValue('Path', $null, [Microsoft.Win32.RegistryValueOptions]::DoNotExpandEnvironmentNames) -ceq $userPath) {
                if ($null -eq $raw) { $registry.DeleteValue('Path') } else { $registry.SetValue('Path', $raw, $kind) }
            }
            throw
        }
    } finally {
        if ($null -ne $registry) { $registry.Dispose() }
        if ($PSVersionTable.PSEdition -eq 'Desktop') { [Net.ServicePointManager]::SecurityProtocol = $oldTls }
        if (!$installed -and [IO.File]::Exists($backup)) {
            Write-Warning "The original executable is available at $backup."
        } else {
            Remove-Item -LiteralPath $stage -Recurse -Force -ErrorAction SilentlyContinue
        }
    }

    if ($pathChanged) {
        # Let Explorer pick up the new user PATH for newly opened terminals.
        try {
            if (!('VineflowerInstaller.EnvironmentNotification' -as [type])) {
                Add-Type -Namespace VineflowerInstaller -Name EnvironmentNotification -MemberDefinition @'
[System.Runtime.InteropServices.DllImport("user32.dll", CharSet=System.Runtime.InteropServices.CharSet.Unicode)]
public static extern System.IntPtr SendMessageTimeout(System.IntPtr hWnd, uint message, System.UIntPtr wParam, string lParam, uint flags, uint timeout, out System.UIntPtr result);
'@
            }
            $result = [UIntPtr]::Zero
            $null = [VineflowerInstaller.EnvironmentNotification]::SendMessageTimeout([IntPtr]0xffff, 0x1a, [UIntPtr]::Zero, 'Environment', 2, 1000, [ref]$result)
        } catch {
            Write-Verbose "Could not broadcast the user PATH change: $_"
        }
    }
    Write-Host "Installed $exe"
}
