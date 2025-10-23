param(
  [string]$Root = ".",
  [string]$OutDir = ".\bench\sha_sweep",
  [string]$PythonExe = "python",
  [int[]]  $RoundsList = @(8, 12, 16, 20, 24),
  [int[]]  $PrefixBitsList = @(0, 8, 12, 16),
  [int[]]  $DeviationsList = @(0, 1, 2),
  [int[]]  $Seeds = @(1,2,3),
  [int]    $TimeoutSec = 120
)

$ErrorActionPreference = "Stop"
New-Item -ItemType Directory -Path $OutDir -Force | Out-Null
$logs = Join-Path $OutDir "logs"
New-Item -ItemType Directory -Path $logs -Force | Out-Null

function Run-One($rounds,$prefix,$dev,$seed){
  $name = "sha_r${rounds}_p${prefix}_d${dev}_s${seed}.json"
  $outf = Join-Path $OutDir $name
  $logf = Join-Path $logs  ([IO.Path]::GetFileNameWithoutExtension($name) + ".log")

  $psi = [System.Diagnostics.ProcessStartInfo]::new()
  $psi.FileName = $PythonExe
  $psi.Arguments = @(
    (Join-Path $Root "sha256_prune.py"),
    "--rounds", $rounds,
    "--prefix-bits", $prefix,
    "--deviations", $dev,
    "--seed", $seed,
    "--out", $outf
  ) -join " "
  $psi.WorkingDirectory = $Root
  $psi.RedirectStandardOutput = $true
  $psi.RedirectStandardError  = $true
  $psi.UseShellExecute = $false
  $p = [System.Diagnostics.Process]::new()
  $p.StartInfo = $psi

  [void]$p.Start()
  $script:so = ""
  $script:se = ""
  $outHandler = [System.Diagnostics.DataReceivedEventHandler]{ param($s,$e) if ($e.Data){ $script:so += $e.Data + "`n" } }
  $errHandler = [System.Diagnostics.DataReceivedEventHandler]{ param($s,$e) if ($e.Data){ $script:se += $e.Data + "`n" } }
  $p.add_OutputDataReceived($outHandler)
  $p.add_ErrorDataReceived($errHandler)
  $p.BeginOutputReadLine()
  $p.BeginErrorReadLine()

  if (-not $p.WaitForExit($TimeoutSec*1000)){
    try { $p.Kill($true) } catch {}
    $exit = -1
  } else {
    $exit = $p.ExitCode
  }

  $log = @()
  $log += "CWD: $Root"
  $log += "CMD: $($psi.FileName) $($psi.Arguments)"
  $log += "EXIT: $exit"
  $log += "`n--- STDOUT ---`n$script:so`n"
  $log += "`n--- STDERR ---`n$script:se`n"
  Set-Content -LiteralPath $logf -Value $log -Encoding UTF8

  if (-not (Test-Path -LiteralPath $outf)){
    return @{
      File = $name; Rounds=$rounds; PrefixBits=$prefix; Deviations=$dev; Seed=$seed;
      Status="no_file"; TimeSec = [double]::NaN
    }
  }
  try {
    $json = Get-Content -Raw -LiteralPath $outf | ConvertFrom-Json
    return @{
      File = $name; Rounds=$rounds; PrefixBits=$prefix; Deviations=$dev; Seed=$seed;
      Status=$json.status; TimeSec=[double]$json.solve_time_sec
    }
  } catch {
    return @{
      File = $name; Rounds=$rounds; PrefixBits=$prefix; Deviations=$dev; Seed=$seed;
      Status="parse_error"; TimeSec=[double]::NaN
    }
  }
}

$rows = New-Object System.Collections.Generic.List[object]
foreach($r in $RoundsList){
  foreach($p in $PrefixBitsList){
    foreach($d in $DeviationsList){
      foreach($s in $Seeds){
        Write-Host "[RUN] rounds=$r prefix=$p dev=$d seed=$s"
        $rows.Add( (Run-One -rounds $r -prefix $p -dev $d -seed $s) )
      }
    }
  }
}

$csv = Join-Path $OutDir "sha_sweep_results.csv"
$rows | Export-Csv -LiteralPath $csv -NoTypeInformation -Delimiter ';' -Encoding UTF8
Write-Host "Wrote results → $csv"
Write-Host "Logs in       → $logs"
