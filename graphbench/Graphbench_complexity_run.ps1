<#  Graphbench_complexity_run.ps1  — PowerShell 7+
    Runs a planted-clique complexity sweep (20 steps), calls graphbench.py,
    captures logs (no async handlers → no runspace crash), enforces timeout,
    and aggregates metrics to CSV.
#>

param(
  [string]$Root       = "C:\development\art_pv_np",
  [string]$OutDir     = "C:\development\art_pv_np\bench\sweep",
  [string]$PythonExe  = "python",
  [int]   $D          = 128,
  [int]   $Kproj      = 32,
  [int]   $TimeoutSec = 450
)

$ErrorActionPreference = "Stop"
$ProgressPreference    = "SilentlyContinue"

function New-RunSpec($i){
  # n grows, k plateaus → difficulty rises (r = n/k)
  $n = 150 + 24*($i-1)        # 150,174,198,...
  $k = switch ($true) {
    { $i -le  5 } { 27 + [math]::Floor(($i-1)/2); break }   # 27..33
    { $i -le 10 } { 34 + [math]::Floor(($i-6)/2); break }   # 34..37
    { $i -le 15 } { 38 + [math]::Floor(($i-11)/2); break }  # 38..39
    default       { 40 }
  }
  [pscustomobject]@{
    n = $n; k = $k; seed = $i
    r = [math]::Round($n / [double]$k, 2, [System.MidpointRounding]::AwayFromZero)
  }
}

function Invoke-GraphbenchRun($spec){
  $seed = $spec.seed; $n = $spec.n; $k = $spec.k; $r = $spec.r
  $rName  = $r.ToString([System.Globalization.CultureInfo]::InvariantCulture)

  New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
  $logDir  = Join-Path $OutDir "logs"; New-Item -ItemType Directory -Force -Path $logDir | Out-Null

  $base     = "pc_n${n}_k${k}_r${rName}_seed${seed}"
  $jsonOut  = Join-Path $OutDir  ($base + ".jsonl")
  $stdoutF  = Join-Path $logDir  ($base + ".stdout")
  $stderrF  = Join-Path $logDir  ($base + ".stderr")
  $logFile  = Join-Path $logDir  ($base + ".log")

  Write-Host ("[{0,2}/20] Run  n={1}, k={2}, r={3}" -f $seed, $n, $k, $rName)

  $args = @(
    (Join-Path $Root "graphbench.py"),
    "--problem","planted_clique",
    "--n",$n,"--p","0.5","--k_clique",$k,
    "--d",$D,"--k_proj",$Kproj,
    "--n_train_yes","250","--n_train_no","250",
    "--n_val_yes","125","--n_val_no","125",
    "--n_test_yes","250","--n_test_no","250",
    "--seed",$seed,"--safety","0.02",
    "--out",$jsonOut
  )

  # Build process (sync, redirected; NO async handlers)
  $psi = [System.Diagnostics.ProcessStartInfo]::new()
  $psi.FileName = $PythonExe
  foreach($a in $args){ [void]$psi.ArgumentList.Add($a) }
  $psi.WorkingDirectory       = $Root
  $psi.RedirectStandardOutput = $true
  $psi.RedirectStandardError  = $true
  $psi.UseShellExecute        = $false
  $proc = [System.Diagnostics.Process]::new()
  $proc.StartInfo = $psi

  $null = $proc.Start()

  # Synchronous read with timeout
  $sw = [System.Diagnostics.Stopwatch]::StartNew()
  $stdout = ""
  $stderr = ""
  while (-not $proc.HasExited) {
    Start-Sleep -Milliseconds 50
    if ($sw.ElapsedMilliseconds -gt ($TimeoutSec * 1000)) {
      try { $proc.Kill($true) } catch {}
      break
    }
  }
  # After exit/kill, drain pipes
  try { $stdout = $proc.StandardOutput.ReadToEnd() } catch {}
  try { $stderr = $proc.StandardError.ReadToEnd() } catch {}

  $exit = if ($proc.HasExited) { $proc.ExitCode } else { "TIMEOUT" }

  # Write combined log
  $cmdLine = "$PythonExe " + ($args -join ' ')
  @(
    "CWD: $Root",
    "CMD: $cmdLine",
    "EXIT: $exit",
    "",
    "--- STDOUT ---",
    $stdout.TrimEnd(),
    "",
    "--- STDERR ---",
    $stderr.TrimEnd()
  ) -join "`r`n" | Set-Content -Path $logFile -Encoding UTF8

  # Also keep raw stdout/stderr (optional)
  Set-Content -Path $stdoutF -Value $stdout -Encoding UTF8
  Set-Content -Path $stderrF -Value $stderr -Encoding UTF8

  if (Test-Path $jsonOut) {
    try {
      $raw = Get-Content -Raw -Path $jsonOut
      $obj = $raw | ConvertFrom-Json
      if ($obj -is [System.Array]) { $obj = $obj[-1] }  # last record if array
      return [pscustomobject]@{
        File     = (Split-Path $jsonOut -Leaf)
        n        = $n
        k        = $k
        r        = $r
        AUC_ROC  = '{0:N6}' -f $obj.test_metrics.AUC_ROC
        AUC_PR   = '{0:N6}' -f $obj.test_metrics.AUC_PR
        ACC_tau  = '{0:N6}' -f $obj.test_metrics.'ACC(tau)'
        Tau      = '{0:N6}' -f $obj.calibration.tau
      }
    } catch {
      Write-Warning "Could not parse metrics JSON for $(Split-Path $jsonOut -Leaf)"
      return $null
    }
  } else {
    Write-Warning "Run failed: n=$n,k=$k → No JSON output file (exit=$exit)"
    return $null
  }
}

Write-Host "=== Complexity sweep: 20 runs ==="
$rows = New-Object System.Collections.Generic.List[object]
1..20 | ForEach-Object {
  $spec = New-RunSpec $_
  $row  = Invoke-GraphbenchRun $spec
  if ($row) { $rows.Add($row) }
}

if ($rows.Count -eq 0) {
  Write-Warning "No valid runs parsed."
  return
}

$csvPath = Join-Path $OutDir "complexity_sweep_results.csv"
$rows | Export-Csv -NoTypeInformation -Encoding UTF8 -Path $csvPath

$rows | Sort-Object r | Format-Table -AutoSize File, n, k, r, AUC_ROC, AUC_PR, ACC_tau, Tau
Write-Host "`nWrote results → $csvPath"
Write-Host "Logs in       → $(Join-Path $OutDir 'logs')"
