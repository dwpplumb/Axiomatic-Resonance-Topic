param(
  [string]$Root       = "C:\development\art_pv_np",
  [string]$OutDir     = "C:\development\art_pv_np\bench\pcd_sweep",
  [string]$PythonExe  = "python",

  [int]$N             = 150,
  [double]$P          = 0.5,
  [int[]]$KList       = @(10,12,14,16,18,20,24,28),

  [int]$Repeats       = 50,

  [int[]]$DList       = @(128,256),
  [int[]]$KprojList   = @(32,64),

  [int]$TrainYes      = 250,
  [int]$TrainNo       = 250,
  [int]$ValYes        = 125,
  [int]$ValNo         = 125,
  [int]$TestYes       = 250,
  [int]$TestNo        = 250,

  [double]$Safety     = 0.02,
  [int]$TimeoutSec    = 0   # 0 = kein Timeout (unbegrenzt)
)

# ---------- Helpers ----------
function New-Dir([string]$Path) {
  if (-not (Test-Path -LiteralPath $Path)) {
    New-Item -ItemType Directory -Force -Path $Path | Out-Null
  }
  return (Resolve-Path -LiteralPath $Path).Path
}

function Run-One(
  [string]$PythonExe,
  [string]$GraphbenchPy,
  [string]$OutAbs,
  [string]$LogsAbs,
  [int]$N, [double]$P, [int]$K, [int]$D, [int]$Kproj,
  [int]$TrainYes, [int]$TrainNo, [int]$ValYes, [int]$ValNo, [int]$TestYes, [int]$TestNo,
  [double]$Safety,
  [int]$Seed,
  [int]$TimeoutSec
){
  $name  = "pcd_n${N}_k${K}_d${D}_kp${Kproj}_s${Seed}"
  $json  = Join-Path $OutAbs "$name.jsonl"
  $logOut = Join-Path $LogsAbs "$name.stdout"
  $logErr = Join-Path $LogsAbs "$name.stderr"

  $args = @(
    $GraphbenchPy,
    "--problem", "planted_clique",
    "--n", $N, "--p", $P, "--k_clique", $K,
    "--d", $D, "--k_proj", $Kproj,
    "--n_train_yes", $TrainYes, "--n_train_no", $TrainNo,
    "--n_val_yes",   $ValYes,   "--n_val_no",   $ValNo,
    "--n_test_yes",  $TestYes,  "--n_test_no",  $TestNo,
    "--seed", $Seed,
    "--safety", $Safety,
    "--out", $json
  )

  $psi = New-Object System.Diagnostics.ProcessStartInfo
  $psi.FileName = $PythonExe
  $psi.ArgumentList.Clear()
  foreach($a in $args){ [void]$psi.ArgumentList.Add([string]$a) }
  $psi.WorkingDirectory = Split-Path -Parent $GraphbenchPy
  $psi.UseShellExecute = $false
  $psi.RedirectStandardOutput = $true
  $psi.RedirectStandardError  = $true
  $psi.CreateNoWindow = $true

  # WICHTIG: anderer Variablenname als $P!
  $proc = [System.Diagnostics.Process]::Start($psi)

  if ($TimeoutSec -gt 0) {
    $ok = $proc.WaitForExit($TimeoutSec * 1000)
    if (-not $ok) {
      try { $proc.Kill($true) } catch {}
      "[timeout] ${name}" | Out-File -FilePath $logErr -Append -Encoding utf8
      return 9002
    }
  } else {
    $proc.WaitForExit()
  }

  $stdout = $proc.StandardOutput.ReadToEnd()
  $stderr = $proc.StandardError.ReadToEnd()
  if ($stdout) { $stdout | Out-File -FilePath $logOut -Append -Encoding utf8 }
  if ($stderr) { $stderr | Out-File -FilePath $logErr -Append -Encoding utf8 }

  return $proc.ExitCode
}

# ---------- Main ----------
$ErrorActionPreference = "Stop"

$RootAbs = (Resolve-Path -LiteralPath $Root).Path
$OutAbs  = New-Dir $OutDir
$LogsAbs = New-Dir (Join-Path $OutAbs "logs")

$GraphbenchPy = Join-Path $RootAbs "graphbench.py"
$AggPy        = Join-Path $RootAbs "pcd_aggregate.py"

Write-Host "=== PCD Complexity Sweep ==="
Write-Host ("Root: {0}" -f $RootAbs)
Write-Host ("Out:  {0}" -f $OutAbs)
Write-Host ("Python: {0}" -f $PythonExe)
Write-Host ""

# Konfigurationsliste bauen
$cfgs = @()
foreach($D in $DList){
  foreach($Kp in $KprojList){
    foreach($K in $KList){
      $cfgs += [PSCustomObject]@{ N=$N; P=$P; K=$K; D=$D; Kproj=$Kp }
    }
  }
}

$cfgIdx = 0
foreach($cfg in $cfgs){
  $cfgIdx++
  $K     = [int]$cfg.K
  $D     = [int]$cfg.D
  $Kproj = [int]$cfg.Kproj

  Write-Host ("[Config {0}/{1}] Stufe: n={2}, k={3}, d={4}, kproj={5}" -f $cfgIdx, $cfgs.Count, $N, $K, $D, $Kproj)

  for($s=1; $s -le $Repeats; $s++){
    $rc = Run-One `
      -PythonExe $PythonExe `
      -GraphbenchPy $GraphbenchPy `
      -OutAbs $OutAbs -LogsAbs $LogsAbs `
      -N $N -P $P -K $K -D $D -Kproj $Kproj `
      -TrainYes $TrainYes -TrainNo $TrainNo -ValYes $ValYes -ValNo $ValNo -TestYes $TestYes -TestNo $TestNo `
      -Safety $Safety -Seed $s -TimeoutSec $TimeoutSec

    if ($rc -eq 0) {
      Write-Host ("  OK  seed={0} -> pcd_n{1}_k{2}_d{3}_kp{4}_s{0}" -f $s, $N, $K, $D, $Kproj)
    } elseif ($rc -eq 9002) {
      Write-Warning ("  TIMEOUT seed={0}" -f $s)
    } else {
      Write-Warning ("  FAIL rc={0} seed={1}" -f $rc, $s)
    }
  }

  # Aggregation pro Konfiguration
  if (Test-Path -LiteralPath $AggPy) {
    $glob = Join-Path $OutAbs ("pcd_n{0}_k{1}_d{2}_kp{3}_s*.jsonl" -f $N,$K,$D,$Kproj)
    $csv  = Join-Path $OutAbs ("pcd_summary_n{0}_k{1}_d{2}_kp{3}.csv" -f $N,$K,$D,$Kproj)
    try {
      # Umgebung ASCII-sicher
      $env:PYTHONIOENCODING = "utf-8"
      [Console]::OutputEncoding = [System.Text.UTF8Encoding]::new($false)
      & $PythonExe $AggPy $glob $csv 2>&1 | ForEach-Object { "$_" } | Write-Host
    } catch {
      Write-Warning ("Aggregation failed for k={0}, d={1}, kp={2}. Error: {3}" -f $K,$D,$Kproj,$_.Exception.Message)
    }
  } else {
    Write-Warning ("pcd_aggregate.py nicht gefunden: {0}" -f $AggPy)
  }

  Write-Host ""
}

Write-Host "=== Sweep fertig ==="
