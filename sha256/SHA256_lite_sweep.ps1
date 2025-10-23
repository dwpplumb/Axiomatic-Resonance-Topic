$root = "C:\development\art_pv_np"
$out  = "$root\bench\sha_sweep\frontier2"
New-Item -ItemType Directory -Force -Path $out | Out-Null

$rounds = 10,11,12
$prefix = 4,6,8
$devs   = 1,2
$fixes  = 10,11,12

$i = 0
foreach ($r in $rounds) {
  foreach ($p in $prefix) {
    foreach ($dv in $devs) {
      foreach ($fw in $fixes) {
        $i++
        $file = "$out\sha_r${r}_p${p}_dev${dv}_fix${fw}.json"
        Write-Host "[$i] r=$r p=$p dev=$dv fix=$fw → $file"
        python "$root\sha256_prune_lite.py" `
          --rounds $r --prefix-bits $p `
          --deviations $dv --dev-lo 64 --dev-hi 127 `
          --fix-w-words $fw `
          --timeout-sec 5 --seed 1 `
          --out $file | Out-Host
      }
    }
  }
}
