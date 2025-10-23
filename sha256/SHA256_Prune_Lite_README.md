\# SHA256-Prune (Lite) — README



This is a \*\*lightweight benchmarking harness\*\* that instantiates a \*\*constraint-pruned\*\* fragment of the SHA-256 pipeline in Z3 and measures solver effort while you tighten the constraints.



It is \*lite\* because it:

\- models only a \*\*reduced front\*\* of the SHA-256 round function (no full compression schedule or message padding),

\- focuses on \*\*bit-vector constraints\*\* that are representative for pruning (prefix bits, fixed schedule words, and limited “deviation” flips),

\- avoids heavy encodings so you can run \*\*many experiments quickly\*\* on a laptop.



> Goal: observe how \*effort\* (Z3’s internal counters) behaves when constraints get stricter — ideally showing plateaus of effort while “precision”/strictness increases.



\## 1) Prerequisites

\- Python 3.10+

\- `z3-solver` Python package

```powershell

python -m pip install --upgrade z3-solver

Files:



sha256\_prune\_lite.py — the solver harness (JSON output).



sha\_aggregate.py — aggregates many JSONs into a CSV for plotting.



2\) CLI Usage (single run)

powershell

Code kopieren

python .\\sha256\_prune\_lite.py `

&nbsp; --rounds 12 `

&nbsp; --prefix-bits 4 `

&nbsp; --deviations 1 `

&nbsp; --dev-lo 0 --dev-hi 255 `

&nbsp; --fix-w-words 10 `

&nbsp; --timeout-sec 30 `

&nbsp; --seed 1 `

&nbsp; --out .\\bench\\sha\_sweep\\example.json

Key args



--rounds: 8/12/24/32 …



--prefix-bits: fixed output bits (↑ stricter)



--deviations: allowed bit flips in range



--dev-lo/--dev-hi: deviation bit range (e.g. 0..255)



--fix-w-words: number of fixed W\[i] (↑ easier)



--timeout-sec, --seed, --out



Output JSON



status ("sat"/"unsat"), solve\_time\_sec, z3\_stats (e.g., rlimit count, num allocs), config echo.



Use z3\_stats\["rlimit count"] or num allocs as effort proxies.



3\) Recommended presets

24 rounds — easy



powershell

Code kopieren

python .\\sha256\_prune\_lite.py `

&nbsp; --rounds 24 --prefix-bits 6 `

&nbsp; --deviations 1 --dev-lo 0 --dev-hi 255 `

&nbsp; --fix-w-words 12 `

&nbsp; --timeout-sec 120 --seed 1 `

&nbsp; --out .\\bench\\sha\_sweep\\r24\_easy.json

24 rounds — harder



powershell

Code kopieren

python .\\sha256\_prune\_lite.py `

&nbsp; --rounds 24 --prefix-bits 6 `

&nbsp; --deviations 2 --dev-lo 0 --dev-hi 255 `

&nbsp; --fix-w-words 10 `

&nbsp; --timeout-sec 180 --seed 1 `

&nbsp; --out .\\bench\\sha\_sweep\\r24\_hard.json

32 rounds — easy



powershell

Code kopieren

python .\\sha256\_prune\_lite.py `

&nbsp; --rounds 32 --prefix-bits 8 `

&nbsp; --deviations 1 --dev-lo 0 --dev-hi 255 `

&nbsp; --fix-w-words 14 `

&nbsp; --timeout-sec 180 --seed 1 `

&nbsp; --out .\\bench\\sha\_sweep\\r32\_easy.json

32 rounds — harder



powershell

Code kopieren

python .\\sha256\_prune\_lite.py `

&nbsp; --rounds 32 --prefix-bits 8 `

&nbsp; --deviations 2 --dev-lo 0 --dev-hi 255 `

&nbsp; --fix-w-words 12 `

&nbsp; --timeout-sec 240 --seed 1 `

&nbsp; --out .\\bench\\sha\_sweep\\r32\_hard.json

4\) Batch experiments (PowerShell)

Micro sweep (8/10/12)



powershell

Code kopieren

$root = "C:\\development\\art\_pv\_np"

$out  = "$root\\bench\\sha\_sweep\\micro"

New-Item -ItemType Directory -Force -Path $out | Out-Null



$rounds = 8,10,12; $prefix = 2,4; $devs = 1,2; $fixes = 10,9

$i = 0

foreach ($r in $rounds) { foreach ($p in $prefix) { foreach ($dv in $devs) {

&nbsp; foreach ($fw in $fixes) {

&nbsp;   $i++; $file = "$out\\sha\_r${r}\_p${p}\_dev${dv}\_fix${fw}.json"

&nbsp;   Write-Host "\[$i] r=$r p=$p dev=$dv fix=$fw → $file"

&nbsp;   python "$root\\sha256\_prune\_lite.py" `

&nbsp;     --rounds $r --prefix-bits $p `

&nbsp;     --deviations $dv --dev-lo 0 --dev-hi 255 `

&nbsp;     --fix-w-words $fw `

&nbsp;     --timeout-sec 30 --seed 1 `

&nbsp;     --out $file | Out-Host

}}}}

Extended sweep up to 32



powershell

Code kopieren

$root = "C:\\development\\art\_pv\_np"

$frontier = "$root\\bench\\sha\_sweep\\frontier32"

New-Item -ItemType Directory -Force -Path $frontier | Out-Null

$cfgs = @(

&nbsp; @{r=24; p=6; d=1; fix=12; seed=1},

&nbsp; @{r=24; p=6; d=2; fix=10; seed=1},

&nbsp; @{r=28; p=7; d=1; fix=13; seed=1},

&nbsp; @{r=28; p=7; d=2; fix=11; seed=1},

&nbsp; @{r=32; p=8; d=1; fix=14; seed=1},

&nbsp; @{r=32; p=8; d=2; fix=12; seed=1}

)

foreach ($c in $cfgs) {

&nbsp; $file = "$frontier\\sha\_r$($c.r)\_p$($c.p)\_dev$($c.d)\_fix$($c.fix)\_s$($c.seed).json"

&nbsp; python "$root\\sha256\_prune\_lite.py" `

&nbsp;   --rounds $($c.r) --prefix-bits $($c.p) `

&nbsp;   --deviations $($c.d) --dev-lo 0 --dev-hi 255 `

&nbsp;   --fix-w-words $($c.fix) `

&nbsp;   --timeout-sec 240 --seed $($c.seed) `

&nbsp;   --out $file | Out-Host

}

5\) Aggregate to CSV

powershell

Code kopieren

python .\\sha\_aggregate.py `

&nbsp; ".\\bench\\sha\_sweep\\frontier32\\\*.json" `

&nbsp; ".\\bench\\sha\_sweep\\frontier32\_summary.csv"

6\) Notes \& Limits

Toy/diagnostic slice (not full SHA-256 cryptanalysis).



Z3/version dependent.



For high --rounds with weak constraints, raise --timeout-sec or --fix-w-words.



bash

Code kopieren



\*\*Schnell speichern (PowerShell):\*\*

```powershell

$readme = @'

\[HIER DEN OBIGEN README-INHALT EINFÜGEN]

'@

$readme | Set-Content -LiteralPath .\\SHA256\_Prune\_Lite\_README.md -Encoding UTF8

