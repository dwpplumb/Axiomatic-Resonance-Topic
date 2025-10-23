# SHA256-Prune: Constraint-Propagation Benchmark (Z3)

**Goal**: Measure how added constraints (hash prefix, bit deviations) prune the search space across a reduced number of SHA‑256 rounds, using an SMT solver (Z3 BitVec). This is an *educational benchmarking tool*, **not** a cryptanalysis toolkit.

## Files
- `sha256_prune.py` — Python CLI that builds a Z3 model for N rounds and applies constraints, then runs the solver and emits JSON.
- `SHA256_sweep.ps1` — PowerShell runner to sweep over rounds / prefix bits / deviations and aggregate results into a CSV.

## Install
```powershell
python -m pip install --upgrade z3-solver
```

## Single run
```powershell
python .\sha256_prune.py --rounds 8 --prefix-bits 12 --deviations 2 --seed 1 --out .\out\demo.json
```

## Sweep (PowerShell)
```powershell
New-Item -ItemType Directory -Path .\bench\sha_sweep -Force | Out-Null

.\SHA256_sweep.ps1 `
  -Root "." `
  -OutDir ".\bench\sha_sweep" `
  -PythonExe "python" `
  -RoundsList @(8,12,16,20,24) `
  -PrefixBitsList @(0,8,12,16) `
  -DeviationsList @(0,1,2) `
  -Seeds @(1,2,3) `
  -TimeoutSec 120
```

The script writes each JSON into `OutDir`, logs into `OutDir\logs`, and a summary CSV at `OutDir\sha_sweep_results.csv`.

## Notes
- Start small (8–16 rounds). Increase rounds or prefix length to see **path pruning** (UNSAT or rising solve-time).
- `--no-fix-w0123` disables the illustrative fixed W0..W3. Keep it ON for comparability.
- All 64 rounds are supported but will be slow.
