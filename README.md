# Bench Suite README

This repository bundles three small, self‑contained benchmarks you’ve been running together:

- **GraphBench (Planted Clique)** — an ART/“axiom projector”–style typical‑case detector on synthetic graphs.
- **PCD Sweep** — a production‑style sweep/aggregation wrapper around GraphBench to produce large CSVs for plots.
- **SHA256‑Prune (Lite)** — a tiny SAT/Z3 toy that explores how simple structural constraints prune the SHA‑256 search space (for fast micro‑runs).

The goal is uniform, repeatable runs that write **JSONL/JSON summaries** and **CSV aggregates** you can plot later.

---

## 1) Repository contents (key files)

```
graphbench.py                      # Core GraphBench (planted clique) implementation & CLI
Graphbench_run.ps1                 # Simple single-config runner for windows/PowerShell
Graphbench_complexity_run.ps1      # 20-step complexity sweep (n,k) for quick diagnostics
graphbench_aggregate.py            # Aggregates *.jsonl into a CSV (AUC_ROC, AUC_PR, ACC, τ, ...)

PCD_Sweep.ps1                      # Parametric sweep launcher for GraphBench (PCD), produces many JSONL + CSV
pcd_aggregate.py                   # Aggregates a folder of PCD JSONL into CSV summaries

sha256_prune_lite.py               # SHA256-Prune (Lite) — SAT/Z3 micro-bench with knobs (rounds/prefix/devs)
SHA256_lite_sweep.ps1              # Small preset sweep for the lite version
sha_aggregate.py                   # Aggregates SHA256-Prune(Lite) *.json into CSV
```

> You already have example output folders like `bench\pcd_sweep\...` and `bench\sha_sweep\...` — keep using those.

---

## 2) Environment & prerequisites

- **Python 3.10+** (3.13 works fine in your logs)
- **NumPy** (`pip install numpy`)
- For the SHA tools: **z3-solver** (`pip install z3-solver`)
- **PowerShell 7+** for the `.ps1` helpers (you’re on 7.5.x)

> All scripts are file‑path aware; pass absolute paths on Windows to avoid quoting issues.

---

## 3) GraphBench — core ideas

- Generate ER graphs **G(n,p)** and “yes” graphs with a **planted k‑clique**.
- Embed each graph via the top‑d eigen‑structure of normalized adjacency: **φ(x) ∈ ℝᵈ**.
- Build a **witness lift** φ(x,w) from positive training examples (use clique nodes).
- Learn a **rank‑k projector** \(P_k\) spanning the “witness subspace” from those lifts.
- Score **q(x) = ||P_k φ(x)||²**; calibrate a threshold **τ** on a validation split (with a small safety margin).
- Report **AUC_ROC**, **AUC_PR**, **ACC(τ)** on a test split.

This is a **typical‑case** detector; it does not claim worst‑case guarantees.

---

## 4) GraphBench — quick starts

### 4.1 Single run (PowerShell)

```powershell
# Paths (adjust)
$Root   = "C:\development\art_pv_np"
$OutDir = "C:\development\art_pv_np\bench\pcd_sweep"

python "$Root\graphbench.py" `
  --problem planted_clique `
  --n 150 --p 0.5 --k_clique 11 `
  --d 128 --k_proj 32 `
  --n_train_yes 250 --n_train_no 250 `
  --n_val_yes 125  --n_val_no 125 `
  --n_test_yes 250 --n_test_no 250 `
  --seed 1 --safety 0.02 `
  --out "$OutDir\pcd_n150_k11_d128_kp32_s1.jsonl"
```

### 4.2 Complexity sweep (20 steps)

```powershell
pwsh -File .\Graphbench_complexity_run.ps1 `
  -Root   "C:\development\art_pv_np" `
  -OutDir "C:\development\art_pv_np\bench\sweep" `
  -PythonExe "python" `
  -D 128 -Kproj 32 `
  -TimeoutSec 450
```

### 4.3 Aggregate to CSV

```powershell
python .\graphbench_aggregate.py `
  "C:\development\art_pv_np\bench\sweep\*.jsonl" `
  "C:\development\art_pv_np\bench\sweep\complexity_sweep_results.csv"
```

CSV columns:
```
file,n,k,ratio_k_sqrt_n,d,k_proj,tau,q_yes_med,q_no_med,AUC_ROC,AUC_PR,ACC_tau
```

- **ratio_k_sqrt_n = k / sqrt(n)** — useful hardness proxy.
- τ and the q‑medians come from validation; metrics from test.

---

## 5) PCD Sweep — large, controlled experiments

`PCD_Sweep.ps1` automates repeating GraphBench over many seeds and configs, creating per‑config CSVs **and** small aggregate CSVs with mean/±std (handy for plots).

### 5.1 Example: one config × 50 repeats

```powershell
pwsh -File .\PCD_Sweep.ps1 `
  -Root   "C:\development\art_pv_np" `
  -OutDir "C:\development\art_pv_np\bench\pcd_sweep\run1_k10_d128_kp32" `
  -PythonExe "python" `
  -N 150 -P 0.5 `
  -KList @(10) `                 # list → can sweep k
  -Repeats 50 `
  -DList @(128) `                # list → can sweep d
  -KprojList @(32) `             # list → can sweep k_proj
  -TrainYes 250 -TrainNo 250 -ValYes 125 -ValNo 125 -TestYes 250 -TestNo 250 `
  -Safety 0.02 `
  -TimeoutSec 0                  # 0 = no timeout
```

The script writes (per config):
```
...\pcd_summary_n150_k10_d128_kp32.csv        # 50 rows (one per seed)
...\pcd_summary_n150_k10_d128_kp32_agg.csv    # mean, std, min, max for the metrics
```

### 5.2 Multi‑config sweep

Just pass lists, e.g. `-KList @(10,12,14,16)` and/or `-DList @(128,256)` and `-KprojList @(32,64)`. The script loops configs and repeats.

> Tip: Keep each run in a distinct output folder (`...\run2_k10_d128_kp32`, `...\run_k_sweep`, …) so nothing is overwritten.

---

## 6) SHA256‑Prune (Lite)

A tiny **SAT/Z3** toy that lets you dial:
- **rounds** to model a truncated SHA‑256 pipeline,
- a small **prefix** condition (bits of the digest),
- a limited number of allowed **deviations** inside a chosen bit‑range,
- and optionally fix a number of message‑schedule words (**Wᵢ**) so the solver’s space collapses.

It writes a compact JSON with `status ∈ {sat, unsat, timeout}`, `solve_time_sec`, a few **z3_stats**, and (if sat) a `model_preview` with the bound `W` words.

### 6.1 Micro sweep (PowerShell)

```powershell
pwsh -File .\SHA256_lite_sweep.ps1 `
  -Root "." `
  -PythonExe "python" `
  -OutDir ".\bench\sha_sweep" `
  -TimeoutSec 30
```

### 6.2 Manual run

```powershell
python .\sha256_prune_lite.py `
  --rounds 12 --prefix-bits 4 `
  --deviations 1 --dev-lo 0 --dev-hi 255 `
  --fix-w-words 10 `
  --timeout-sec 60 --seed 1 `
  --out .\bench\sha_sweep\r12_p4_dev1_fix10.json
```

### 6.3 Aggregate SHA results

```powershell
python .\sha_aggregate.py ".\bench\sha_sweep\*.json" ".\bench\sha_sweep\sha_summary.csv"
```

CSV columns (typical):
```
file,rounds,prefix_bits,deviations,fix_w_words,dev_lo,dev_hi,status,solve_time_sec
```

> **Lite vs. full:** the *lite* model keeps the SAT instance tiny and fast (a few rounds, partial constraints). Your earlier **full** `sha256_prune.py` is heavier and only for long runs—use *lite* for demos and param studies.

---

## 7) What to plot later

For GraphBench/PCD:
- **x:** `k / sqrt(n)` (hardness)
- **y:** `AUC_ROC` (or `AUC_PR` / `ACC_tau`), with error bars from the `_agg.csv`

For SHA Lite:
- **x:** rounds (or prefix_bits / deviations)
- **y:** `solve_time_sec` (and share of `sat/unsat/timeout`)

---

## 8) Repro tips

- Always pin the **seed** lists for repeatability.
- Keep separate output folders per run (`run1_…`, `run2_…`) and archive the resulting CSVs.
- When running huge sweeps, prefer **PowerShell 7** and avoid background jobs to keep logs simple.
- If you need *elapsed time* in GraphBench JSONL, add it around the call site (easy to instrument).

---

## 9) Minimal cheat sheet

```powershell
# Single GraphBench
python .\graphbench.py --n 150 --p 0.5 --k_clique 12 --d 128 --k_proj 32 `
  --n_train_yes 250 --n_train_no 250 --n_val_yes 125 --n_val_no 125 `
  --n_test_yes 250 --n_test_no 250 --seed 1 --safety 0.02 `
  --out .\bench\pcd_sweep\demo.jsonl

# PCD sweep (50 repeats, one config)
pwsh -File .\PCD_Sweep.ps1 -Root . -OutDir .\bench\pcd_sweep\run_demo `
  -PythonExe python -N 150 -P 0.5 -KList @(12) -Repeats 50 -DList @(128) -KprojList @(32) `
  -TrainYes 250 -TrainNo 250 -ValYes 125 -ValNo 125 -TestYes 250 -TestNo 250 -Safety 0.02 -TimeoutSec 0

# SHA256-Prune(Lite)
python .\sha256_prune_lite.py --rounds 12 --prefix-bits 4 --deviations 1 --dev-lo 0 --dev-hi 255 `
  --fix-w-words 10 --timeout-sec 60 --seed 1 --out .\bench\sha_sweep\demo_sha.json
```
