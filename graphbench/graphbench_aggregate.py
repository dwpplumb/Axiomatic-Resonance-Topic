#!/usr/bin/env python3
import argparse, glob, json, csv, os, re

def row_from_jsonl(path):
    # Jede Datei enthält genau 1 JSON-Objekt (von graphbench.py gedruckt)
    with open(path, "r", encoding="utf-8") as f:
        obj = json.loads(f.read())
    # Dateiname parsen (n, k_clique, ratio ~ r)
    base = os.path.basename(path)
    m = re.search(r"pc_n(\d+)_k(\d+)_r([0-9.]+)_seed(\d+)\.jsonl", base.replace(",",".")) or \
        re.search(r"pc_n(\d+)_k(\d+).*seed(\d+)", base)
    n = int(m.group(1)) if m else obj.get("n")
    k = int(m.group(2)) if m and len(m.groups())>=2 else obj.get("k_clique")
    seed = int(m.group(4) if m and len(m.groups())>=4 else (m.group(3) if m else obj.get("seed",0)))
    r = obj.get("n",1)/max(obj.get("k_clique",1),1) if "n" in obj and "k_clique" in obj else None

    calib = obj.get("calibration", {})
    test  = obj.get("test_metrics", {})

    return {
        "file": base,
        "seed": seed,
        "n": obj.get("n", n),
        "k_clique": obj.get("k_clique", k),
        "r_est": r,
        "D": obj.get("d"),
        "K_proj": obj.get("k_proj"),
        "tau": calib.get("tau"),
        "QYes_Med": calib.get("q_yes_med"),
        "QNo_Med": calib.get("q_no_med"),
        "safety": calib.get("safety"),
        "AUC_ROC": test.get("AUC_ROC"),
        "AUC_PR":  test.get("AUC_PR"),
        "ACC_tau": test.get("ACC(tau)")
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("glob_in", help="z.B. .\\bench\\sweep\\*.jsonl")
    ap.add_argument("csv_out", help="z.B. .\\bench\\sweep\\complexity_sweep_results_full.csv")
    args = ap.parse_args()

    paths = sorted(glob.glob(args.glob_in))
    if not paths:
        print("[warn] keine Dateien gematcht")
        return

    rows = [row_from_jsonl(p) for p in paths]
    cols = ["file","seed","n","k_clique","r_est","D","K_proj","tau","QYes_Med","QNo_Med","safety","AUC_ROC","AUC_PR","ACC_tau"]

    with open(args.csv_out, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows: w.writerow(r)

    print(f"[ok] wrote {len(rows)} rows → {args.csv_out}")

if __name__ == "__main__":
    main()
