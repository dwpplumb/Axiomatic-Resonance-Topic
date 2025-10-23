# sha_aggregate.py  (robuste Version mit Logging)
import json, glob, csv, os, sys, traceback

def complexity_idx(r, p, dev, fix, a=1.0, b=0.5, c=0.7, d=0.4):
    return a*r + b*p - c*dev + d*fix

def load_json(path):
    # erlaubt sowohl „normales JSON“ als auch 1-Objekt-JSONL
    with open(path, "r", encoding="utf-8") as f:
        txt = f.read().strip()
    try:
        return json.loads(txt)
    except json.JSONDecodeError:
        # falls es doch JSONL ist, nimm erste nicht-leere Zeile
        for line in txt.splitlines():
            line=line.strip()
            if line:
                try:
                    return json.loads(line)
                except Exception:
                    pass
        raise

def main():
    if len(sys.argv) != 3:
        print("usage: python sha_aggregate.py <glob_json> <out_csv>")
        sys.exit(2)

    pattern = sys.argv[1]
    out_csv = sys.argv[2]

    paths = sorted(glob.glob(pattern))
    print(f"[info] glob: {pattern}")
    print(f"[info] matched files: {len(paths)}")
    for p in paths[:5]:
        print(f"       - {p}")
    if len(paths) == 0:
        print("[warn] no files matched — aborting (no CSV written).")
        return

    rows = []
    bad = 0
    for path in paths:
        try:
            J = load_json(path)
            r  = int(J.get("rounds", 0))
            p  = int(J.get("prefix_bits", J.get("prefix", 0)))
            dv = int(J.get("deviations", 0))
            fw = int(J.get("fix_w_words", J.get("fix", 0)))
            status = str(J.get("status", "unknown")).lower()
            t  = J.get("solve_time_sec", None)
            z3 = J.get("z3_stats") or {}
            rlim = z3.get("rlimit count", z3.get("rlimit_count"))

            prec = 1.0 if status == "unsat" else 0.0
            cidx = round(complexity_idx(r, p, dv, fw), 3)

            rows.append({
                "file": os.path.basename(path),
                "rounds": r, "prefix_bits": p, "deviations": dv, "fix_w_words": fw,
                "status": status,
                "solve_time_sec": t,
                "rlimit": rlim,
                "complexity_idx": cidx,
                "precision_proxy": prec
            })
        except Exception as e:
            bad += 1
            print(f"[warn] failed to parse {path}: {e}")
            # Debug optional:
            # traceback.print_exc()

    if not rows:
        print(f"[warn] 0 rows parsed successfully, bad={bad}. No CSV written.")
        return

    rows.sort(key=lambda x: (x["complexity_idx"], -x["precision_proxy"], (x["solve_time_sec"] or 0)))
    os.makedirs(os.path.dirname(out_csv), exist_ok=True)

    with open(out_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader(); w.writerows(rows)

    print(f"[ok] wrote {len(rows)} rows → {out_csv}  (failed: {bad})")

if __name__ == "__main__":
    main()
