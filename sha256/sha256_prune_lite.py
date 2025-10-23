
# sha256_prune_lite.py
# Lightweight SHA-256 constraint benchmark with Z3
#
# Goals:
# - Keep models small & fast by default
# - Provide flags to scale complexity gradually
#
# Defaults are intentionally mild: 4 rounds, 8-bit prefix, 1 deviation bit,
# deviations restricted to the first 64 input bits, many message words fixed,
# and a 30s solver timeout.
#
# Usage (PowerShell):
#   python .\sha256_prune_lite.py --out .\bench\sha_sweep\demo.json
#
# Scale up:
#   python sha256_prune_lite.py --rounds 8 --prefix-bits 12 --deviations 2 --timeout-sec 120 --out run.json
#
import argparse, json, random, time
from typing import Dict, Any
import z3

# --- SHA-256 helpers (bit-vector ops) ---
def R(x, n):  return z3.LShR(x, n)
def S(x, n):  return z3.RotateRight(x, n)
def Ch(x,y,z): return (x & y) ^ (~x & z)
def Maj(x,y,z): return (x & y) ^ (x & z) ^ (y & z)
def Sig0(x):  return S(x,2) ^ S(x,13) ^ S(x,22)
def Sig1(x):  return S(x,6) ^ S(x,11) ^ S(x,25)
def sig0(x):  return S(x,7) ^ S(x,18) ^ R(x,3)
def sig1(x):  return S(x,17) ^ S(x,19) ^ R(x,10)

# Round constants:
K = [
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
]

IV = [  # Initial hash values (H0..H7)
    0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
    0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19
]

def z3_stats_to_dict(stats: z3.Statistics) -> Dict[str, Any]:
    d = {}
    try:
        for k in stats.keys():
            try:
                d[k] = stats.get_key_value(k)
            except Exception:
                # Some stats keys are tuples or not directly serializable
                v = stats[k]
                try:
                    d[k] = int(v)
                except Exception:
                    try:
                        d[k] = float(v)
                    except Exception:
                        d[k] = str(v)
    except Exception:
        pass
    return d

def build_model(args) -> Dict[str, Any]:
    s = z3.Solver()
    s.set("timeout", int(args.timeout_sec*1000))

    # Message schedule W[0..63]
    W = [None]*64
    # Strategy: fix many words to constants for speed (partial evaluation),
    # leave a small window symbolic where we also place deviation bits.
    # By default, fix_w_words=14 → W0..W13 fixed, W14..W15 symbolic.
    fix_w_words = args.fix_w_words
    fix_seed = random.Random(args.seed)

    # deterministic constants for fixed words
    def fixed_word(i):
        # simple LCG-ish pattern for stable but varied constants
        return z3.BitVecVal((0x9E3779B1 * (i+1) + 0x85EBCA77) & 0xffffffff, 32)

    for i in range(16):
        if i < fix_w_words:
            W[i] = fixed_word(i)
        else:
            W[i] = z3.BitVec(f"W{i}", 32)

    # Extend schedule with partial evaluation when possible
    for t in range(16, max(16, args.rounds)):
        x = W[t-15]; y = W[t-2]
        term = (sig1(y) + W[t-7] + sig0(x) + W[t-16]) & z3.BitVecVal(0xffffffff,32)
        # If all inputs are concrete, z3 simplifies heavily; else keep symbolic
        W[t] = z3.simplify(term)

    # Place deviations within a bit-range over the first 2 symbolic words by default
    # Use bit-index [lo, hi] inclusive
    dev_rng_lo = args.dev_lo
    dev_rng_hi = args.dev_hi

    # Collect candidate bit positions from available symbolic words
    sym_words = [i for i in range(16) if i >= fix_w_words] or [15]
    cand_bits = []
    for i in sym_words[:2]:  # at most first two symbolic words for speed
        base = i*32
        for b in range(32):
            gbit = base + b
            if dev_rng_lo <= gbit <= dev_rng_hi:
                cand_bits.append((i, b))

    rng = random.Random(args.seed)
    rng.shuffle(cand_bits)
    picked = cand_bits[:max(0, args.deviations)]
    for (wi, bi) in picked:
        # Force that particular input bit to 1
        mask = (1 << bi)
        s.add( (W[wi] & mask) == mask )

    # Initial state
    a,b,c,d,e,f,g,h = [z3.BitVecVal(x,32) for x in IV]

    # Rounds (small number by default)
    for t in range(args.rounds):
        T1 = (h + Sig1(e) + Ch(e,f,g) + z3.BitVecVal(K[t],32) + W[t]) & z3.BitVecVal(0xffffffff,32)
        T2 = (Sig0(a) + Maj(a,b,c)) & z3.BitVecVal(0xffffffff,32)
        h = g
        g = f
        f = e
        e = (d + T1) & z3.BitVecVal(0xffffffff,32)
        d = c
        c = b
        b = a
        a = (T1 + T2) & z3.BitVecVal(0xffffffff,32)

    # Prefix constraint on final 'a'
    if args.prefix_bits > 0:
        # Enforce top 'prefix_bits' of 'a' to be zero
        shift = 32 - args.prefix_bits
        s.add(z3.LShR(a, shift) == 0)

    t0 = time.perf_counter()
    res = s.check()
    t1 = time.perf_counter()

    out = {
        "rounds": args.rounds,
        "prefix_bits": args.prefix_bits,
        "deviations": args.deviations,
        "seed": args.seed,
        "status": str(res),
        "solve_time_sec": round(t1 - t0, 6),
        "z3_params": {"timeout_ms": int(args.timeout_sec*1000)},
        "z3_stats": z3_stats_to_dict(s.statistics()),
        "deviation_positions": [wi*32+bi for (wi,bi) in picked],
        "fix_w_words": fix_w_words,
        "dev_bit_range": [dev_rng_lo, dev_rng_hi]
    }

    # Tiny model preview if SAT
    if res == z3.sat:
        m = s.model()
        preview = {}
        for i in range(16):
            if z3.is_const(W[i]) and hasattr(W[i], 'decl') and W[i].decl().kind() == z3.Z3_OP_UNINTERPRETED:
                val = m.eval(W[i], model_completion=True)
                preview[f"W{i}"] = int(val.as_long()) & 0xffffffff
            elif isinstance(W[i], z3.BitVecNumRef):
                preview[f"W{i}"] = int(W[i].as_long()) & 0xffffffff
        out["model_preview"] = preview

    return out

def main():
    ap = argparse.ArgumentParser(description="Lite SHA-256 pruning benchmark (Z3)")
    ap.add_argument("--rounds", type=int, default=4, help="number of SHA-256 rounds (1..64)")
    ap.add_argument("--prefix-bits", type=int, default=8, help="zero-prefix bits required on final 'a'")
    ap.add_argument("--deviations", type=int, default=1, help="number of input bits forced to 1")
    ap.add_argument("--seed", type=int, default=1, help="PRNG seed for picking deviation bits")
    ap.add_argument("--timeout-sec", type=float, default=30.0, help="Z3 timeout in seconds")
    ap.add_argument("--dev-lo", type=int, default=0, help="min global bit-index for deviations (0..511)")
    ap.add_argument("--dev-hi", type=int, default=63, help="max global bit-index for deviations (0..511)")
    ap.add_argument("--fix-w-words", type=int, default=14, help="fix W[0..fix_w_words-1] to constants")
    ap.add_argument("--out", type=str, required=True, help="output JSON file")
    args = ap.parse_args()

    out = build_model(args)

    # Emit JSON
    with open(args.out, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
    print("\n=== SHA256-Prune(Lite) result ===")
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
