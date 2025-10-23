"""
GMF (Guided Multiplication Factorization) — CLI v3 (with discovery)
-------------------------------------------------------------------
What's new:
- --discover: when both factors are "unknown", scan a bounded k-range (odd k) as descriptors
             and find the smallest linear factor via guided-multiplication check.
- --kmax:    upper bound for discovery scan (default 10_000; toy-safe).
- --full:    recursively factor by repeatedly discovering smallest factors until kmax exhausted
             or remaining cofactor looks prime (simple primality check).

Still purely number-theoretic and NON-crypto; intended as a structural demo.
"""

from math import gcd
import random, time, argparse, sys, csv
from typing import Optional, List, Tuple

TOY_SMALL_FACTORS = [3,5,7,11,13,17,19,23]

class Descriptor:
    def __init__(self, k:int):
        self.k = k
    def __repr__(self):
        return f"π[k={self.k}]"

def Mem_R(N:int)->bool:
    if N <= 3:
        return False
    for p in TOY_SMALL_FACTORS:
        if N % p == 0 and N != p:
            return True
    return False

def Describe(N:int):
    return [Descriptor(k) for k in TOY_SMALL_FACTORS]

def LocalStep(pi:Descriptor, state)->int:
    return pi.k

def IsAdmissible(pi:Descriptor, g:int, t:int)->bool:
    return (g == pi.k) and (g > 1)

def StepBudget(pi:Descriptor, N:int)->int:
    return max(8, len(str(N)) // 2)

def NontrivialGCD(x:int, N:int)->int:
    d = gcd(x, N)
    return d if (d != 1 and d != N) else 1

def GMF_Safe(N:int):
    if N <= 1 or not Mem_R(N):
        return 1, ["N is trivial or not in toy ℛ"]
    logs = []
    for pi in Describe(N):
        u, T = 1, StepBudget(pi, N)
        log = [f"start: N_bits≈{N.bit_length()}, {pi}, T={T}"]
        for t in range(T):
            g = LocalStep(pi, (u, None, t, N))
            if not IsAdmissible(pi, g, t):
                log.append(f"t={t}: inadmissible g={g}")
                break
            u = (u * g) % N
            d = NontrivialGCD(u, N)
            log.append(f"t={t}: u={u}, gcd={d}")
            if d != 1:
                log.append(f"SUCCESS factor={d}")
                return d, log
        logs.extend(log)
    return 1, logs

def GMF_Fast(N:int, retries:int=5)->int:
    if not Mem_R(N):
        return 1
    for _ in range(retries):
        for pi in Describe(N):
            u, T = 1, StepBudget(pi, N)
            for _ in range(T):
                u = (u * pi.k) % N
                d = NontrivialGCD(u, N)
                if d != 1:
                    return d
    return 1

def random_odd_with_bits(bits:int, rng:Optional[random.Random]=None)->int:
    if rng is None:
        rng = random
    if bits < 2:
        raise ValueError("bits must be >= 2")
    x = rng.getrandbits(bits) | (1 << (bits-1)) | 1
    return x

def build_demo_N_bits(small_factor:int, bits:int, rng:Optional[random.Random]=None):
    if small_factor % 2 == 0:
        raise ValueError("small_factor must be odd for this toy.")
    M = random_odd_with_bits(bits, rng=rng)
    if M % small_factor == 0:
        M += 2
    N = small_factor * M
    return N, M

def _run_steps_only_with_k(N:int, k:int):
    u = 1
    for _ in range(8):
        u = (u * k) % N
        d = NontrivialGCD(u, N)
        if d != 1:
            return d, 1
    return 1, 8

def discover_smallest_linear_factor(N:int, kmax:int=10_000)->int:
    if N % 2 == 0:
        return 2
    for k in range(3, kmax+1, 2):
        d, _ = _run_steps_only_with_k(N, k)
        if d != 1:
            return d
    return 1

def is_probable_prime(n:int, rounds:int=8)->bool:
    if n < 2:
        return False
    small_base = [2,3,5,7,11,13,17,19,23,29]
    if n in small_base:
        return True
    for p in small_base:
        if n % p == 0:
            return False
    d = n-1; s = 0
    while d % 2 == 0:
        d //= 2; s += 1
    import random as _r
    for _ in range(rounds):
        a = _r.randrange(2, n-2)
        x = pow(a, d, n)
        if x == 1 or x == n-1:
            continue
        for __ in range(s-1):
            x = pow(x, 2, n)
            if x == n-1:
                break
        else:
            return False
    return True

def full_factorization_toy(N:int, kmax:int=10_000)->List[int]:
    factors = []
    stack = [N]
    while stack:
        m = stack.pop()
        if m <= 1:
            continue
        if is_probable_prime(m):
            factors.append(m)
            continue
        d = discover_smallest_linear_factor(m, kmax=kmax)
        if d == 1:
            factors.append(m)
        else:
            factors.append(d)
            stack.append(m // d)
    factors.sort()
    return factors

def benchmark_bitlengths(bit_lengths=(256,512,1024,2048), repeats=1, rng_seed:Optional[int]=None, include_values=False, use_hex=False):
    rows = []
    rng = random.Random(rng_seed) if rng_seed is not None else random
    for bits in bit_lengths:
        for k in TOY_SMALL_FACTORS:
            for r in range(repeats):
                N, M = build_demo_N_bits(k, bits, rng=rng)
                t0 = time.perf_counter()
                found, _steps = _run_steps_only_with_k(N, k)
                dt = (time.perf_counter() - t0) * 1000.0
                base = {
                    "target_bits(M)": bits,
                    "N_bits": N.bit_length(),
                    "small_factor": k,
                    "found": found,
                    "time_ms": round(dt, 4),
                    "repeat": r
                }
                if include_values:
                    base["M"] = (hex(M) if use_hex else str(M))
                    base["N"] = (hex(N) if use_hex else str(N))
                rows.append(base)
    return rows

def parse_args(argv=None):
    p = argparse.ArgumentParser(description="GMF toy demo (no crypto): factor a given N or build N from bit-length.")
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--N", type=str, help="Concrete integer N (decimal string) to factor.")
    g.add_argument("--bits", type=int, help="Build N = small_factor * M, where M has exactly <bits> bits (odd).")
    p.add_argument("--small-factor", type=int, default=13, help="Small odd factor when using --bits (default: 13).")
    p.add_argument("--mode", choices=["safe","fast"], default="safe", help="safe: logs & strict checks; fast: heuristic.")
    p.add_argument("--discover", action="store_true", help="When both factors are unknown: scan odd k up to --kmax to find smallest linear factor.")
    p.add_argument("--kmax", type=int, default=10_000, help="Upper bound for --discover scan (toy).")
    p.add_argument("--full", action="store_true", help="Recursively factor by discovery until bounded (toy).")
    p.add_argument("--benchmark", type=str, default="", help="Comma-separated list of bit-lengths to benchmark (e.g. '256,512,1024').")
    p.add_argument("--repeats", type=int, default=1, help="Repeats per bit-length in benchmark (default: 1).")
    p.add_argument("--csv", type=str, default="", help="Optional CSV output path for benchmark results.")
    p.add_argument("--truncate-log", type=int, default=6, help="Show only the first k log lines (safe mode).")
    p.add_argument("--seed", type=int, default=None, help="Seed for reproducible --bits generation.")
    p.add_argument("--print-M", action="store_true", help="Print random M when using --bits.")
    p.add_argument("--print-N", action="store_true", help="Also print N when using --bits.")
    p.add_argument("--hex", action="store_true", help="Print big integers in hexadecimal.")
    p.add_argument("--save-N", type=str, default="", help="Save the generated N (decimal) to file.")
    p.add_argument("--print-cases", action="store_true", help="Benchmark: print each case with M and N values.")
    return p.parse_args(argv)

def _fmt_int(x:int, use_hex:bool)->str:
    return hex(x) if use_hex else str(x)

def main(argv=None):
    args = parse_args(argv)
    rng = random.Random(args.seed) if args.seed is not None else None

    if args.benchmark:
        bit_lengths = [int(x.strip()) for x in args.benchmark.split(",") if x.strip()]
        rows = benchmark_bitlengths(bit_lengths, repeats=args.repeats, rng_seed=args.seed,
                                    include_values=args.print-cases or bool(args.csv), use_hex=args.hex)
        header = ["target_bits(M)","N_bits","small_factor","found","time_ms","repeat"]
        if args.print-cases or args.csv:
            header += ["M","N"]
        if args.csv:
            with open(args.csv, "w", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=header)
                w.writeheader()
                for r in rows:
                    w.writerow(r)
            print(f"[OK] Benchmark written to: {args.csv}")
        if args.print-cases:
            print(" | ".join(header))
            for r in rows:
                print(" | ".join(str(r.get(h,"")) for h in header))
        else:
            if not args.csv:
                print(" | ".join(header))
                for r in rows[:min(24, len(rows))]:
                    print(" | ".join(str(r.get(h,'')) for h in header))
        return 0

    if args.bits is not None:
        N, M = build_demo_N_bits(args.small_factor, args.bits, rng=rng)
        print(f"Built N with M_bits={args.bits}, small_factor={args.small_factor}, N_bits≈{N.bit_length()}")
        if args.print_M:
            print("M =", _fmt_int(M, args.hex))
        if args.print_N:
            print("N =", _fmt_int(N, args.hex))
        if args.save_N:
            with open(args.save_N, "w", encoding="utf-8") as f:
                f.write(str(N))
            print(f"[OK] N saved to {args.save_N}")
    else:
        try:
            N = int(args.N, 10)
        except ValueError:
            print("Error: --N must be a base-10 integer string", file=sys.stderr)
            return 1

    print("Factoring N =", _fmt_int(N, args.hex))

    if args.discover or args.full:
        if args.full:
            facs = full_factorization_toy(N, kmax=args.kmax)
            print(f"[FULL] factors (toy): {', '.join(_fmt_int(x, args.hex) for x in facs)}")
            return 0
        else:
            d = discover_smallest_linear_factor(N, kmax=args.kmax)
            print(f"[DISCOVER] smallest linear factor (toy) up to kmax={args.kmax}: {_fmt_int(d, args.hex)}")
            return 0

    t0 = time.perf_counter()
    if args.mode == "safe":
        d, log = GMF_Safe(N)
        dt = (time.perf_counter() - t0) * 1000.0
        print(f"mode=safe | factor={d} | time_ms={dt:.3f}")
        for line in log[:max(0, args.truncate_log)]:
            print("  ", line)
        if len(log) > args.truncate_log:
            print("  ... (log truncated)")
    else:
        d = GMF_Fast(N)
        dt = (time.perf_counter() - t0) * 1000.0
        print(f"mode=fast | factor={d} | time_ms={dt:.3f}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
