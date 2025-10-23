#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SHA256-Prune Benchmark (Z3-based)
- Models a truncated SHA-256 compression with a configurable number of rounds.
- Lets you enforce a zero-prefix on register A after the last modeled round.
- Lets you introduce "deviations" by forcing selected message-schedule input bits to 1.
- Writes a JSONL or JSON file with status, timings, and basic stats.

This is a benchmarking/constraint-propagation toy — not a cryptanalytic tool.
"""

import argparse
import json
import math
import os
import random
import time
from typing import Any, Dict, List

import z3

# --- Helpers -----------------------------------------------------------------

def rotr(x: z3.BitVecRef, n: int) -> z3.BitVecRef:
    return z3.LShR(x, n) | (x << (32 - n))

def sigma0(x: z3.BitVecRef) -> z3.BitVecRef:
    # small sigma0 for message schedule
    return rotr(x, 7) ^ rotr(x, 18) ^ z3.LShR(x, 3)

def sigma1(x: z3.BitVecRef) -> z3.BitVecRef:
    # small sigma1 for message schedule
    return rotr(x, 17) ^ rotr(x, 19) ^ z3.LShR(x, 10)

def capsigma0(x: z3.BitVecRef) -> z3.BitVecRef:
    # big Sigma0 for round function
    return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22)

def capsigma1(x: z3.BitVecRef) -> z3.BitVecRef:
    # big Sigma1 for round function
    return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25)

def ch(x: z3.BitVecRef, y: z3.BitVecRef, z: z3.BitVecRef) -> z3.BitVecRef:
    return (x & y) ^ (~x & z)

def maj(x: z3.BitVecRef, y: z3.BitVecRef, z: z3.BitVecRef) -> z3.BitVecRef:
    return (x & y) ^ (x & z) ^ (y & z)

# SHA-256 K constants (first 32 entries are enough for < 32 rounds; we include 64 for generality)
K = [
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2,
]

# Initial values (IV) as per SHA-256
IV = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

def stats_to_dict(stats: "z3.StatisticsRef") -> Dict[str, Any]:
    d: Dict[str, Any] = {}
    try:
        for k in stats.keys():
            # statistics can be int or float
            try:
                d[str(k)] = int(stats.get_key_value(k))
            except Exception:
                try:
                    d[str(k)] = float(stats.get_key_value(k))
                except Exception:
                    d[str(k)] = str(stats.get_key_value(k))
    except Exception:
        # fallback: best effort string
        d = {"_repr": str(stats)}
    return d

def select_deviation_bits(n_bits: int, how_many: int, rng: random.Random) -> List[int]:
    # choose unique bit positions in [0, n_bits)
    positions = list(range(n_bits))
    rng.shuffle(positions)
    return sorted(positions[:max(0, min(how_many, n_bits))])

# --- Core model ---------------------------------------------------------------

def build_sha256_truncated(rounds: int,
                           prefix_bits: int,
                           deviations: int,
                           rng: random.Random,
                           fix_w0123: bool = True):
    """
    Returns (solver, variables, last_A) where:
      - solver has all constraints
      - variables is a dict with keys: W (list[BitVec]), A..H (list per round+1), etc.
      - last_A is the BitVecRef of A after the final modeled round
    """
    assert 1 <= rounds <= 64, "rounds must be in [1..64]"
    s = z3.Solver()

    # Message schedule W[0..63]
    W = [z3.BitVec(f"W_{i}", 32) for i in range(64)]

    # For demo stability: optionally fix W0..W3 to a concrete "padding-ish" pattern
    # (These are arbitrary demo constants, *NOT* derived from real input!)
    if fix_w0123:
        s.add(W[0] == z3.BitVecVal(0x61616180, 32))  # 'a'*1 + 0x80
        s.add(W[1] == z3.BitVecVal(0, 32))
        s.add(W[2] == z3.BitVecVal(0, 32))
        s.add(W[3] == z3.BitVecVal(0x00000008, 32))  # length=8 bits (toy)
    # W[16..63] (Z3 derives by constraints as used)

    # Introduce "deviations": force selected bits among W[0..15] to 1
    # We choose absolute bit positions across these 16 words (16*32 = 512 bits)
    dev_positions = select_deviation_bits(16*32, deviations, rng)
    for bitpos in dev_positions:
        word_idx = bitpos // 32
        bit_idx  = bitpos % 32
        s.add(z3.Extract(bit_idx, bit_idx, W[word_idx]) == z3.BitVecVal(1, 1))

    # Compute W[16..] as in spec (constraints)
    for t in range(16, 64):
        s0 = sigma0(W[t-15])
        s1 = sigma1(W[t-2])
        Wt = (W[t-16] + s0 + W[t-7] + s1) & z3.BitVecVal(0xffffffff, 32)
        s.add(W[t] == Wt)

    # Working variables a..h
    A = [z3.BitVec(f"A_{i}", 32) for i in range(rounds+1)]
    B = [z3.BitVec(f"B_{i}", 32) for i in range(rounds+1)]
    C = [z3.BitVec(f"C_{i}", 32) for i in range(rounds+1)]
    D = [z3.BitVec(f"D_{i}", 32) for i in range(rounds+1)]
    E = [z3.BitVec(f"E_{i}", 32) for i in range(rounds+1)]
    F = [z3.BitVec(f"F_{i}", 32) for i in range(rounds+1)]
    G = [z3.BitVec(f"G_{i}", 32) for i in range(rounds+1)]
    H = [z3.BitVec(f"H_{i}", 32) for i in range(rounds+1)]

    # Initialize from IV
    s.add(A[0] == z3.BitVecVal(IV[0], 32))
    s.add(B[0] == z3.BitVecVal(IV[1], 32))
    s.add(C[0] == z3.BitVecVal(IV[2], 32))
    s.add(D[0] == z3.BitVecVal(IV[3], 32))
    s.add(E[0] == z3.BitVecVal(IV[4], 32))
    s.add(F[0] == z3.BitVecVal(IV[5], 32))
    s.add(G[0] == z3.BitVecVal(IV[6], 32))
    s.add(H[0] == z3.BitVecVal(IV[7], 32))

    # Round updates
    for t in range(rounds):
        T1 = (H[t] + capsigma1(E[t]) + ch(E[t], F[t], G[t]) + z3.BitVecVal(K[t], 32) + W[t]) & z3.BitVecVal(0xffffffff, 32)
        T2 = (capsigma0(A[t]) + maj(A[t], B[t], C[t])) & z3.BitVecVal(0xffffffff, 32)

        s.add(H[t+1] == G[t])
        s.add(G[t+1] == F[t])
        s.add(F[t+1] == E[t])
        s.add(E[t+1] == (D[t] + T1) & z3.BitVecVal(0xffffffff, 32))
        s.add(D[t+1] == C[t])
        s.add(C[t+1] == B[t])
        s.add(B[t+1] == A[t])
        s.add(A[t+1] == (T1 + T2) & z3.BitVecVal(0xffffffff, 32))

    # After last round, enforce zero-prefix on A if requested
    if prefix_bits > 0:
        assert 0 <= prefix_bits <= 32, "prefix_bits must be in [0..32]"
        # "Top prefix_bits == 0"  =>  (A_last >> (32 - prefix_bits)) == 0
        # (If prefix_bits==32, A_last must be exactly 0.)
        shift = 32 - prefix_bits
        if shift == 0:
            s.add(A[rounds] == z3.BitVecVal(0, 32))
        else:
            s.add(z3.LShR(A[rounds], shift) == z3.BitVecVal(0, 32))

    variables = {
        "W": W, "A": A, "B": B, "C": C, "D": D, "E": E, "F": F, "G": G, "H": H,
        "deviation_positions": dev_positions,
    }
    return s, variables, A[rounds]

def run_instance(rounds: int, prefix_bits: int, deviations: int, seed: int, out_path: str, no_fix_w0123: bool) -> Dict[str, Any]:
    rng = random.Random(seed)
    solver, vars_dict, A_last = build_sha256_truncated(
        rounds=rounds,
        prefix_bits=prefix_bits,
        deviations=deviations,
        rng=rng,
        fix_w0123=(not no_fix_w0123),
    )

    t0 = time.time()
    res = solver.check()
    t1 = time.time()

    stats = solver.statistics()
    stats_d = stats_to_dict(stats)

    out: Dict[str, Any] = {
        "rounds": rounds,
        "prefix_bits": prefix_bits,
        "deviations": deviations,
        "seed": seed,
        "status": str(res),
        "solve_time_sec": round(t1 - t0, 6),
        "z3_stats": stats_d,
        "deviation_positions": vars_dict["deviation_positions"],
    }

    if res == z3.sat:
        model = solver.model()
        # include a small preview (last A, and first four W words) to help sanity-check
        a_val = model[ A_last ]
        try:
            a_int = model.evaluate(A_last).as_long()
        except Exception:
            a_int = None
        preview = {"A_last_hex": (f"{a_int:08x}" if isinstance(a_int, int) else None)}
        for i in range(4):
            try:
                w_i = model.evaluate(vars_dict["W"][i]).as_long()
                preview[f"W{i}"] = f"{w_i:08x}"
            except Exception:
                preview[f"W{i}"] = None
        out["model_preview"] = preview

    # ensure directory
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
    return out

# --- CLI ---------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description="SHA256-Prune: truncated SHA-256 + constraints (Z3)")
    ap.add_argument("--rounds", type=int, required=True, help="Number of compression rounds to model (1..64)")
    ap.add_argument("--prefix-bits", type=int, default=0, help="Zero-prefix on A after last round (0..32)")
    ap.add_argument("--deviations", type=int, default=0, help="Force this many input bits among W[0..15]*32 to 1")
    ap.add_argument("--seed", type=int, default=1, help="PRNG seed for picking deviation bit positions")
    ap.add_argument("--out", type=str, required=True, help="Output JSON path")
    ap.add_argument("--no-fix-w0123", action="store_true",
                    help="Do not fix W0..W3 demo constants (default: fix them for stability)")

    args = ap.parse_args()

    out = run_instance(
        rounds=args.rounds,
        prefix_bits=args.prefix_bits,
        deviations=args.deviations,
        seed=args.seed,
        out_path=args.out,
        no_fix_w0123=args.no_fix_w0123,
    )

    print("\n=== SHA256-Prune result ===")
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
