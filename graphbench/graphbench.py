#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GraphBench v0.1 — ART-style projector benchmark for graph problems (Planted-Clique)

Core idea (from ART sketch):
- Encode graph x -> phi(x) ∈ R^d (unit-norm).
- Build witness lift phi(x, w) using certificate w (e.g., clique nodes).
- Approximate witness-subspace W_L by V_k from training witnesses; projector P_k = B B^T.
- Statistic q_k(x) = || P_k phi(x) ||^2; calibrate threshold τ_k on validation.
This is typical-case calibration and makes no worst-case claim. (See ART paper.)

Usage (examples at bottom or run `python graphbench.py -h`).
"""

import argparse, json, math, os, sys, random
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict
import numpy as np

# -------------------------
# Utils
# -------------------------

def set_seed(seed: int):
    random.seed(seed)
    np.random.seed(seed % (2**32 - 1))

def normalize(v: np.ndarray, eps: float = 1e-12) -> np.ndarray:
    n = np.linalg.norm(v)
    return v / max(n, eps)

def eig_topd_symmetric(A: np.ndarray, d: int) -> Tuple[np.ndarray, np.ndarray]:
    """Return top-d eigenvalues (desc) and eigenvectors for symmetric A.
    eigh returns ascending eigenvalues; we slice [-d:] and reverse."""
    evals, evecs = np.linalg.eigh(A)
    if d > A.shape[0]:
        d = A.shape[0]
    idx = np.argsort(evals)[-d:][::-1]
    return evals[idx], evecs[:, idx]

def sym_normalized_adj(A: np.ndarray) -> np.ndarray:
    """D^{-1/2} A D^{-1/2} (with eps for isolated nodes)."""
    deg = A.sum(axis=1)
    Dinv2 = np.diag(1.0 / np.sqrt(np.maximum(deg, 1e-12)))
    return Dinv2 @ A @ Dinv2

def auc_roc(scores: np.ndarray, labels: np.ndarray) -> float:
    """Simple ROC AUC (no sklearn)."""
    order = np.argsort(scores)
    labels_sorted = labels[order]
    n_pos = labels.sum()
    n_neg = len(labels) - n_pos
    if n_pos == 0 or n_neg == 0:
        return float('nan')
    rank_sum = 0.0
    for i, y in enumerate(labels_sorted, start=1):
        if y == 1:
            rank_sum += i
    # Mann–Whitney U
    U = rank_sum - n_pos*(n_pos+1)/2.0
    return U / (n_pos * n_neg)

def auc_pr(scores: np.ndarray, labels: np.ndarray) -> float:
    """Approximate PR-AUC via threshold sweep."""
    order = np.argsort(scores)[::-1]
    tp = fp = 0
    fn = int(labels.sum())
    last_prec = 1.0
    last_rec = 0.0
    area = 0.0
    for i in order:
        if labels[i] == 1:
            tp += 1
            fn -= 1
        else:
            fp += 1
        prec = tp / max(tp+fp, 1)
        rec  = tp / max(tp+fn, 1)
        area += (rec - last_rec) * ((prec + last_prec) / 2.0)
        last_prec, last_rec = prec, rec
    return area

# -------------------------
# Synthetic graph generators
# -------------------------

def er_graph(n: int, p: float, rng: np.random.Generator) -> np.ndarray:
    """Erdős–Rényi G(n,p), undirected, no self-loops."""
    M = rng.random((n, n)) < p
    A = np.triu(M, 1)
    A = A + A.T
    return A.astype(float)

def planted_clique_graph(n: int, p: float, k: int, rng: np.random.Generator) -> Tuple[np.ndarray, List[int]]:
    """ER(n,p) + planted k-clique; returns adjacency and clique node list."""
    A = er_graph(n, p, rng)
    clique = rng.choice(n, size=k, replace=False).tolist()
    for i in range(k):
        for j in range(i+1, k):
            A[clique[i], clique[j]] = 1.0
            A[clique[j], clique[i]] = 1.0
    return A, clique

# -------------------------
# Feature map φ(x) and lift φ(x, w)
# -------------------------

def phi_graph(A: np.ndarray, d: int) -> Tuple[np.ndarray, np.ndarray]:
    """
    Graph embedding φ(x): take top-d eigenvalues of normalized adjacency (unit-norm).
    Also return U_d (n×d) to allow witness-lift.
    """
    Ahat = sym_normalized_adj(A)
    evals, U = eig_topd_symmetric(Ahat, d)
    phi = normalize(evals.astype(float))
    return phi, U

def phi_lift(A: np.ndarray, U_d: np.ndarray, witness_nodes: List[int]) -> np.ndarray:
    """
    Witness lift φ(x, w): sum rows of U_d over witness nodes, unit-normalize.
    Lives in R^d (same space as φ(x)), so witness subspace WL ⊆ R^d.
    """
    S = U_d[witness_nodes, :].sum(axis=0)
    return normalize(S.astype(float))

# -------------------------
# Projector from witness vectors
# -------------------------

def projector_from_witnesses(W: np.ndarray, k_proj: int) -> np.ndarray:
    """
    W: matrix of size (#yes_train × d), rows are witness vectors φ(x,w).
    Build rank-k projector P_k = B B^T, where B are top-k left singular vectors of W.
    """
    # SVD on W (rows are samples). Compute on covariance: C = W^T W
    C = W.T @ W
    evals, evecs = np.linalg.eigh(C)  # symmetric
    idx = np.argsort(evals)[::-1]
    evecs = evecs[:, idx]
    k = min(k_proj, evecs.shape[1])
    B = evecs[:, :k]    # d×k orthonormal (for C SPD)
    P = B @ B.T         # d×d projector
    return P

def q_stat(P: np.ndarray, phi_x: np.ndarray) -> float:
    """q_k(x) = || P_k phi(x) ||^2."""
    y = P @ phi_x
    return float(np.dot(y, y))

# -------------------------
# Dataset builders
# -------------------------

@dataclass
class Instance:
    A: np.ndarray
    label: int
    witness: Optional[List[int]]

def make_dataset_planted_clique(n: int, p: float, k_clique: int,
                                n_yes: int, n_no: int, seed: int) -> List[Instance]:
    rng = np.random.default_rng(seed)
    data: List[Instance] = []
    for _ in range(n_yes):
        A, w = planted_clique_graph(n, p, k_clique, rng)
        data.append(Instance(A=A, label=1, witness=w))
    for _ in range(n_no):
        A = er_graph(n, p, rng)
        data.append(Instance(A=A, label=0, witness=None))
    rng.shuffle(data)
    return data

# -------------------------
# Calibration of τ_k
# -------------------------

def calibrate_tau(q_yes: List[float], q_no: List[float], safety: float = 0.0) -> float:
    """
    Conservative mid-quantile threshold with optional inward safety margin.
    """
    if len(q_yes) == 0 or len(q_no) == 0:
        return 0.5
    y_med = float(np.median(q_yes))
    n_med = float(np.median(q_no))
    tau = 0.5 * (y_med + n_med)
    # safety margin: pull inward away from extremes
    return max(0.0 + safety, min(1.0 - safety, tau))

# -------------------------
# Training / Evaluation
# -------------------------

def train_projector_planted_clique(train_yes: List[Instance], d: int, k_proj: int) -> Dict:
    """Collect witness-lift vectors across yes-instances, build projector."""
    W = []
    for inst in train_yes:
        phi_x, U_d = phi_graph(inst.A, d)
        v = phi_lift(inst.A, U_d, inst.witness or [])
        W.append(v)
    W = np.vstack(W) if W else np.zeros((0, d))
    if W.shape[0] == 0:
        raise RuntimeError("No witness vectors; need at least one positive training instance.")
    Pk = projector_from_witnesses(W, k_proj)
    return {"Pk": Pk, "d": d, "k_proj": k_proj}

def eval_split(split: List[Instance], Pk: np.ndarray, d: int) -> Tuple[np.ndarray, np.ndarray]:
    scores, labels = [], []
    for inst in split:
        phi_x, _ = phi_graph(inst.A, d)
        s = q_stat(Pk, phi_x)
        scores.append(s)
        labels.append(inst.label)
    return np.array(scores), np.array(labels)

# -------------------------
# Main CLI
# -------------------------

def main():
    ap = argparse.ArgumentParser(description="GraphBench v0.1 — ART-style projector benchmark (Planted-Clique).")
    ap.add_argument("--problem", type=str, default="planted_clique", choices=["planted_clique"],
                    help="Which graph problem to simulate.")
    ap.add_argument("--n", type=int, default=150, help="Number of nodes.")
    ap.add_argument("--p", type=float, default=0.5, help="ER edge probability.")
    ap.add_argument("--k_clique", type=int, default=10, help="Clique size for positives.")
    ap.add_argument("--d", type=int, default=32, help="Embedding dimension for φ(x) (top-d eigenvalues/vectors).")
    ap.add_argument("--k_proj", type=int, default=8, help="Projector rank k.")
    ap.add_argument("--n_train_yes", type=int, default=50)
    ap.add_argument("--n_train_no",  type=int, default=50)
    ap.add_argument("--n_val_yes",   type=int, default=50)
    ap.add_argument("--n_val_no",    type=int, default=50)
    ap.add_argument("--n_test_yes",  type=int, default=200)
    ap.add_argument("--n_test_no",   type=int, default=200)
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--safety", type=float, default=0.02, help="Safety margin for τ (pull inward).")
    ap.add_argument("--out", type=str, default=None, help="If set, write JSON summary to this path.")
    args = ap.parse_args()

    set_seed(args.seed)

    # Build datasets
    ds_train = make_dataset_planted_clique(args.n, args.p, args.k_clique, args.n_train_yes, args.n_train_no, args.seed+1)
    ds_val   = make_dataset_planted_clique(args.n, args.p, args.k_clique, args.n_val_yes,   args.n_val_no,   args.seed+2)
    ds_test  = make_dataset_planted_clique(args.n, args.p, args.k_clique, args.n_test_yes,  args.n_test_no,  args.seed+3)

    train_yes = [x for x in ds_train if x.label == 1]

    model = train_projector_planted_clique(train_yes, d=args.d, k_proj=args.k_proj)
    Pk = model["Pk"]

    # Validation to pick τ
    val_scores, val_labels = eval_split(ds_val, Pk, d=args.d)
    q_yes = val_scores[val_labels == 1].tolist()
    q_no  = val_scores[val_labels == 0].tolist()
    tau = calibrate_tau(q_yes, q_no, safety=args.safety)

    # Test
    test_scores, test_labels = eval_split(ds_test, Pk, d=args.d)
    roc = auc_roc(test_scores, test_labels)
    pr  = auc_pr(test_scores, test_labels)
    yhat = (test_scores >= tau).astype(int)
    acc = float((yhat == test_labels).mean())

    summary = {
        "problem": args.problem,
        "n": args.n,
        "p": args.p,
        "k_clique": args.k_clique,
        "d": args.d,
        "k_proj": args.k_proj,
        "sizes": {
            "train_yes": args.n_train_yes, "train_no": args.n_train_no,
            "val_yes": args.n_val_yes,     "val_no": args.n_val_no,
            "test_yes": args.n_test_yes,   "test_no": args.n_test_no
        },
        "calibration": {
            "tau": tau,
            "q_yes_med": float(np.median(q_yes)) if q_yes else None,
            "q_no_med":  float(np.median(q_no))  if q_no  else None,
            "safety": args.safety
        },
        "test_metrics": {
            "AUC_ROC": roc,
            "AUC_PR": pr,
            "ACC(tau)": acc
        }
    }

    print("\n=== GraphBench v0.1 results ===")
    print(json.dumps(summary, indent=2))

    if args.out:
        os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
        with open(args.out, "w", encoding="utf-8") as f:
            json.dump(summary, f, indent=2)
        print(f"\nSaved: {args.out}")

if __name__ == "__main__":
    main()
