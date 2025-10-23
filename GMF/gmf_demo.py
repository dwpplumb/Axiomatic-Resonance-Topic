# Guided Multiplication Factorization (toy demo)
from math import gcd

TOY_SMALL_PRIMES = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

class Descriptor:
    def __init__(self, k:int):
        self.k = k
    def __repr__(self):
        return f"π[k={self.k}]"

def Mem_R(N:int)->bool:
    if N <= 3:
        return False
    for p in TOY_SMALL_PRIMES:
        if N % p == 0 and N != p:
            return True
    return False

def Describe(N:int):
    return [Descriptor(k) for k in [3,5,7,11,13,17]]

def IsAdmissible(pi:Descriptor, g:int, t:int)->bool:
    return g == pi.k and g > 1

def LocalStep(pi:Descriptor, state)->int:
    return pi.k

def StepBudget(pi:Descriptor, N:int)->int:
    return max(8, len(str(N))*2)

def NontrivialGCD(x:int, N:int)->int:
    d = gcd(x, N)
    return d if (d != 1 and d != N) else 1

def GMF_Safe(N:int):
    if N <= 1 or not Mem_R(N):
        return 1, ["N is trivial or not in toy ℛ"]
    logs = []
    for pi in Describe(N):
        u, T = 1, StepBudget(pi, N)
        log = [f"start: N={N}, {pi}, T={T}"]
        for t in range(T):
            g = LocalStep(pi, (u, None, t, N))
            if not IsAdmissible(pi, g, t):
                log.append(f"t={t}: inadmissible g={g}")
                break
            u = (u * g) % N
            d = NontrivialGCD(u, N)
            log.append(f"t={t}: u={u}, g={g}, gcd={d}")
            if d != 1:
                log.append(f"SUCCESS factor={d}")
                return d, log
        logs.extend(log)
    return 1, logs

def GMF_Fast(N:int, retries:int=5):
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

if __name__ == "__main__":
    tests = [91, 77, 221, 121, 997, 10007]
    for N in tests:
        d, log = GMF_Safe(N)
        print(f"N={N}: factor={d}")
        print("  log:", " / ".join(log[:6]) + (" ... (truncated)" if len(log)>6 else ""))
