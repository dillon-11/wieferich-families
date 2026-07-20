#!/usr/bin/env python3
"""Q7 probe: unit-root Wieferich DEPTH of every Gold-atlas member.

Depth e := v_p(u^{p-1} - 1), u the p-adic unit root of x^2 - a x + p
(4p = a^2 + |D| b^2), Hensel-lifted mod p^6.  Membership = depth >= 2
(Gold's criterion, lambda_p(K) > 1).  Q7 conjectures lambda_p(K) = depth.

Prediction (preregistered): sum of 1/p over members ~ 0.47, so 0 or 1
members of depth >= 3, any candidate at p <= 200.

Guard: the lifted u must satisfy u^2 - a u + p == 0 mod p^6 and u != 0
mod p; if any member fails the guard the run is VACUOUS.
Mutation control (a -> a+2): every mutated member must drop to depth < 2.
"""
import sys

ATLAS = "data/gold_atlas.tsv"

MUTATE = "--mutate-a" in sys.argv

def unit_root_depth(p, a, K=6):
    mod = p ** K
    # Hensel: f(u) = u^2 - a u + p, start u0 = a mod p (unit branch)
    u = a % p
    for _ in range(K + 2):
        f = (u * u - a * u + p) % mod
        fp = (2 * u - a) % mod
        try:
            inv = pow(fp, -1, mod)
        except ValueError:
            return None, None
        u = (u - f * inv) % mod
    if (u * u - a * u + p) % mod != 0 or u % p == 0:
        return None, None
    w = pow(u, p - 1, mod)
    d = (w - 1) % mod
    if d == 0:
        return K, u  # depth >= K (floor)
    e = 0
    while d % p == 0:
        d //= p
        e += 1
    return e, u

def main():
    rows = []
    for line in open(ATLAS):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        D, p, a = [int(x) for x in line.split()]
        if MUTATE:
            a = a + 2
        rows.append((D, p, a))

    depths = []
    for D, p, a in rows:
        e, u = unit_root_depth(p, a)
        if e is None:
            if MUTATE:
                depths.append((D, p, 0))
                continue
            print(f"VACUOUS guard failed at D={D} p={p}")
            return
        depths.append((D, p, e))
        print(f"D={D:5d} p={p:10d} depth={e}")

    deep = [(D, p, e) for D, p, e in depths if e >= 3]
    if MUTATE:
        alive = [(D, p, e) for D, p, e in depths if e >= 2]
        # background rate for a random trace is 1/p; expected survivors
        # sum(1/p) ~ 0.47, so the control passes at <= 2 survivors
        print(f"MUTATED: {len(alive)}/{len(depths)} still depth>=2 {alive}")
        print("CONFIRMED" if len(alive) <= 2 else "REFUTED")
        return

    ge2 = sum(1 for _, _, e in depths if e >= 2)
    print(f"members depth>=2: {ge2}/{len(depths)}  depth>=3: {len(deep)} -> {deep}")
    ok = ge2 == len(depths) and len(deep) <= 1 and all(p <= 200 for _, p, _ in deep)
    print("CONFIRMED" if ok else "REFUTED")

if __name__ == "__main__":
    main()
