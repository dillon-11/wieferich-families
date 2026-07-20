#!/usr/bin/env python3
"""The Wilson integral of the family (paper section 2.6).

Lerch's congruence: sum_{a=1}^{p-1} q_p(a) == w_p (mod p), with
q_p(a) = (a^(p-1)-1)/p and w_p = ((p-1)!+1)/p (sign in the paper's
conventions; checked directly below for p <= 300).

Involuted form: for a pairing a*b_a == PAIR (mod p) with PAIR = -+1
(the root pairing of the quadratic unit family x^2 - kx - PAIR), the
section-carry total over the window [1, p-1] obeys

    S(p) = sum_{a=1}^{p-1} (a*b_a - PAIR)/p == 2*sign*w_p (mod p),

sign = +1 for PAIR = -1 (the metallic family x^2-kx-1) and sign = -1
for PAIR = +1 (the norm-plus family x^2-kx+1): the carry-total reads
the Wilson quotient through the norm character of the family.

Run with PAIR = -1 or PAIR = +1; PAIR = 3 is a non-unit pairing and
serves as the control (the identity must fail).

A Wieferich event at (k, p) is a pointwise zero of the Fermat-quotient
spectrum; a Wilson prime (5, 13, 563) is a zero of its total.
"""
import sys

PAIR = -1   # pairing constant a*b_a == PAIR (mod p); -1 metallic, +1 norm-plus
PMAX = 3000


def primes(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i * i :: i] = bytearray(len(s[i * i :: i]))
    return [i for i in range(3, n + 1) if s[i]]


def main():
    sign = 1 if PAIR < 0 else -1
    fails, tested, lerch_bad = [], 0, 0
    for p in primes(PMAX):
        p2 = p * p
        fact = 1
        for a in range(2, p):
            fact = fact * a % p2
        if (fact + 1) % p:
            print(f"VACUOUS wilson-divisibility failed at p={p}")
            return 3
        w = ((fact + 1) // p) % p
        S = 0
        for a in range(1, p):
            b = (PAIR * pow(a, -1, p)) % p
            if b == 0:
                b = p
            S += (a * b - PAIR) // p
        if (S - 2 * sign * w) % p != 0:
            fails.append(p)
        if p <= 300:   # direct Lerch check, independent of the pairing
            qsum = sum((pow(a, p - 1, p2) - 1) // p for a in range(1, p)) % p
            if (qsum - w) % p != 0:
                lerch_bad += 1
        tested += 1
    print(f"tested {tested} primes to {PMAX}; PAIR={PAIR}; "
          f"failures {len(fails)} {fails[:10]}; lerch_direct_bad={lerch_bad}")
    if lerch_bad:
        print("VACUOUS direct Lerch check failed")
        return 3
    if not fails:
        print("CONFIRMED carry-total identity at every prime")
        return 0
    print(f"REFUTED {len(fails)}/{tested} primes violate the identity")
    return 1


if __name__ == "__main__":
    sys.exit(main())
