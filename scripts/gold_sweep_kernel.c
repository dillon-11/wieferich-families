/* gold_sweep_kernel.c -- the h-graded Gold (unit-root Wieferich) sweep in C.
 *
 * Closed form: a(a^p - a)/p == -1 (mod p) at principal split primes, with
 * a the Cornacchia trace (4p = a^2 + |D| b^2); equivalent to the depth-2
 * Hensel unit-root (Gold) flag, one Frobenius power per prime.
 * Segmented sieve over [lo, hi], 47 fields h = 1..5. Emits "MEMBER D p a"
 * lines plus a "TALLY splits lam count" line per run for Poisson gating
 * across shards.
 *
 *   cc -O2 -std=c11 -o gold_sweep_kernel gold_sweep_kernel.c -lm
 *   ./gold_sweep_kernel 100000000 1000000000
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;

static const int64_t FIELDS[] = {
    -3, -4, -7, -8, -11, -19, -43, -67, -163,
    -15, -20, -24, -35, -40, -51, -52, -88, -91, -115,
    -23, -31, -59, -83, -107, -139, -211, -283, -307, -331, -379, -499,
    -39, -55, -56, -68, -84, -120, -132, -136,
    -47, -79, -103, -127, -131, -179, -227, -347,
};
#define NFIELDS (sizeof(FIELDS) / sizeof(FIELDS[0]))

static u64 mulmod(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }

static u64 powmod(u64 a, u64 e, u64 m) {
    u64 r = 1 % m;
    a %= m;
    while (e) {
        if (e & 1) r = mulmod(r, a, m);
        a = mulmod(a, a, m);
        e >>= 1;
    }
    return r;
}

/* Tonelli-Shanks sqrt of a mod prime p; returns 0 sentinel-free via *ok. */
static u64 sqrt_mod(u64 a, u64 p, int *ok) {
    a %= p;
    *ok = 1;
    if (a == 0) return 0;
    if (powmod(a, (p - 1) / 2, p) != 1) { *ok = 0; return 0; }
    if ((p & 3) == 3) return powmod(a, (p + 1) / 4, p);
    u64 q = p - 1, z = 2;
    int s = 0;
    while (!(q & 1)) { q >>= 1; s++; }
    while (powmod(z, (p - 1) / 2, p) != p - 1) z++;
    int m = s;
    u64 c = powmod(z, q, p), t = powmod(a, q, p), r = powmod(a, (q + 1) / 2, p);
    while (t != 1) {
        int i = 0;
        u64 tt = t;
        while (tt != 1) { tt = mulmod(tt, tt, p); i++; }
        u64 b = powmod(c, (u64)1 << (m - i - 1), p);
        m = i;
        c = mulmod(b, b, p);
        t = mulmod(t, c, p);
        r = mulmod(r, b, p);
    }
    return r;
}

/* modified Cornacchia: x with 4p = x^2 + d*y^2 (d = |D|); 0 if not principal. */
static u64 cornacchia_trace(u64 d, u64 p, u64 sq_negD) {
    u64 lim = (u64)sqrtl(4.0L * p);
    u64 roots[2] = { sq_negD, p - sq_negD };
    for (int k = 0; k < 2; k++) {
        u64 r = roots[k];
        if ((r & 1) != (d & 1)) r += p;      /* match parity of d */
        u64 a = 2 * p, b = r;
        while (b > lim) { u64 t = a % b; a = b; b = t; }
        u128 t = (u128)4 * p - (u128)b * b;
        if (t % d == 0) {
            u128 y2 = t / d;
            u64 y = (u64)sqrtl((long double)y2);
            for (u64 yy = y > 1 ? y - 1 : 0; yy <= y + 1; yy++)
                if ((u128)yy * yy == y2) return b;
        }
    }
    return 0;
}

/* closed form: a(a^p - a)/p == -1 mod p, computed mod p^2 (p^2 < 2^63 ok). */
static int is_wief(u64 a, u64 p) {
    u64 p2 = p * p;
    u64 ap = powmod(a % p2, p, p2);
    u64 diff = (ap + p2 - a % p2) % p2;       /* a^p - a mod p^2 */
    if (diff % p != 0) return 0;              /* always 0 by Fermat */
    u64 c = (diff / p) % p;
    return mulmod(a % p, c, p) == p - 1;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s lo hi\n", argv[0]); return 1; }
    u64 lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);

    /* base primes to sqrt(hi) */
    u64 base_lim = (u64)sqrtl((long double)hi) + 2;
    char *comp = calloc(base_lim + 1, 1);
    u64 nbase = 0, *base = malloc(sizeof(u64) * (base_lim / 2 + 100));
    for (u64 i = 2; i <= base_lim; i++)
        if (!comp[i]) {
            base[nbase++] = i;
            for (u64 j = i * i; j <= base_lim; j += i) comp[j] = 1;
        }

    const u64 SEG = 1 << 22;
    char *seg = malloc(SEG);
    u64 splits = 0, flags = 0;
    double lam = 0.0;

    for (u64 s = lo; s < hi; s += SEG) {
        u64 e = s + SEG < hi ? s + SEG : hi;
        memset(seg, 0, SEG);
        for (u64 i = 0; i < nbase; i++) {
            u64 q = base[i], st = (s + q - 1) / q * q;
            if (st < q * q) st = q * q;
            for (u64 j = st; j < e; j += q) seg[j - s] = 1;
        }
        for (u64 p = s; p < e; p++) {
            if (seg[p - s] || p < 5) continue;
            for (size_t f = 0; f < NFIELDS; f++) {
                u64 d = (u64)(-FIELDS[f]);
                if (p % d == 0) continue;
                int ok;
                u64 r0 = sqrt_mod((p - d % p) % p, p, &ok);  /* sqrt(-d) */
                if (!ok) continue;
                u64 a = cornacchia_trace(d, p, r0);
                if (!a) continue;
                splits++;
                lam += 1.0 / (double)p;
                if (is_wief(a, p)) {
                    flags++;
                    printf("MEMBER %lld %llu %llu\n", (long long)FIELDS[f],
                           (unsigned long long)p, (unsigned long long)a);
                    fflush(stdout);
                }
            }
        }
    }
    printf("TALLY %llu %.6f %llu\n", (unsigned long long)splits, lam,
           (unsigned long long)flags);
    return 0;
}
