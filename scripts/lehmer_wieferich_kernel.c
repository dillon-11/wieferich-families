/* lehmer_wieferich_kernel.c -- the Lehmer-Salem Wieferich census.
 *
 * Unit: Lehmer's number, the root of L = x^10+x^9-x^7-x^6-x^5-x^4-x^3+x+1
 * (the smallest known Salem number). The unit's
 * Wieferich condition at p: tr(alpha^p) == tr(alpha) = -1 (mod p^2), where
 * tr(alpha^p) is read off x^p mod (L, p^2) against the exact power sums
 * t_0..t_9 = 10,-1,1,2,1,4,4,6,1,2. The mod-p congruence tr(alpha^p) == -1
 * (mod p) holds for every prime (Frobenius); the census asserts it as a guard
 * and flags the mod-p^2 refinement -- heuristic rate 1/p per prime.
 *
 *   cc -O2 -std=c11 -o lehmer_wieferich_kernel lehmer_wieferich_kernel.c -lm
 *   ./lehmer_wieferich_kernel <lo> <hi> [depth]    depth: 2 (default) | 1 control
 *
 * Emits "MEMBER p" lines, "GUARD-VIOLATION p" (never expected), and a final
 * "TALLY nprimes lam flags" line.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;

#define DEG 10
/* x^10 = -x^9 +x^7 +x^6 +x^5 +x^4 +x^3 -x -1 : reduction coeffs (degree 0..9) */
static const int RED[DEG] = { -1, -1, 0, 1, 1, 1, 1, 1, 0, -1 };
/* exact power sums tr(alpha^k), k = 0..9 */
static const long long TK[DEG] = { 10, -1, 1, 2, 1, 4, 4, 6, 1, 2 };

static u64 mulmod(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }

/* c = a*b mod (L, m); a,b,c degree<10, coeffs < m */
static void polymul(const u64 *a, const u64 *b, u64 *c, u64 m) {
    u64 t[2 * DEG - 1];
    memset(t, 0, sizeof(t));
    for (int i = 0; i < DEG; i++) {
        if (!a[i]) continue;
        for (int j = 0; j < DEG; j++) {
            if (!b[j]) continue;
            u64 *p = &t[i + j];
            *p = (u64)(((u128)*p + mulmod(a[i], b[j], m)) % m);
        }
    }
    for (int d = 2 * DEG - 2; d >= DEG; d--) {
        u64 v = t[d];
        if (!v) continue;
        t[d] = 0;
        for (int j = 0; j < DEG; j++) {
            if (RED[j] == 1)       t[d - DEG + j] = (u64)(((u128)t[d - DEG + j] + v) % m);
            else if (RED[j] == -1) t[d - DEG + j] = (u64)(((u128)t[d - DEG + j] + m - v) % m);
        }
    }
    memcpy(c, t, DEG * sizeof(u64));
}

/* trace of x^e mod (L, m) */
static u64 trace_pow(u64 e, u64 m) {
    u64 f[DEG], base[DEG];
    memset(f, 0, sizeof(f)); memset(base, 0, sizeof(base));
    f[0] = 1 % m;          /* 1 */
    base[1] = 1;           /* x */
    while (e) {
        if (e & 1) polymul(f, base, f, m);
        polymul(base, base, base, m);
        e >>= 1;
    }
    u64 tr = 0;
    for (int i = 0; i < DEG; i++) {
        long long tk = TK[i];
        u64 tku = tk >= 0 ? (u64)tk % m : m - ((u64)(-tk) % m);
        tr = (u64)(((u128)tr + mulmod(f[i], tku % m, m)) % m);
    }
    return tr;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s lo hi [depth]\n", argv[0]); return 1; }
    u64 lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    int depth = argc > 3 ? atoi(argv[3]) : 2;

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
    u64 nprimes = 0, flags = 0;
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
            nprimes++;
            lam += 1.0 / (double)p;
            u64 m = depth == 2 ? p * p : p;
            u64 tr = trace_pow(p, m);
            /* guard: tr == -1 (mod p) must ALWAYS hold */
            if ((tr + 1) % p != 0) {
                printf("GUARD-VIOLATION %llu\n", (unsigned long long)p);
                fflush(stdout);
                continue;
            }
            if (tr == m - 1) {
                flags++;
                printf("MEMBER %llu\n", (unsigned long long)p);
                fflush(stdout);
            }
        }
    }
    printf("TALLY %llu %.6f %llu\n", (unsigned long long)nprimes, lam,
           (unsigned long long)flags);
    return 0;
}
