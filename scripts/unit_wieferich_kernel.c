/* unit_wieferich_kernel.c -- the generic unit Wieferich census.
 *
 * Generalizes lehmer_wieferich_kernel.c to ANY monic integer unit polynomial
 * (constant term +-1): the unit Wieferich condition at p is
 * tr(alpha^p) == tr(alpha) (mod p^2), read from x^p mod (P, p^2) against the
 * exact power sums (computed internally by Newton's identities). The mod-p
 * congruence (Frobenius) is asserted as a guard at every prime.
 *
 *   cc -O2 -std=c11 -o unit_wieferich_kernel unit_wieferich_kernel.c -lm
 *   ./unit_wieferich_kernel <lo> <hi> <depth> <a_d> <a_{d-1}> ... <a_0>
 *
 * depth: 2 (census) | 1 (control: every prime flags).
 * Emits "MEMBER p", "GUARD-VIOLATION p", and "TALLY nprimes lam flags".
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;

#define MAXDEG 32
static int DEG;
static long long A[MAXDEG + 1];      /* a_d .. a_0, a_d = 1 */
static long long TK[MAXDEG];         /* power sums t_0..t_{d-1} */

static u64 mulmod(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }

static u64 tou(long long v, u64 m) {
    long long r = v % (long long)m;
    return r >= 0 ? (u64)r : (u64)(r + (long long)m);
}

/* c = a*b mod (P, m) */
static void polymul(const u64 *a, const u64 *b, u64 *c, u64 m) {
    u64 t[2 * MAXDEG];
    int n = DEG;
    memset(t, 0, sizeof(u64) * (2 * n - 1));
    for (int i = 0; i < n; i++) {
        if (!a[i]) continue;
        for (int j = 0; j < n; j++) {
            if (!b[j]) continue;
            t[i + j] = (t[i + j] + mulmod(a[i], b[j], m)) % m;
        }
    }
    for (int d = 2 * n - 2; d >= n; d--) {
        u64 v = t[d];
        if (!v) continue;
        t[d] = 0;
        /* x^n = -(a_{n-1} x^{n-1} + ... + a_0) */
        for (int j = 0; j < n; j++) {
            long long aj = A[n - j];          /* coeff of x^j */
            if (!aj) continue;
            u64 w = mulmod(v, tou(-aj, m), m);
            t[d - n + j] = (t[d - n + j] + w) % m;
        }
    }
    memcpy(c, t, sizeof(u64) * n);
}

static u64 trace_pow(u64 e, u64 m) {
    u64 f[MAXDEG], base[MAXDEG];
    memset(f, 0, sizeof(f)); memset(base, 0, sizeof(base));
    f[0] = 1 % m;
    base[1 % DEG] = DEG > 1 ? 1 : 0;          /* x (deg >= 2 always here) */
    while (e) {
        if (e & 1) polymul(f, base, f, m);
        polymul(base, base, base, m);
        e >>= 1;
    }
    u64 tr = 0;
    for (int i = 0; i < DEG; i++)
        tr = (tr + mulmod(f[i], tou(TK[i], m), m)) % m;
    return tr;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: %s lo hi depth a_d .. a_0\n", argv[0]); return 1; }
    u64 lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    int depth = atoi(argv[3]);
    int ncoef = argc - 4;
    DEG = ncoef - 1;
    if (DEG < 2 || DEG > MAXDEG) { fprintf(stderr, "bad degree\n"); return 1; }
    for (int i = 0; i < ncoef; i++) A[i] = atoll(argv[4 + i]);
    if (A[0] != 1) { fprintf(stderr, "not monic\n"); return 1; }
    if (A[DEG] != 1 && A[DEG] != -1) { fprintf(stderr, "not a unit\n"); return 1; }

    /* Newton: p_k = -k a_{d-k} - sum_{i=1}^{k-1} a_{d-i} p_{k-i}   (k <= d) */
    TK[0] = DEG;
    for (int k = 1; k < DEG; k++) {
        long long s = -(long long)k * A[k];
        for (int i = 1; i < k; i++) s -= A[i] * TK[k - i];
        TK[k] = s;
    }
    long long tr1 = TK[1 % DEG];

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
            u64 m = depth == 3 ? p * p * p : (depth == 2 ? p * p : p);
            u64 tr = trace_pow(p, m);
            u64 want_modp = tou(tr1, p);
            if (tr % p != want_modp) {
                printf("GUARD-VIOLATION %llu\n", (unsigned long long)p);
                fflush(stdout);
                continue;
            }
            if (tr == tou(tr1, m)) {
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
