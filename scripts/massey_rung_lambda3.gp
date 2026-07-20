\\ Massey rung lambda>=3 test for K = Q(sqrt(-11)), p = 5 (Qi arXiv:2402.06028, 5.1.2)
default(parisize, 512M);

p = 5;
K = bnfinit(y^2 - y + 3, 1);
alpha = Mod(y + 1, K.pol);
print("N(alpha) = ", nfeltnorm(K, alpha));

T = polsubcyclo(25, 5);
rnf = rnfinit(K, T);
rnfpol = rnfequation(K.pol, T);

rni = rnfisnorminit(K, T);
res = rnfisnorm(rni, alpha, flag = 100);
beta = res[1]; q = res[2];
print("norm defect q (1 = exact): ", q);
if (q != 1, print("VACUOUS: not an exact norm"); quit);

betaabs = rnfeltreltoabs(rnf, beta);
L = nfinit(rnfpol);
print("L degree: ", poldegree(L.pol));

G = nfgaloisconj(L);
xid = Mod(x, L.pol);
compose(A, B) = subst(lift(A), x, B);
ord5 = List();
{
for (i = 1, #G,
  s = Mod(G[i], L.pol);
  if (s != xid,
    s5 = s;
    for (k = 1, 4, s5 = compose(s5, s));
    if (s5 == xid, listput(ord5, s));
  );
);
}
print("#nontrivial order-5 autos: ", #ord5);
SGIDX = eval(Str(getenv("SGIDX"))); if(SGIDX<1||SGIDX>4, SGIDX=1); sg = ord5[SGIDX];
TWIST = eval(Str(getenv("TWIST")));

\\ A1 = prod_{i=1}^{4} sg^i(beta)^i
bi = Mod(betaabs, L.pol);
{
if (TWIST == 1,
  gam = Mod(x^3 - 2*x + 1, L.pol);
  bi = bi * gam / compose(gam, sg);
  print("twist applied"));
}
A1 = Mod(1, L.pol);
cur = bi;
{
for (i = 1, 4,
  cur = compose(cur, sg);  \\ apply sg: element(x) -> element(sg(x))
  A1 = A1 * cur^i;
);
}
print("A1 computed");

fa = idealfactor(L, A1);
nrow = matsize(fa)[1];
print("A1 factorization rows: ", nrow);

Kid = idealhnf(K, 1);
\\ per-K-prime dedup: map P -> m (= v_Q(A1) mod 5, must be constant over Q|P)
Plist = List(); Mlist = List();
{
for (r = 1, nrow,
  Q = fa[r,1]; vq = fa[r,2];
  ell = Q.p;
  if (ell != 5,
    m = vq % 5;
    dec = idealprimedec(K, ell);
    for (j = 1, #dec,
      P = dec[j];
      piP = nfbasistoalg(K, P.gen[2]);
      piPabs = Mod(subst(lift(liftall(piP)), y, lift(rnfeltreltoabs(rnf, Mod(y, K.pol)))), L.pol);
      if (nfeltval(L, piPabs, Q) > 0,
        found = 0;
        for (t = 1, #Plist,
          if (Plist[t] == [ell, j],
            found = 1;
            if (Mlist[t] != m, print("VACUOUS: inconsistent m over Q|P at ", ell); quit);
          );
        );
        if (!found, listput(Plist, [ell, j]); listput(Mlist, m));
      );
    );
  );
);
for (t = 1, #Plist,
  m = Mlist[t];
  if (m != 0,
    dec = idealprimedec(K, Plist[t][1]);
    Kid = idealmul(K, Kid, idealpow(K, dec[Plist[t][2]], 5 - m));
  );
);
}
pr = bnfisprincipal(K, Kid);
print("class of adjustment ideal: ", pr[1]);
alpha1 = nfbasistoalg(K, pr[2]);
print("alpha1 = ", alpha1);
\\ verify v_Q(alpha1 * A1) = 0 mod 5 for all Q away from 5
a1abs = Mod(subst(lift(liftall(alpha1)), y, lift(rnfeltreltoabs(rnf, Mod(y, K.pol)))), L.pol);
prodel = a1abs * A1;
fv = idealfactor(L, prodel);
bad = 0;
{
for (r = 1, matsize(fv)[1],
  if (fv[r,1].p != 5 && fv[r,2] % 5 != 0, bad++);
);
}
print("away-from-5 valuation check: bad rows = ", bad);

dec5 = idealprimedec(K, 5);
{
if (idealval(K, alpha, dec5[1]) > 0,
  P0 = dec5[1]; Pbar = dec5[2],
  P0 = dec5[2]; Pbar = dec5[1]);
}
abar = Mod(2 - y, K.pol);  \\ conjugate of alpha; generates Pbar
print("check: v_Pbar(abar) = ", idealval(K, abar, Pbar));
v0 = idealval(K, alpha1, P0);
vb = idealval(K, alpha1, Pbar);
print("v_P0(alpha1) = ", v0, "  v_Pbar(alpha1) = ", vb);
\\ normalize to a unit above 5 (alpha, abar have vanishing cup product: member)
u = alpha1 * alpha^(-v0) * abar^(-vb);
t1 = nfbasistoalg(K, nfeltpow(K, u, p - 1));
d = t1 - 1;
w = idealval(K, d, Pbar);
print("v_Pbar(u^(p-1) - 1) = ", w);
print(if(w >= 2, "RUNG-ZERO (lambda >= 3)", "RUNG-NONZERO (lambda = 2)"));
quit
