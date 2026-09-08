"""Numerical checks for Section 3 of arXiv:2608.25279 (companion to the Lean development).

This script is a numerical sanity check, not a verification: Part 2 evaluates the
inequalities of Lemma 3.3 at ISOLATED grid points (5 values of kappa, 50 values of beta,
50 values of s), using interval arithmetic only to make each pointwise evaluation rigorous.
The grid points do not cover the parameter domain of the lemma. Part 1 is an exact
symbolic check of ONE instance (m = 8, kappa = 1000), an example and not coverage.

Part 1 (exact arithmetic in Q(sqrt 2), sympy).  A concrete instance of the roots-of-unity
construction with m = 8, kappa = 1000, beta = 881/1000, s = 1879/500000:
  * numerical stability and rho_q(s,beta;kappa) < q_kappa (C* = 28), i.e. the hypotheses
    of Lemma 3.3 and case (C) of Theorem 1.1;
  * P_8(s,beta;kappa) < 0 (strict cycling condition (3.19));
  * the projection scalars I_{0,j}, j = 1..7, computed both from the definition
    <x0 - M x0, M xj - M x0> and from the half-angle form (3.9); all strictly negative;
  * identity (3.11) at the instance;
  * the cycle equation (3.3) for grad psi = x + (kappa-1) M x at every cycle point;
  * r_max of (3.13) as an exact algebraic number, and the projection identity
    proj_C(x0 + u) = M x0 for exact rational sample points u with |u| < r_max
    (variational inequality (3.12) checked exactly at every vertex);
  * Assumption 2: rho(A_1)^8 = beta^4 < 1, and the constants r0, b* of Proposition 3.4.
Part 2 (floating point scan + rigorous interval arithmetic, mpmath.iv).  For several
kappa and a grid of (s,beta) in the hypothesis region of Lemma 3.3 (numerically stable,
rho_q < q_kappa), verify the conclusion (some m >= 3 has P_m < 0) and every intermediate
claim of the proof of Lemma 3.3 that is imported from [22] in normalized form:
  (3.20) ell(rho) <= beta <= rho^2 with rho = rho_q; beta > 13/42; (3.21) s > (50/3) u (1-beta);
  existence of m0 with 2/3 <= C_beta <= 3/2; real roots (beta >= beta_-(m)) for 3 <= m <= m0;
  (3.23) s_-(beta,m0) <= (50/3) u (1-beta); the overlap (3.14) for 3 <= m < m0;
  s_+(beta,3) >= 2(1+beta)/kappa; and P_{m bar} < 0 for the selected m bar.
  The [22, Lemma B.7] ratio bound and the (3.18) bound 3 + sqrt 5 are checked for m up to 10^4.
Part 3 (floating point).  Monotonicity and Lipschitz bounds of grad psi = x + (kappa-1) proj_C
for the instance of Part 1 on random pairs of points.
All Part 2 evaluations use interval arithmetic: an inequality at a grid point is reported
as holding only if it holds for every point of the enclosing intervals of the evaluation.
"""
from __future__ import annotations
import math, itertools, sys
import numpy as np
import sympy as sp
import mpmath
from mpmath import iv

# ----------------------------------------------------------------------------- helpers
r2 = sp.sqrt(2)

def q2_parts(e):
    """Write an element of Q(sqrt2) as (p, q) with e = p + q*sqrt2, p, q rational."""
    e = sp.expand(sp.radsimp(sp.together(sp.expand(e))))
    p = e.subs(r2, 0)
    q = sp.expand((e - p) / r2)
    assert p.is_Rational and q.is_Rational, (e, p, q)
    return sp.Rational(p), sp.Rational(q)

def q2_sign(e):
    """Exact sign of p + q sqrt2: compare p and -q sqrt2 via squares."""
    p, q = q2_parts(e)
    if q == 0:
        return int(sp.sign(p))
    if p == 0:
        return int(sp.sign(q))
    # sign(p + q sqrt2): if p and q same sign, that sign; else compare p^2 vs 2 q^2
    if sp.sign(p) == sp.sign(q):
        return int(sp.sign(p))
    if p**2 > 2 * q**2:
        return int(sp.sign(p))
    if p**2 < 2 * q**2:
        return int(sp.sign(q))
    return 0

def q2_lt(e1, e2):
    return q2_sign(e2 - e1) > 0

# ----------------------------------------------------------------------------- Part 1
print("=" * 78)
print("PART 1: exact instance in Q(sqrt2), m = 8, kappa = 1000, beta = 881/1000, s = 1879/500000")
print("=" * 78)
kappa = sp.Integer(1000); u = 1 / kappa; Cs = sp.Integer(28)
beta = sp.Rational(881, 1000); s = sp.Rational(1879, 500000); m = 8
theta = 2 * sp.pi / m
c = r2 / 2; sn = r2 / 2  # cos, sin of theta = pi/4
qk = (1 - Cs * u) / (1 + Cs * u)
print(f"q_kappa = {qk} = {float(qk):.6f}")
# numerical stability (2.10)
stab = 2 * (1 + beta) / kappa
assert s > 0 and s < stab
print(f"numerical stability: 0 < s = {s} = {float(s):.7f} < 2(1+beta)/kappa = {float(stab):.7f}  [exact]")
# rho_q(s,beta;kappa): max over t in {1+beta-s, 1+beta-s kappa} of f(t)
def rho_of_t(t):
    if q2_sign(4 * beta - t**2) >= 0:  # |t| <= 2 sqrt(beta): complex pair, modulus sqrt(beta)
        return sp.sqrt(beta)
    return (sp.Abs(t) + sp.sqrt(t**2 - 4 * beta)) / 2
t1 = 1 + beta - s; tk = 1 + beta - s * kappa
print(f"t at lambda=1: {t1} ({float(t1):.6f}), 2 sqrt(beta) = {float(2*sp.sqrt(beta)):.6f}; t at lambda=kappa: {tk} ({float(tk):.6f})")
r1 = rho_of_t(t1); rk = rho_of_t(tk)
rho_q = sp.Max(r1, rk)
print(f"rho(A_1) = {r1} = {float(r1):.6f}; rho(A_kappa) = {rk} = {float(rk):.6f}; rho_q = {float(rho_q):.6f}")
# rho_q < q_kappa exactly.  Each rho is either sqrt(beta) or (|t| + sqrt(D))/2 with D = t^2 - 4 beta rational.
def rho_lt(t, y):
    """exact test rho_of_t(t) < y for rational t, y > 0"""
    if q2_sign(4 * beta - t**2) >= 0:
        return beta < y**2
    D = t**2 - 4 * beta
    return (2 * y - sp.Abs(t) > 0) and (D < (2 * y - sp.Abs(t))**2)
assert rho_lt(t1, qk) and rho_lt(tk, qk)
print(f"rho_q < q_kappa  [exact: at lambda = 1 the roots are real, D = t^2 - 4 beta = {t1**2 - 4*beta} < (2 q_kappa - |t|)^2 = {(2*qk - t1)**2}; at lambda = kappa the pair is complex, beta < q_kappa^2]")
# P_8 exact
P8 = s**2 - 2 * (beta - c + u * (1 - beta * c)) * s + 2 * u * (1 - c) * (1 + beta**2 - 2 * beta * c)
p, q = q2_parts(P8)
print(f"P_8(s,beta;kappa) = {p} + ({q}) sqrt2 = {float(P8):.6e}; sign = {q2_sign(P8)}  [exact]")
assert q2_sign(P8) < 0
# a, b, M, cycle points
a_ = ((1 + beta - s) - (1 + beta) * c) / ((kappa - 1) * s)
b_ = -(1 - beta) * sn / ((kappa - 1) * s)
print(f"a = {float(a_):.6f}, b = {float(b_):.6f}, det M = a^2+b^2 = {float(a_**2+b_**2):.6f}")
def rot(j):
    cj = sp.cos(j * theta); sj = sp.sin(j * theta)
    return sp.Matrix([[cj, -sj], [sj, cj]])
M = sp.Matrix([[a_, -b_], [b_, a_]])
x0 = sp.Matrix([1, 0])
X = [sp.simplify(rot(j) * x0) for j in range(m)]
MX = [sp.simplify(M * X[j]) for j in range(m)]
# I_{0,j} from the definition and from (3.9)
cot_vals = {1: 1 + r2, 2: sp.Integer(1), 3: r2 - 1, 4: sp.Integer(0), 5: -(r2 - 1), 6: sp.Integer(-1), 7: -(1 + r2)}
print("I_{0,j}: definition vs (3.9)")
I0 = {}
for j in range(1, m):
    Idef = sp.expand((X[0] - MX[0]).dot(MX[j] - MX[0]))
    I39 = sp.expand((1 - sp.cos(j * theta)) * (a_**2 + b_**2 - a_ - b_ * cot_vals[j]))
    assert q2_sign(Idef - I39) == 0
    I0[j] = Idef
    print(f"  j={j}: I_(0,j) = {float(Idef):+.6e}  sign {q2_sign(Idef)}  (3.9) agrees exactly")
    assert q2_sign(Idef) < 0
# identity (3.11)
lhs = P8; rhs = (kappa - 1)**2 * s**2 / (kappa * (1 - c)) * I0[1]
assert q2_sign(lhs - rhs) == 0
print("identity (3.11): P_8 = (kappa-1)^2 s^2 / (kappa (1 - cos theta)) I_(0,1)  [exact]")
# cycle equation (3.3): grad psi(x_t) = x_t + (kappa-1) M x_t equals ((1+beta) x_t - beta x_{t-1} - x_{t+1})/s
for t in range(m):
    g1 = X[t] + (kappa - 1) * MX[t]
    g2 = ((1 + beta) * X[t] - beta * X[(t - 1) % m] - X[(t + 1) % m]) / s
    d = sp.expand(g1 - g2)
    assert q2_sign(d[0]) == 0 and q2_sign(d[1]) == 0
print("cycle equation (3.3) with grad psi(x) = x + (kappa-1) proj_C(x) = x + (kappa-1) M x: exact at all 8 cycle points")
# r_max: min_j (-I_{0,j}) / |M (x_j - x_0)|,  |M(x_j-x_0)|^2 = (a^2+b^2)(2 - 2 cos(j theta))
rmax2 = None; jstar = None
for j in range(1, m):
    val2 = I0[j]**2 / ((a_**2 + b_**2) * (2 - 2 * sp.cos(j * theta)))
    val2 = sp.expand(val2)
    if rmax2 is None or q2_lt(val2, rmax2):
        rmax2, jstar = val2, j
p, q = q2_parts(rmax2)
rmax = sp.sqrt(rmax2)
print(f"r_max^2 = {p} + ({q}) sqrt2 (attained at j = {jstar}); r_max = {float(rmax):.6f}")
# projection identity on the ball: exact rational sample points u with |u|^2 < r_max^2
rng = np.random.default_rng(3)
nsamp = 400; nok = 0
for _ in range(nsamp):
    ang = rng.uniform(0, 2 * math.pi); rad = rng.uniform(0, 1) * float(rmax) * 0.999
    uu = sp.Matrix([sp.Rational(int(round(rad * math.cos(ang) * 10**8)), 10**8), sp.Rational(int(round(rad * math.sin(ang) * 10**8)), 10**8)])
    if not q2_lt(sp.expand(uu.dot(uu)), rmax2):
        continue
    for t in range(m):
        xt = X[t] + uu
        for j in range(m):
            if j == t: continue
            val = sp.expand((xt - MX[t]).dot(MX[j] - MX[t]))
            assert q2_sign(val) <= 0, (t, j, val)
    nok += 1
print(f"projection identity proj_C(x_t + u) = M x_t checked exactly at {nok} rational sample points u with |u| < r_max, all 8 cycle points, all 7 vertices each: PASS")
# a point slightly outside r_max where (3.12) fails, to show r_max is not slack: along the binding direction
# binding vertex j* at t=0: direction of M(x_j*-x_0) inward; take u = -(1+eps) r_max * n, n = M(x_j* - x_0)/|.|
# (numerical illustration only)
nvec = np.array([float(v) for v in (MX[jstar] - MX[0])]); nvec /= np.linalg.norm(nvec)
for eps in (0.99, 1.01):
    uu = eps * float(rmax) * nvec
    xt = np.array([1.0, 0.0]) + uu
    vals = [np.dot(xt - np.array([float(v) for v in MX[0]]), np.array([float(v) for v in (MX[j] - MX[0])])) for j in range(1, m)]
    print(f"  numerical: u = {eps} r_max along the binding normal: max_j <x_0+u-Mx_0, Mx_j-Mx_0> = {max(vals):+.3e} ({'<=0' if max(vals)<=0 else '>0, projection changes'})")
# Assumption 2
tA = 1 + beta - s
assert rho_lt(tA, sp.Integer(1))
print(f"A_1 = A_1(s,beta): trace {tA}, real eigenvalues, rho(A_1) = {float(r1):.6f} < 1 exactly (D < (2 - t)^2), so rho(A_1^8) = rho(A_1)^8 = {float(r1**8):.6f} < 1  [exact]")
r0 = rmax / 2; bstar = (kappa - 1) * sp.sqrt(a_**2 + b_**2)
print(f"Proposition 3.4 constants: r0 = r_max/2 = {float(r0):.6f}; b* = (kappa-1) sqrt(a^2+b^2) = {float(bstar):.6f}; lambda* = 1")
# Lemma 4.4 / Theorem 4.5 constants for this instance (floating point)
h = math.sqrt(2 * float(s) / (1 + float(beta))); gam = -math.log(float(beta)) / h
tau2 = h * h * (1 - float(beta)**2)
A1 = np.array([[1 + float(beta) - float(s), -float(beta)], [1.0, 0.0]])
B = np.array([[1.0], [0.0]])
G0 = 0.0
for k in range(1, 3000):
    G0 = max(G0, sum(np.linalg.norm(np.linalg.matrix_power(A1, k - i) @ B, 2) for i in range(1, k + 1)))
dcirc = 2 * math.sin(math.pi / m)
aa = min(float(r0), dcirc) / 4
delta = aa / (2 * G0); c0 = delta**2 / (2 * tau2)
print(f"OBABO tuning realizing (s,beta): h = {h:.6f}, gamma = {gam:.6f} (gamma h = {gam*h:.6f}), tau^2 = {tau2:.6e}")
print(f"Lemma 4.4 constants (d = 2, H_j = Id, A_j = A_1 (+) A_1): G0 = {G0:.4f} (sup over k <= 3000), d_circ = {dcirc:.6f}, a = {aa:.6f}, delta = {delta:.4e}, c0 = {c0:.4e} = 1/{1/c0:.0f}")
print(f"  N_R = floor(e^(c0 R^2)/16) >= 1 once R >= sqrt(log(16)/c0) = {math.sqrt(math.log(16)/c0):.1f}")

# ----------------------------------------------------------------------------- Part 2
print()
print("=" * 78)
print("PART 2: Lemma 3.3 and its imported inputs on a grid, floating scan + interval evaluation at isolated grid points")
print("=" * 78)
mpmath.mp.dps = 40
iv.dps = 40

def scan(kappa_f, Cs_f=28.0, nb=50, ns=50, mmax=200):
    u = 1.0 / kappa_f; qk = (1 - Cs_f * u) / (1 + Cs_f * u); g = (1 - u) / (1 + u)
    ms = np.arange(3, mmax + 1); cm = np.cos(2 * np.pi / ms)
    fails = []; npts = 0; mbars = {}; minmargin = 1e9
    worst = None; points = []
    # beta grid concentrated near 1 (the region rho_q < q_kappa lies near the optimal tuning)
    bgrid = 1 - np.logspace(math.log10(0.7), math.log10(2e-4), nb)
    for bt in bgrid:
        for sf in np.linspace(0.02, 0.995, ns):
            s_ = sf * 2 * (1 + bt) / kappa_f
            # rho_q
            def f(t):
                return math.sqrt(bt) if abs(t) <= 2 * math.sqrt(bt) else (abs(t) + math.sqrt(t * t - 4 * bt)) / 2
            rho = max(f(1 + bt - s_), f(1 + bt - s_ * kappa_f))
            if not rho < qk: continue
            npts += 1
            P = s_**2 - 2 * (bt - cm + u * (1 - bt * cm)) * s_ + 2 * u * (1 - cm) * (1 + bt**2 - 2 * bt * cm)
            conclusion = (P < 0).any()
            # Step 1: (3.20) and beta > 13/42
            ell = rho * (g - rho) / (1 - g * rho)
            step1 = (ell <= bt + 1e-12) and (bt <= rho**2 + 1e-12) and (bt > 13 / 42)
            # Step 2: (3.21), m0, real roots for 3..m0, (3.23)
            step21 = s_ > 50 / 3 * u * (1 - bt)
            Cb = (bt - cm) / (1 - bt)
            idx = np.where((Cb >= 2 / 3) & (Cb <= 1.5))[0]
            m0 = None; step2 = False; step3 = False; mbar = None; overlap = True; sp3 = False
            if len(idx) > 0:
                m0 = int(ms[idx[0]])
                A = bt - cm + u * (1 - bt * cm); B2 = A**2 - 2 * u * (1 - cm) * (1 + bt**2 - 2 * bt * cm)
                real = B2[:m0 - 2] >= 0  # m = 3..m0
                sm = A - np.sqrt(np.maximum(B2, 0)); spl = A + np.sqrt(np.maximum(B2, 0))
                bound323 = sm[m0 - 3] <= 50 / 3 * u * (1 - bt) + 1e-15
                step2 = step21 and real.all() and bound323
                # Step 3
                cands = [mm for mm in range(3, m0 + 1) if s_ > sm[mm - 3]]
                if cands:
                    mbar = cands[0]
                    step3 = s_ < spl[mbar - 3] and P[mbar - 3] < 0
                overlap = all(sm[mm - 3] < spl[mm - 2] for mm in range(3, m0))
                sp3 = spl[0] >= 2 * (1 + bt) / kappa_f - 1e-15
            ok = conclusion and step1 and step2 and step3 and overlap and sp3
            if not ok:
                fails.append((bt, s_, rho, conclusion, step1, step21, m0, step2, step3, overlap, sp3))
            else:
                mbars[mbar] = mbars.get(mbar, 0) + 1
                points.append((bt, s_, mbar, m0))
                marg = -P[mbar - 3] / (2 * (1 + bt) / kappa_f)**2
                if marg < minmargin: minmargin, worst = marg, (bt, s_, mbar, m0)
    return npts, fails, mbars, minmargin, worst, points

def eval_point(kappa_f, bt, s_, mbar, m0, Cs_f=28.0):
    """Interval evaluation of every inequality of Lemma 3.3's proof at the single point (s, beta, kappa)."""
    K = iv.mpf(kappa_f); u = 1 / K; b = iv.mpf(bt); S = iv.mpf(s_); C = iv.mpf(Cs_f)
    qk = (1 - C * u) / (1 + C * u); g = (1 - u) / (1 + u)
    res = {}
    res['stable'] = (S > 0) and (S < 2 * (1 + b) / K)
    def f(t):
        # returns (interval for the modulus of the larger root, branch); branch must be certain
        if t**2 <= 4 * b: return iv.sqrt(b), 'complex'
        if t**2 >= 4 * b: return (abs(t) + iv.sqrt(t**2 - 4 * b)) / 2, 'real'
        return None, None
    (r1, br1), (rk, brk) = f(1 + b - S), f(1 + b - S * K)
    if r1 is None or rk is None: res['rho_branch'] = False; return res
    # rho_q = max(r1, rk) as an interval
    rho = iv.mpf([max(r1.a, rk.a), max(r1.b, rk.b)])
    res['rho_q < q_kappa'] = rho < qk
    ell = rho * (g - rho) / (1 - g * rho)
    res['(3.20) ell(rho) <= beta'] = ell <= b
    if br1 == 'complex' and brk == 'complex':
        res['(3.20) beta <= rho^2'] = True  # rho = sqrt(beta) exactly at both endpoints: equality
    elif (br1 == 'real' and r1 > iv.sqrt(b)) or (brk == 'real' and rk > iv.sqrt(b)):
        res['(3.20) beta <= rho^2'] = b < rho**2
    else:
        res['(3.20) beta <= rho^2'] = b <= rho**2
    res['beta > 13/42'] = b > iv.mpf(13) / 42
    res['(3.21) s > 50/3 u (1-beta)'] = S > iv.mpf(50) / 3 * u * (1 - b)
    def cosm(mm): return iv.cos(2 * iv.pi / mm)
    cm0 = cosm(m0); Cb = (b - cm0) / (1 - b)
    res['m0: 2/3 <= C_beta <= 3/2'] = (Cb >= iv.mpf(2) / 3) and (Cb <= iv.mpf(3) / 2)
    def AB(mm):
        cmm = cosm(mm); A = b - cmm + u * (1 - b * cmm); B2 = A**2 - 2 * u * (1 - cmm) * (1 + b**2 - 2 * b * cmm)
        return A, B2
    allreal = True
    for mm in range(3, m0 + 1):
        A, B2 = AB(mm); allreal = allreal and (B2 >= 0)
    res['real roots for 3<=m<=m0'] = allreal
    A0, B20 = AB(m0)
    res['(3.23) s_-(beta,m0) <= 50/3 u (1-beta)'] = (A0 - iv.sqrt(B20)) <= iv.mpf(50) / 3 * u * (1 - b)
    ov = True
    for mm in range(3, m0):
        A1_, B1_ = AB(mm); A2_, B2_ = AB(mm + 1)
        ov = ov and ((A1_ - iv.sqrt(B1_)) < (A2_ + iv.sqrt(B2_)))
    res['(3.14) overlap for 3<=m<m0'] = ov
    A3, B23 = AB(3)
    res['s_+(beta,3) >= 2(1+beta)/kappa'] = (A3 + iv.sqrt(B23)) >= 2 * (1 + b) / K
    Am, B2m = AB(mbar)
    res['minimality: s <= s_-(beta,m) for 3<=m<mbar'] = all((S <= (AB(mm)[0] - iv.sqrt(AB(mm)[1]))) for mm in range(3, mbar)) if mbar > 3 else True
    res['s_-(beta,mbar) < s < s_+(beta,mbar)'] = ((Am - iv.sqrt(B2m)) < S) and (S < (Am + iv.sqrt(B2m)))
    cmb = cosm(mbar)
    Pm = S**2 - 2 * (b - cmb + u * (1 - b * cmb)) * S + 2 * u * (1 - cmb) * (1 + b**2 - 2 * b * cmb)
    res['P_mbar < 0'] = Pm < 0
    return res

for kappa_f in (1000.0, 3000.0, 1e4, 1e5, 1e6):
    npts, fails, mbars, minmargin, worst, points = scan(kappa_f)
    if worst is None:
        print(f"kappa = {kappa_f:.0f}: grid points in region {npts}, failures {len(fails)}, no point passing all steps"); continue
    print(f"kappa = {kappa_f:.0f}: grid points in the hypothesis region: {npts}; failures of any step: {len(fails)}; m_bar histogram: {dict(sorted(mbars.items()))}; smallest normalized margin -P_mbar/(2(1+beta)/kappa)^2 = {minmargin:.3e} at beta={worst[0]:.4f}, s={worst[1]:.3e}, mbar={worst[2]}, m0={worst[3]}")
    if fails:
        for fl in fails[:5]: print("   FAIL:", fl)
    # interval evaluation at the worst point and at a few random points of the region
    res = eval_point(kappa_f, worst[0], worst[1], worst[2], worst[3])
    bad = [k for k, v in res.items() if v is not True]
    print(f"   interval evaluation at the worst point: {'all inequalities hold' if not bad else 'FAILED: ' + str(bad)}")
    ncert = 0; nbad = 0; failkeys = {}
    for (bt, s_, mbar, m0) in points:
        res = eval_point(kappa_f, bt, s_, mbar, m0)
        bad = [k for k, v in res.items() if v is not True]
        if bad:
            nbad += 1
            for k in bad: failkeys[k] = failkeys.get(k, 0) + 1
        else: ncert += 1
    print(f"   interval evaluation at ALL region grid points: {ncert} points pass, {nbad} fail" + (f"; failing items: {failkeys}" if failkeys else ""))

# imported facts checked for m up to 1e4
print("\n[22, Lemma B.7] ratio (1-cos theta_m)/(1-cos theta_{m+1}) in [1, 3/2] for 3 <= m <= 10^4, and the (3.18) bound:")
ms = np.arange(3, 10001); r = (1 - np.cos(2 * np.pi / ms)) / (1 - np.cos(2 * np.pi / (ms + 1)))
print(f"   min ratio {r.min():.6f} (m={ms[r.argmin()]}), max ratio {r.max():.6f} (m={ms[r.argmax()]})")
ms4 = np.arange(4, 10001); cc = np.cos(2 * np.pi / (ms4 + 1)); xi = 1 / cc - 1; rhs318 = xi + 2 * (1 - np.cos(2 * np.pi / ms4)) / xi
print(f"   max over 4 <= m <= 10^4 of xi_(m+1) + 2(1 - cos theta_m)/xi_(m+1) = {rhs318.max():.6f} (m = {ms4[rhs318.argmax()]}), vs 3 + sqrt5 = {3+math.sqrt(5):.6f}")
# interval evaluation of the m=4 value: 1/cos(2pi/5) - 1 + 2(1 - cos(pi/2)) / (1/cos(2pi/5) - 1) = 1/cos(2 pi/5) + 1  (< 3+sqrt5)
c5 = iv.cos(2 * iv.pi / 5); xi5 = 1 / c5 - 1
v4 = xi5 + 2 * (1 - iv.cos(2 * iv.pi / 4)) / xi5
print(f"   m = 4 value (interval): {v4}; 3 + sqrt5 = {3 + iv.sqrt(5)}; inequality holds {v4 < 3 + iv.sqrt(5)}")

# ----------------------------------------------------------------------------- Part 3
print()
print("=" * 78)
print("PART 3: monotonicity and Lipschitz bounds of grad psi for the Part 1 instance (floating point)")
print("=" * 78)
verts = np.array([[float(v) for v in MX[j]] for j in range(m)])
def proj_polygon(x):
    # inside test via half-planes (vertices in counterclockwise order)
    inside = True
    for j in range(m):
        p1, p2 = verts[j], verts[(j + 1) % m]; e = p2 - p1; nrm = np.array([e[1], -e[0]])
        if np.dot(x - p1, nrm) > 0: inside = False; break
    if inside: return x.copy()
    best = None; bd = 1e18
    for j in range(m):
        p1, p2 = verts[j], verts[(j + 1) % m]; e = p2 - p1
        tpar = np.clip(np.dot(x - p1, e) / np.dot(e, e), 0, 1); pr = p1 + tpar * e; d = np.linalg.norm(x - pr)
        if d < bd: bd, best = d, pr
    return best
kf = float(kappa)
def grad_psi(x): return x + (kf - 1) * proj_polygon(x)
rng = np.random.default_rng(11)
mono_min = 1e9; lip_max = 0
for _ in range(20000):
    x = rng.normal(size=2) * 2; y = rng.normal(size=2) * 2
    d = x - y; gd = grad_psi(x) - grad_psi(y)
    mono_min = min(mono_min, np.dot(gd, d) / np.dot(d, d)); lip_max = max(lip_max, np.linalg.norm(gd) / np.linalg.norm(d))
print(f"min over 20000 random pairs of <grad psi(x)-grad psi(y), x-y>/|x-y|^2 = {mono_min:.6f} (>= 1 required)")
print(f"max over 20000 random pairs of |grad psi(x)-grad psi(y)|/|x-y| = {lip_max:.6f} (<= kappa = {kf:.0f} required)")
# check (3.8) numerically: grad psi(x_t + u) - grad psi(x_t) = u for |u| <= r_max
worst = 0
for t in range(m):
    xt = np.array([float(v) for v in X[t]])
    for _ in range(2000):
        ang = rng.uniform(0, 2 * math.pi); rad = rng.uniform(0, 1) * float(rmax)
        uu = rad * np.array([math.cos(ang), math.sin(ang)])
        worst = max(worst, np.linalg.norm(grad_psi(xt + uu) - grad_psi(xt) - uu))
print(f"max over cycle points and 2000 random |u| <= r_max each of |grad psi(x_t+u) - grad psi(x_t) - u| = {worst:.3e}")
