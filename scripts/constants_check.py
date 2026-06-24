#!/usr/bin/env python3
"""Audit constants for the tenth Prop. 5.1 coefficient revision.

This is not the Arb finite certificate.  It computes the elementary numerical
allowances used in the analytic sign-lock.  Unlike the ninth diagnostic script,
P4 and the far-tail allowance are computed from the displayed formulae rather
than hard-coded.
"""
import math

zmax = 50.0/27.0
m0 = 361
budget = m0*m0*math.exp(-zmax)*(1.0-2.0/m0)
print(f"C2 budget at theta=0.9, m0=361: {budget:.12f}")

# Poisson moment helper: sum_{s>=0} x^s/s! f(s).
def pois_sum(x, f, n=200):
    term = 1.0
    total = f(0)*term
    for s in range(1, n):
        term *= x/s
        total += term*f(s)
        if abs(term) < 1e-300:
            break
    return total

e1 = lambda s: s*(s+1)/2.0
q2 = lambda s: s*(s+1)*(2*s+1)/6.0
ztilde = zmax*math.exp(0.2237)

P1 = 0.5*(1.168**2)*pois_sum(ztilde, lambda s: e1(s)**2) + 0.75*pois_sum(zmax, q2)
P2 = 1.095*pois_sum(zmax, lambda s: s)
P3a = pois_sum(zmax, lambda s: 4.258*(2*s+3)+0.25)
P3b = 36.6*math.exp(zmax)
P3c = 89.8*math.exp(zmax)

# P4 cross terms, full-factor version.
S_e1_tilde = pois_sum(ztilde, e1)
S_e1s_tilde = pois_sum(ztilde, lambda s: e1(s)*s)
S_s = pois_sum(zmax, lambda s: s)
P4_dom = 1.168*13.2*S_e1_tilde
P4_uv = 1.168*1.095/m0*S_e1s_tilde
P4_veps = 1.095*13.2/m0*S_s
P4_veu = 1.095*13.2*1.168/(m0*m0)*S_e1s_tilde
P4 = P4_dom + P4_uv + P4_veps + P4_veu

# Far tail in the displayed Stirling/saddle bound. Scan N at the binding m=361.
def far_tail_m2_scaled(m=m0):
    L = math.ceil(m/3)
    best = (-1.0, None)
    for N in range(1, int((40.0/3.0)*m)+1):
        z = 5.0*N/(36.0*m)
        logv = (math.log(36.0) + 6.37 - math.log(5.0*N)
                + m*math.log(m) - math.lgamma(m)
                + math.log(2.04) + L*math.log(z) - math.lgamma(L+1))
        val = math.exp(logv)*m*m
        if val > best[0]:
            best = (val, N)
    return best
Tail_actual, Tail_N = far_tail_m2_scaled()
Tails = max(Tail_actual, 1e-160)

pieces = [
    ("P1 gamma residual", P1, 426),
    ("P2 d drift", P2, 13),
    ("P3a two-block recentering", P3a, 184),
    ("P3b j>=3 two-block", P3b, 234),
    ("P3c >=3 blocks", P3c, 573),
    ("P4 cross terms", P4, 784),
    ("far tail m^2-scaled", Tails, 1),
]
print("\nAnalytic C2 budget pieces (computed value, rounded allowance):")
total_allow = 0
for name, val, allow in pieces:
    total_allow += allow
    print(f"  {name:30s} {val:14.6f}  <= {allow}")
print(f"  P4 breakdown: dominant={P4_dom:.6f}, u*v={P4_uv:.6f}, v*eps={P4_veps:.6f}, v*eps*u={P4_veu:.6f}")
print(f"  far-tail worst N at m=361: N={Tail_N}, m^2*tail={Tail_actual:.6e}")
print(f"  total allowance: {total_allow} < {budget:.3f}")

# Kappa_2 regression only; not an input to the proof.
def kappa(z):
    return math.exp(-z)*(623*z/108.0 - 6*z*z + (5.0/3.0)*z**3 - z**4/8.0)
mx = max((abs(kappa(i*(10/3)/200000)), i) for i in range(200001))
print(f"\nChecksum grid max |kappa2| on [0,10/3]: {mx[0]:.12f} at grid index {mx[1]}")

# Fail-safe gate: this script is a release check, not only a printout, so it
# must exit nonzero if any allowance or the budget is violated (or non-finite).
_fail = [f"{name}: value {val:.6f} exceeds allowance {allow}"
         for name, val, allow in pieces if not (val <= allow)]
if not all(math.isfinite(v) for _, v, _ in pieces):
    _fail.append("a computed allowance is not finite")
if not (total_allow < budget):
    _fail.append(f"total allowance {total_allow} not below budget {budget:.6f}")
if _fail:
    raise SystemExit("FAIL constants_check:\n  " + "\n  ".join(_fail))
print("constants_check OK: every piece within its allowance and the total below budget")
