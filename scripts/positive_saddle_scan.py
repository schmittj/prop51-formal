#!/usr/bin/env python3
"""Positive-part saddle majorant scan (corrected from the tenth revision).

Evaluates the explicit summand majorants of Lemma 6.1 (paper eqs.
(small-majorant)/(tempered-majorant)) over the critical window
401 <= a <= 2000.

Correction vs. prop51_tenth_positive_saddle_certificate.py: that script
scanned only N = 12a-8, asserting monotonicity in N.  The small-regime
majorant is increasing in N, but the *tempered* majorant scales as 96/N and
is decreasing in N, and the regime cutoff k_dagger = ceil(sqrt(N)) moves with
N.  Sound fix used here: for each (a, k), take the maximum of
  * the small-regime formula at its worst edge N = 12a-8 (increasing in N),
    applied whenever k could be in the small regime for some N in the
    rectangle, i.e. k <= ceil(sqrt(12a-8)); and
  * the tempered formula at its worst edge N = 6a-7 (decreasing in N),
    applied whenever k could be tempered for some N, i.e. k > ceil(sqrt(6a-7)).
The result upper-bounds the majorant for every N in [6a-7, 12a-8].
Empirically this costs less than a factor 2.5 vs. the single-edge scan and
remains ~1e-16 at worst, against the 1e-8 target of Lemma 6.1.

Usage: python3 positive_saddle_scan.py [--quick]   (--quick: a <= 600)
"""
import math
import sys

A_LO, A_HI = 401, 600 if "--quick" in sys.argv else 2000
LOG2 = math.log(2.0)


def logcomb(n, r):
    if r < 0 or r > n:
        return float("inf")
    return math.lgamma(n + 1) - math.lgamma(r + 1) - math.lgamma(n - r + 1)


def logaddexp(x, y):
    if x == -math.inf:
        return y
    if y == -math.inf:
        return x
    if x < y:
        x, y = y, x
    return x + math.log1p(math.exp(y - x))


def log_small(a, N, k):
    j = a - k
    return (math.log(65.0 / N) + math.log(k * j / (a - 1.0))
            - logcomb(a - 2, k - 1)
            + 1.139 * math.sqrt(N) + 0.2 * j + 2.9 * a / j + 1.0
            - (a - k) * LOG2)


def log_tempered(a, N, k):
    j = a - k
    return (math.log(96.0 / N) + math.log(k * j / (a - 1.0))
            - logcomb(a - 2, k - 1)
            + 0.2 * a + 5.7 * a / k + 2.9 * a / j + 2.0
            - (a - k) * LOG2)


def majorant_for_a(a):
    Nhi, Nlo = 12 * a - 8, 6 * a - 7
    kd_hi = math.ceil(math.sqrt(Nhi))   # largest possible small-regime cutoff
    kd_lo = math.ceil(math.sqrt(Nlo))   # smallest possible cutoff
    kmax = math.floor(0.9 * a)
    logsum, worst = -math.inf, None
    for k in range(1, kmax + 1):
        v = -math.inf
        if k <= kd_hi:                  # small regime possible for some N
            v = max(v, log_small(a, Nhi, k))
        if k > kd_lo:                   # tempered regime possible for some N
            v = max(v, log_tempered(a, Nlo, k))
        logsum = logaddexp(logsum, v)
        if worst is None or v > worst[1]:
            worst = (k, v)
    return logaddexp(logsum, -0.49 * a), worst


best = None
for a in range(A_LO, A_HI + 1):
    logtotal, worst = majorant_for_a(a)
    if best is None or logtotal > best[1]:
        best = (a, logtotal, worst)

target = math.log(1e-8)
print(f"scanned a={A_LO}..{A_HI}, both N edges per regime")
print(f"worst summed majorant: a={best[0]}, log={best[1]:.6f}, "
      f"value={math.exp(best[1]):.6e}  (target log {target:.2f})")
print(f"worst summand: k={best[2][0]}, logterm={best[2][1]:.6f}")
assert best[1] < target, "positive-part majorant exceeds 1e-8 target!"
print("PASS: positive part below 1e-8 throughout the window.")
