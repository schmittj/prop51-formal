Please relay the following to the Codex worker.

## Critical correction: retire the exact-upper-edge product constructor

I need to correct one recommendation from my previous note. Do **not** pursue

```lean
LargeTailProductCertificate
  .ofClosedExactUpperEdgeProductGeFourNatSignLockComplement
```

The required `hsmallGeFour` is not merely expensive: it is false for the hard-coded exact split-factorial product.

At the first required cell
[
a=3000,\qquad k=4,\qquad j=2996,
]
write
[
M=12a-8=35992,\qquad L=6a-7=17993.
]

The exact split bounds contain the positive subterms
[
X_{\rm exact}\ge \frac{(Mc_1)^4}{4!}
]
and, from the (s=0,r=1) term of the (Y)-sum,
[
Y_{\rm exact}\ge \frac M{50},6^j(j-1)!.
]

Using
[
c_j\le\frac4{25}6^j(j-1)!,\qquad c_1=\frac56,\qquad c_4=1130,
]
the claimed small scalar inequality would force
[
R:=
\frac{
2,2^j M,(Mc_1)^4/4!,(M/50)
}{
130\cdot4j\cdot Lc_4(4/25),
\operatorname{PE}(E,3000)
}
\le1,
]
where
[
E=\texttt{positiveSmallExponentUpper 3000 4}
=819.513871829\ldots.
]

Direct evaluation gives
[
\log_{10}R=557.513027\ldots,
\qquad
R\approx3.26\times10^{557}.
]

The obstruction is structural: the coarse split (Y)-bound has lost the dyadic gain and contains a (6^j(j-1)!) term. The outside normalization then contributes an uncancelled (2^j), which cannot fit under an (e^{0.2j+O(\sqrt a)}) target.

Therefore:

* no endpoint monotonicity proof can establish `hsmallGeFour`;
* no `xyBound` dominating that exact split product can satisfy the desired scalar inequality;
* the current exact-upper-edge constructor should be treated as a legacy dead end.

A sharper split (Y)-surrogate retaining (3^j) could possibly repair that architecture, but constructing it is less direct than bounding the actual coefficients.

The replacement route should be:

```lean
PositiveSaddleLargeTailProductPrefixPointwise.ofRawCleared
LargeTailProductCertificate.ofRawCleared
```

using the actual `Bq * Qq` raw predicates.

---

# Recommended direct saddle route

The same two analytic lemmas can solve:

1. the finite product fields for (401\le a\le2000);
2. the prefix product fields for (2001\le a<3000);
3. the entire large-tail product certificate for (a\ge3000).

No exact coefficient grid should be needed.

The provisional (12/5) radius idea can be improved: use

[
\boxed{\beta=\frac{34}{15}}.
]

This is particularly convenient because
[
\frac{68/25}{34/15}=\frac65,
]
so the existing rational factorial bound interacts with it exactly.

## 1. Generic finite-exponential toolkit

Add a small file such as `Prop51/SaddleDirect.lean`. Define an inclusive finite exponential prefix

```lean
def expPrefix (x : ℚ) (m : Nat) : ℚ :=
  ∑ r ∈ Finset.range (m + 1), x^r / (r.factorial : ℚ)
```

The useful generic lemmas are:

```lean
theorem expCoeff_scale ...
theorem coeff_pow_le_gas_pow ...
theorem expCoeff_saddle ...
theorem expPrefix_mul_le ...
theorem one_add_pow_le_expPrefix ...
theorem monomial_le_expPrefix ...
```

### Scaling

Prove by strong induction from `expCoeff_succ_mul`:

[
\operatorname{expCoeff}(r\mapsto \rho^rL_r,m)
=\rho^m\operatorname{expCoeff}(L,m).
]

The inductive summand uses
[
\rho^{t+1}\rho^{m-t}=\rho^{m+1}.
]

### Coefficient of a power bounded by the total gas

For (M_r\ge0), (p\le m), prove

[
[t^p]\left(\sum_rM_rt^r\right)^q
\le
\left(\sum_{r=0}^mM_r\right)^q.
]

Induct on (q). At the successor step, use `coeff_mul` and

[
\sum_{r=0}^pM_r,[t^{p-r}]G^q
\le
\sum_{r=0}^mM_r,G_m^q
=G_m^{q+1}.
]

This avoids enumerating compositions.

Together with the existing `expCoeff_eq_sum_pow`, this gives the generic saddle lemma

[
\rho^m\operatorname{expCoeff}(L,m)
\le
P_m!\left(\sum_{r=1}^m L_r\rho^r\right),
]
where (P_m=\texttt{expPrefix}).

### Prefix convolution

Prove once:

[
P_m(x)P_n(y)\le P_{m+n}(x+y)
\qquad(x,y\ge0).
]

Expand the product, enlarge the rectangle of pairs ((p,q)) to the triangle
(p+q\le m+n), regroup by (t=p+q), and use

[
\frac{x^py^q}{p!,q!}
====================

\binom{p+q}{p}\frac{x^py^q}{(p+q)!}
]
together with `add_pow`.

The project already uses
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`. Mathlib’s ordered-finset API also supplies `Finset.sum_le_sum`, `sum_le_sum_of_subset_of_nonneg`, and `single_le_sum`, so these enlargements can remain symbolic rather than executable. ([Lean Community][1])

### Absorbing elementary factors

Prove

[
(1+d)^n\le P_n(nd),\qquad d\ge0.
]

Use exactly the binomial argument already used in `one_add_inv_pow_le`:

[
\binom nr r!\le n^r.
]

Also record

[
\frac{x^m}{m!}\le P_m(x).
]

Do not turn anything into `partialExpUpper` until the last line. This avoids multiplying two `partialExpUpper` expressions.

---

# 2. One uniform factorial-gas lemma

Define

[
u_{n,r}:=
\left(\frac{34}{15}\right)^r\frac{(r-1)!}{n^r}.
]

The needed estimate is

[
\boxed{
n\ge40
\quad\Longrightarrow\quad
\sum_{r=2}^n u_{n,r}\le\frac1n.
}
]

The term ratio is rational:

[
\frac{u_{n,r+1}}{u_{n,r}}
=\frac{34r}{15n},
\qquad
\frac{u_{n,r}}{u_{n,r+1}}
=\frac{15n}{34r}.
]

Thus the sequence decreases and then increases, with the switch near
(15n/34).

A Lean-friendly proof is to split into:

[
{2,3},\qquad
{4,\ldots,n-10},\qquad
{n-9,\ldots,n}.
]

## Endpoint control

Let

[
U_n:=n,u_{n,n}
=\left(\frac{34}{15}\right)^n\frac{n!}{n^n}.
]

Then

[
\frac{U_{n+1}}{U_n}
===================

\frac{34/15}{(1+1/n)^n}.
]

For (n\ge3), existing monotonicity of ((1+1/n)^n) gives

[
(1+1/n)^n\ge(4/3)^3=\frac{64}{27},
]
hence
[
\frac{U_{n+1}}{U_n}\le\frac{153}{160}<1.
]

The only fixed check needed is

[
U_{30}<\frac1{16}.
]

That should be a small `norm_num [U, Nat.factorial]` check. Consequently
(U_n\le1/16) for (n\ge30).

For the factor (nU_n), let (W_n=nU_n). For (n\ge40),

[
\frac{W_{n+1}}{W_n}
\le
\frac{41}{40}\frac{153}{160}
============================

\frac{6273}{6400}<1.
]

Thus
[
W_n\le W_{40}\le\frac{40}{16}=\frac52.
]

## Low terms

For (n\ge40),

[
n(u_{n,2}+u_{n,3})
==================

\frac{\beta^2}{n}+\frac{2\beta^3}{n^2}
\le\frac16.
]

It suffices to check the right side at (n=40).

## High block

For (r\ge n-9),

[
\frac{u_{n,r}}{u_{n,r+1}}\le\frac35.
]

Therefore

[
n\sum_{r=n-9}^n u_{n,r}
\le
\frac52U_n
\le\frac5{32}
\le\frac15.
]

## Middle block

By unimodality, every (4\le r\le n-10) satisfies

[
u_{n,r}\le u_{n,4}+u_{n,n-10}.
]

There are at most (n) terms, so

[
n\sum_{r=4}^{n-10}u_{n,r}
\le n^2u_{n,4}+n^2u_{n,n-10}.
]

The left endpoint satisfies

[
n^2u_{n,4}
=\frac{6\beta^4}{n^2}
\le\frac18.
]

For the right endpoint, ten backwards ratio steps give

[
u_{n,n-10}\le\left(\frac35\right)^{10}u_{n,n}.
]

Hence

[
n^2u_{n,n-10}
\le
\left(\frac35\right)^{10}W_n
\le
\left(\frac35\right)^{10}\frac52
<\frac1{50}.
]

Combining the blocks,

[
n\sum_{r=2}^nu_{n,r}
\le
\frac16+\frac18+\frac1{50}+\frac15
==================================

\frac{307}{600}<1.
]

All variable-length sums remain symbolic. Only the small endpoint checks are evaluated.

---

# 3. Small-radius gas lemma

For the small branch, put

[
s=\lceil\sqrt N\rceil,\qquad \rho_X=\frac1{6s}.
]

Define

[
v_{s,r}:=\frac{(r-1)!}{s^r}.
]

For (4\le r<k\le s),

[
\frac{v_{s,r+1}}{v_{s,r}}=\frac rs\le1.
]

Therefore, for (s\ge32),

[
\begin{aligned}
\sum_{r=2}^k v_{s,r}
&\le
\frac1{s^2}+\frac2{s^3}
+s\frac6{s^4}\
&=
\frac1{s^2}+\frac8{s^3}\
&\le
\frac5{4s^2}.
\end{aligned}
]

In the intended range (a\ge401), the rectangle gives (N\ge2399), hence (s\ge49).

---

# 4. The three specialized coefficient estimates

Use the generic saddle lemma with these radii.

Let (j=a-k).

## Small (B^+)

With
[
\rho_X=\frac1{6s},
\qquad s=\lceil\sqrt N\rceil,
]
the weighted gas is bounded by

[
\begin{aligned}
G_X
&\le
Nc_1\rho_X
+
\frac{4N}{25}
\sum_{r=2}^k\frac{(r-1)!}{s^r}\
&\le
\frac{5N}{36s}+\frac{N}{5s^2}\
&\le
\frac{5s}{36}+\frac15.
\end{aligned}
]

Thus

[
B^+_k(N)
\le
(6s)^k
P_k!\left(\frac{5s}{36}+\frac15\right).
]

## Tempered (B^+)

Take

[
\rho_X=\frac{17}{45k}
=\frac{\beta}{6k}.
]

The weighted gas is

[
G_X
\le
\frac{17N}{54k}+\frac{4N}{25k}.
]

Hence

[
B^+_k(N)
\le
\left(\frac{45k}{17}\right)^k
P_k!\left(
\frac{17N}{54k}+\frac{4N}{25k}
\right).
]

## (Q_j)

Take

[
\rho_Y=\frac{34}{45j}
=\frac{\beta}{3j}.
]

Then

[
G_Y
\le
\frac{17N}{108j}+\frac{2N}{25j},
]
and

[
Q_j(N)
\le
\left(\frac{45j}{34}\right)^j
P_j!\left(
\frac{17N}{108j}+\frac{2N}{25j}
\right).
]

The hypotheses (n\ge40) needed for the common gas lemma are automatic:

* (j\ge41), using the existing
  `self_le_ten_mul_posJ_of_le_posKmax`;
* in the tempered branch, (k\ge50);
* in the small branch, only the (s\ge32) lemma is needed for (B^+).

---

# 5. Normalize with the existing factorial bound

From `c_lb`,

[
c_n\ge\frac5{36}6^n(n-1)!.
]

For the small (B)-factor,

[
\frac{(6s)^k}{c_k}
\le
\frac{36}{5},
k,\frac{s^k}{k!}.
]

For the tempered (B)-factor, `factorial_lb` and

[
\frac{15}{34}
=============

\frac65\frac{25}{68}
]
give

[
\frac{(45k/17)^k}{c_k}
\le
\frac{36}{5},k\left(\frac65\right)^k.
]

For (Q), including the normalized factor (2,2^j),

[
\frac{2,2^j(45j/34)^j}{c_j}
\le
\frac{72}{5},j\left(\frac65\right)^j.
]

Thus the common constant is

[
\boxed{
C_0=\frac{36}{5}\frac{72}{5}
=\frac{2592}{25}
=103.68.
}
]

---

# 6. Core small and tempered product bounds

Use `Bq_le_Bplusq` and `Qq_nonneg`. Therefore the assumption
`0 < Bq N k` is unnecessary in the analytic proof and can simply be ignored.

Because (N\le12a),

[
\frac{17N}{54k}+\frac{4N}{25k}
\le
\frac{1282}{225}\frac ak
<
\frac{57}{10}\frac ak,
]
and

[
\frac{17N}{108j}+\frac{2N}{25j}
\le
\frac{641}{225}\frac aj
<
\frac{29}{10}\frac aj.
]

## Small core inequality

Absorb

[
\frac{s^k}{k!}\le P_k(s)
]
and
[
\left(\frac65\right)^j
======================

\left(1+\frac15\right)^j
\le P_j(j/5).
]

Repeated prefix convolution then gives

[
\boxed{
2,2^j B_q(N,k)Q_q(N,j)
\le
C_0,kj,c_kc_j,
P_{2a}!\left(
\frac{41}{36}s+\frac j5+
\frac{29}{10}\frac aj+\frac15
\right).
}
]

## Tempered core inequality

Here

[
\left(\frac65\right)^{k+j}
==========================

\left(\frac65\right)^a
\le P_a(a/5).
]

Hence

[
\boxed{
2,2^j B_q(N,k)Q_q(N,j)
\le
C_0,kj,c_kc_j,
P_{2a}!\left(
\frac a5+
\frac{57}{10}\frac ak+
\frac{29}{10}\frac aj
\right).
}
]

These are the two reusable analytic theorems. Everything else should be a short wrapper.

---

# 7. Finite small branch: bypass the tangent route

The direct upper-edge target is easier than the tangent target.

Let
[
M=12a-8,\qquad s_{\rm hi}=\lceil\sqrt M\rceil.
]

The direct raw-cleared target equivalent to
`positiveSmallXYProductBound` is

[
2,2^j M B_qQ_q
\le
\frac{2581}{20},
kj,N,c_kc_j,
\operatorname{PE}(E_s,800),
]
where

[
E_s=
\frac{1139}{1000}s_{\rm hi}
+\frac j5+\frac{29}{10}\frac aj+1.
]

The edge constants satisfy

[
\frac{2592}{25}M
\le
\frac53\frac{2581}{20}N.
]

At the lower edge this reduces to

[
31104(12a-8)\le64525(6a-7),
]
or
[
202843\le13902a,
]
so it is automatic for (a\ge401).

Absorb the factor (5/3) as

[
\frac53=P_1(2/3).
]

The total prefix argument becomes

[
\frac{41}{36}s+\frac j5+
\frac{29}{10}\frac aj+\frac15+\frac23.
]

Now

[
\frac{1139}{1000}-\frac{41}{36}
=\frac1{9000},
\qquad
1-\left(\frac15+\frac23\right)=\frac2{15},
]
and (s\le s_{\rm hi}). Therefore this argument is at most (E_s).

Finally:

1. use argument monotonicity of `expPrefix`;
2. invoke `sum_exp_le E_s 800 ...`.

There is no need to prove monotonicity of `partialExpUpper` itself, and no tangent-edge table is required.

The fact that the symbolic prefix may have (2a+2) terms is harmless: in `sum_exp_le`, the final `T` is arbitrary. The condition is only (E_s<800), already proved in the project.

This directly proves the requested

```lean
Xnorm N k * Ynorm N (posJ a k)
  ≤ positiveSmallXYProductBound a N k
```

for the bounded constructor.

---

# 8. Finite tempered branch

The core constant already fits:

[
\frac{2592}{25}
<
\frac{2117}{20},
]
with exact slack (217/100).

The core prefix argument

[
\frac a5+
\frac{57}{10}\frac ak+
\frac{29}{10}\frac aj
]
is at most

[
\texttt{positiveTemperedExponentUpper a k}
]
because the latter has an additional (+2).

Use argument monotonicity followed by

```lean
sum_exp_le
  (positiveTemperedExponentUpper a k)
  positiveExpCutoff
  ...
```

This proves

```lean
Xnorm N k * Ynorm N (posJ a k)
  ≤ positiveTemperedXYProductBound a N k
```

again without using `hB`.

---

# 9. Prefix and large tail

Use the same core inequalities.

## Small raw large target

Multiply the small core by (M=12a-8). Use

[
\frac{2592}{25}M
\le
\frac53\cdot130,N.
]

Absorb (5/3) exactly as in the finite small branch. Then invoke
`sum_exp_le` with cutoff (a), using the existing theorem

```lean
positiveSmallExponentUpper_lt_largeExpCutoff
```

This yields

```lean
positiveSmallLargeXYProductRawCleared a N k
```

for every (a>2000).

## Tempered raw large target

Multiply the tempered core by (L=6a-7). Since (L\le N) and

[
\frac{2592}{25}<192,
]
the constant comparison is immediate.

Use the existing exponent cutoff (8a) to obtain

```lean
positiveTemperedLargeXYProductRawCleared a N k
```

for every (a>2000).

These same two theorems supply both the bounded prefix and the infinite tail:

```lean
def productPrefix :
    PositiveSaddleLargeTailProductPrefixPointwise :=
  PositiveSaddleLargeTailProductPrefixPointwise.ofRawCleared
    smallLargeRaw_analytic
    temperedLargeRaw_analytic

def hproduct : LargeTailProductCertificate :=
  LargeTailProductCertificate.ofRawCleared
    smallLargeRaw_analytic
    temperedLargeRaw_analytic
```

Then the bounded certificate should be assembled with

```lean
BoundedPositiveCertificate
  .ofCombinedProductScaledEdgeMajorantDirectPrefix
```

using:

* `finiteSmallXY_analytic`;
* `finiteTemperedXY_analytic`;
* the existing finite solo proof;
* `productPrefix`;
* the existing solo-prefix proof.

---

# Recommended implementation order

1. Add a brief regression note or cheap lower-bound check showing that the exact-upper-edge (a=3000,k=4) target is false.
2. Stop generating exact raw-product grid shards.
3. Implement `expPrefix`, scaling, gas-power, saddle, and convolution lemmas.
4. Prove `temperedFactorialGas_le_inv`.
5. Prove `smallFactorialGas_le`.
6. Prove the two reusable core product inequalities.
7. Add four thin wrappers:

   * finite small;
   * finite tempered;
   * large/prefix small raw;
   * large/prefix tempered raw.
8. Assemble `productPrefix`, `hproduct`, and then `hbounded`.

The only part likely to require nontrivial Lean bookkeeping is the one-time prefix-convolution reindexing. The analytic inequalities themselves reduce to `field_simp`, `ring`, `positivity`, `omega`, and small fixed `norm_num` checks. No proof should unfold a sum with a number of terms proportional to (a).

The mathematical constants above have been checked, including the (a=3000,k=4) obstruction. I have not kernel-checked the proposed Lean skeleton, so minor API-name or rewriting adjustments may be necessary.

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/BigOperators/Group/Finset.html "Mathlib.Algebra.Order.BigOperators.Group.Finset"
