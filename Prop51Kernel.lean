/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# The executable interval-certificate kernel (Layer B)

All *executable* code of the Layer B certificate: dyadic floats/intervals
and the interval port of the `c`/`B`/`Q` recurrences of `Prop51/Defs.lean`,
culminating in `Prop51.checkRange`.

This module deliberately imports **nothing beyond the Lean core prelude** —
no Mathlib — so that the library can be natively precompiled
(`precompileModules` in `lakefile.toml`).  The `native_decide` certificates
(`Prop51/CertificateInterval*.lean`) then evaluate `checkRange` as compiled
native code rather than through the IR interpreter (~10× faster).

Everything here is *definitions only*.  The soundness theory lives in the
main library, stated over `ℚ`:

* `Prop51/Dyadic.lean`       — enclosure semantics of `DF`/`DI` and every
                                operation (`DI.mem_add`, `DI.mem_mul`, …);
* `Prop51/IntervalCert.lean` — the tables enclose the exact rational
                                sequences, and `checkRange lo len = true`
                                implies `Unorm a N < 0` on the covered
                                rectangle.

Design notes (details in `Prop51/Dyadic.lean`):

* a `DF` `(m, e)` denotes the rational `m · 2^e`; a `DI` is a pair of
  endpoint `DF`s, lower endpoints rounding toward `-∞`, upper toward `+∞`;
* mantissas are capped at `PREC = 192` bits — the working precision of the
  reference Arb run (`certificates/prop51_A400_certificate_package.zip`);
* only extern-fast primitives appear on the hot path: `Nat.shiftLeft`,
  `Nat.shiftRight`, `Nat.log2`, `Int.fdiv` and `Int` ring operations.
-/

namespace Prop51

/-- Working precision in bits (mirrors the 192-bit Arb reference run). -/
def PREC : Nat := 192

/-! ## Integer shifts -/

/-- `m · 2^k` by extern-fast natural shifts. -/
def shl (m : Int) (k : Nat) : Int :=
  match m with
  | .ofNat n => .ofNat (n <<< k)
  | .negSucc n => .negSucc ((n+1) <<< k - 1)

/-- `⌊m / 2^k⌋` (floor, toward `-∞`) by extern-fast natural shifts. -/
def floorShr (m : Int) (k : Nat) : Int :=
  match m with
  | .ofNat n => .ofNat (n >>> k)
  | .negSucc n => .negSucc (n >>> k)

/-- `⌈m / 2^k⌉` (ceiling, toward `+∞`). -/
def ceilShr (m : Int) (k : Nat) : Int := -(floorShr (-m) k)

/-! ## Dyadic floats -/

/-- A dyadic float: the rational number `m · 2^e`. -/
structure DF where
  m : Int
  e : Int

namespace DF

/-- Round down (toward `-∞`) to a `PREC`-bit mantissa. -/
def rdn (f : DF) : DF :=
  let s := f.m.natAbs.log2
  if s < PREC then f
  else ⟨floorShr f.m (s + 1 - PREC), f.e + ((s + 1 - PREC : Nat) : Int)⟩

/-- Round up (toward `+∞`) to a `PREC`-bit mantissa. -/
def rup (f : DF) : DF :=
  let s := f.m.natAbs.log2
  if s < PREC then f
  else ⟨ceilShr f.m (s + 1 - PREC), f.e + ((s + 1 - PREC : Nat) : Int)⟩

/-- Exact negation. -/
def neg (f : DF) : DF := ⟨-f.m, f.e⟩

/-- Exact addition (align to the smaller exponent). -/
def addE (a b : DF) : DF :=
  let e := min a.e b.e
  ⟨shl a.m (a.e - e).toNat + shl b.m (b.e - e).toNat, e⟩

/-- Exact multiplication. -/
def mulE (a b : DF) : DF := ⟨a.m * b.m, a.e + b.e⟩

end DF

/-! ## Dyadic intervals -/

/-- A dyadic interval `[lo, hi]`; the enclosure semantics (`DI.mem`) and all
soundness lemmas live in `Prop51/Dyadic.lean`. -/
structure DI where
  lo : DF
  hi : DF

/-- Enclosure of four dyadic floats: align all mantissas to the common
minimal exponent (exact), take mantissa `min`/`max`, round outward.  Used
for interval multiplication (the four corner products). -/
def hull4 (p1 p2 p3 p4 : DF) : DI :=
  let e := min (min p1.e p2.e) (min p3.e p4.e)
  let m1 := shl p1.m (p1.e - e).toNat
  let m2 := shl p2.m (p2.e - e).toNat
  let m3 := shl p3.m (p3.e - e).toNat
  let m4 := shl p4.m (p4.e - e).toNat
  ⟨DF.rdn ⟨min (min m1 m2) (min m3 m4), e⟩,
   DF.rup ⟨max (max m1 m2) (max m3 m4), e⟩⟩

namespace DI

/-- The exact interval `[0, 0]`. -/
def zero : DI := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩

/-- The exact interval `[1, 1]`. -/
def one : DI := ⟨⟨1, 0⟩, ⟨1, 0⟩⟩

/-- The exact singleton interval `[n, n]` for a natural `n`. -/
def exact (n : Nat) : DI := ⟨⟨(n : Int), 0⟩, ⟨(n : Int), 0⟩⟩

/-- Outward-rounded addition. -/
def add (I J : DI) : DI := ⟨DF.rdn (I.lo.addE J.lo), DF.rup (I.hi.addE J.hi)⟩

/-- Exact negation. -/
def neg (I : DI) : DI := ⟨I.hi.neg, I.lo.neg⟩

/-- Outward-rounded scaling by a natural number. -/
def nsmul (n : Nat) (I : DI) : DI :=
  ⟨DF.rdn ⟨(n : Int) * I.lo.m, I.lo.e⟩, DF.rup ⟨(n : Int) * I.hi.m, I.hi.e⟩⟩

/-- Exact division by `2^k` (an exponent shift). -/
def shr (k : Nat) (I : DI) : DI :=
  ⟨⟨I.lo.m, I.lo.e - (k : Int)⟩, ⟨I.hi.m, I.hi.e - (k : Int)⟩⟩

/-- Outward-rounded division by a positive natural number. -/
def divNat (I : DI) (n : Nat) : DI :=
  ⟨DF.rdn ⟨(shl I.lo.m PREC).fdiv (n : Int), I.lo.e - (PREC : Int)⟩,
   DF.rup ⟨-((-(shl I.hi.m PREC)).fdiv (n : Int)), I.hi.e - (PREC : Int)⟩⟩

/-- Outward-rounded multiplication via the four corner products. -/
def mul (I J : DI) : DI :=
  hull4 (I.lo.mulE J.lo) (I.lo.mulE J.hi) (I.hi.mulE J.lo) (I.hi.mulE J.hi)

/-- The convex hull of `I` and `{0}`: encloses both every member of `I`
and the number `0`.  Used for the conditionally-included positive-part
terms of the majorant (conservative sign handling — no interval sign
decision is ever needed). -/
def hull0 (I : DI) : DI :=
  ⟨if I.lo.m < 0 then I.lo else ⟨0, 0⟩,
   if 0 < I.hi.m then I.hi else ⟨0, 0⟩⟩

end DI

/-! ## Interval tables for the `c`/`B`/`Q` recurrences

These mirror, step by step, the exact rational recurrences of
`Prop51/Defs.lean` (`cList`, `expList` for `BListQ`/`QListQ`); the
correspondence is proved in `Prop51/IntervalCert.lean`. -/

/-- Convolution for the Riccati step:
`convC T m j` encloses `Σ_{i<j} i·(m-i)·c_i·c_{m-i}` when `T` encloses `c`. -/
def convC (T : Array DI) (m : Nat) : Nat → DI
  | 0 => DI.zero
  | (i+1) => (convC T m i).add
      (DI.nsmul (i * (m - i)) ((T.getD i DI.zero).mul (T.getD (m-i) DI.zero)))

/-- Interval enclosure of `[c_0, …, c_A]` (cf. `cList`). -/
def cTab : Nat → Array DI
  | 0 => #[DI.zero]
  | 1 => #[DI.zero, (DI.exact 5).divNat 6]
  | (n+2) =>
      let T := cTab (n+1)
      T.push ((DI.nsmul (6*(n+1)) (T.getD (n+1) DI.zero)).add
        ((DI.nsmul 6 (convC T (n+1) (n+1))).divNat (n+2)))

/-- Convolution for the `B`-recurrence step:
`convB cT T N n j` encloses `Σ_{t<j} (t+1)·(-N·c_{t+1})·Bq N (n-t)`. -/
def convB (cT T : Array DI) (N n : Nat) : Nat → DI
  | 0 => DI.zero
  | (t+1) => (convB cT T N n t).add
      ((DI.nsmul ((t+1) * N)
        ((cT.getD (t+1) DI.zero).mul (T.getD (n-t) DI.zero))).neg)

/-- Interval enclosure of `[B_0, …, B_n]`, `B_k = [X^k] C(X)^{-N}`. -/
def bTab (cT : Array DI) (N : Nat) : Nat → Array DI
  | 0 => #[DI.one]
  | (n+1) =>
      let T := bTab cT N n
      T.push ((convB cT T N n (n+1)).divNat (n+1))

/-- Convolution for the `Q`-recurrence step:
`convQ cT T N n j` encloses `Σ_{t<j} (t+1)·((N/2)·c_{t+1}/2^(t+1))·Qq N (n-t)`. -/
def convQ (cT T : Array DI) (N n : Nat) : Nat → DI
  | 0 => DI.zero
  | (t+1) => (convQ cT T N n t).add
      (DI.shr (t+2) (DI.nsmul ((t+1) * N)
        ((cT.getD (t+1) DI.zero).mul (T.getD (n-t) DI.zero))))

/-- Interval enclosure of `[Q_0, …, Q_n]`, `Q_j = [X^j] C(X/2)^{N/2}`. -/
def qTab (cT : Array DI) (N : Nat) : Nat → Array DI
  | 0 => #[DI.one]
  | (n+1) =>
      let T := qTab cT N n
      T.push ((convQ cT T N n (n+1)).divNat (n+1))

/-! ## The checker -/

/-- Enclosure of the positive-part sum
`Σ_{k<j} ite (1 ≤ k ∧ 0 < B_k) (B_k·Q_{a-k}) 0` via `hull0`. -/
def uTerms (B Q : Array DI) (a : Nat) : Nat → DI
  | 0 => DI.zero
  | (j+1) => (uTerms B Q a j).add
      (if j = 0 then DI.zero
       else DI.hull0 ((B.getD j DI.zero).mul (Q.getD (a-j) DI.zero)))

/-- Check a single pair `(a, N)` against shared tables: certified
`B_a + Q_a + Σ_{1≤k<a, B_k>0} B_k Q_{a-k} < 0` (numerator of `Unorm`). -/
def checkPair (B Q : Array DI) (a : Nat) : Bool :=
  decide ((((B.getD a DI.zero).add (Q.getD a DI.zero)).add
    (uTerms B Q a a)).hi.m < 0)

/-- Check every admissible `a` for one `N`, sharing the `B`/`Q` tables. -/
def checkColumn (cT : Array DI) (N : Nat) : Bool :=
  let rmax := min 400 ((N+7)/6)
  let B := bTab cT N rmax
  let Q := qTab cT N rmax
  let alo := max 61 ((N+19)/12)
  (List.range' alo (rmax + 1 - alo)).all fun a => checkPair B Q a

/-- Check all columns `N ∈ [lo, lo+len)`. -/
def checkRange (lo len : Nat) : Bool :=
  let cT := cTab 400
  (List.range' lo len).all fun N => checkColumn cT N

end Prop51
