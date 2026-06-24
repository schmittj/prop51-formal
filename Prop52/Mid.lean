/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Mid-range certificate kernel for the printed Proposition 5.2 coefficient

This module translates the normalized recurrences used by the printed
Proposition 5.2 interval certificate for `14 <= a <= 149`.

The definitions here are exact rational arithmetic; this module supplies the
mid-range kernel only.  `PrintedCoeffNegativityMid` itself is closed in
`Prop52.MidBridge` (`printedCoeffNegativityMid_closed`), via the one-parameter
majorant inequality

  `printedCoeff μ a <= U_a (N μ)`,

followed by a finite proof that `U_a(N)/(N c_a) < 0` throughout the rectangle.  The names below mirror the notation of the accompanying TeX note:
`X_r = B_r/(N c_r)`, `Y_r = 2^r Q_r/(M c_r)`,
`S_r = 2^r R_r/(M c_r)`, and `midUNormExact = U_a(N)/(N c_a)`.
-/

import Prop52.Statement
import Prop51.Majorant
import Mathlib.Tactic

namespace Prop52

/-! ## Normalized logarithmic coefficients -/

/-- Exact reciprocal of a binomial coefficient, as a rational number. -/
def midInvChoose (n k : Nat) : ℚ :=
  1 / ((Nat.choose n k : Nat) : ℚ)

/--
Prefix list `[d_0, ..., d_A]`, where
`c_r = 6^r (r-1)! d_r` for `r >= 1`.

The recurrence is the numerically stable form used by the C++ interval
certificate.  It avoids constructing the much larger unnormalized `c_r`
inside the executable mid-range checker.
-/
def midDList : Nat → List ℚ
  | 0 => [0]
  | 1 => [0, 5 / 36]
  | 2 => [0, 5 / 36, 5 / 36]
  | n + 3 =>
      let r := n + 3
      let l := midDList (r - 1)
      let s : ℚ := ((List.range (r - 2)).map fun j : Nat =>
        let i := j + 1
        l.getD i 0 * l.getD (r - 1 - i) 0 * midInvChoose (r - 1) i).sum
      l ++ [l.getD (r - 1) 0 + s / (r : ℚ)]

/-- The normalized logarithmic coefficient `d_r`. -/
def midD (r : Nat) : ℚ :=
  (midDList r).getD r 0

/-- `R_{k,r} = c_k c_{r-k} / c_r`, expressed through the normalized `d`'s. -/
def midR (k r : Nat) : ℚ :=
  if 1 ≤ k ∧ k < r then
    midD k * midD (r - k) / midD r /
      (((r - 1 : Nat) : ℚ) * ((Nat.choose (r - 2) (k - 1) : Nat) : ℚ))
  else
    0

/-! ## Array-backed exact tables

The list definitions above are convenient mathematical specifications.  The
certificate checker below uses arrays so that each prefix is computed once.
-/

/-- Array version of `midDList`. -/
def midDTab : Nat → Array ℚ
  | 0 => #[0]
  | 1 => #[0, 5 / 36]
  | 2 => #[0, 5 / 36, 5 / 36]
  | n + 3 =>
      let r := n + 3
      let T := midDTab (r - 1)
      let s : ℚ := ((List.range (r - 2)).map fun j : Nat =>
        let i := j + 1
        T.getD i 0 * T.getD (r - 1 - i) 0 * midInvChoose (r - 1) i).sum
      T.push (T.getD (r - 1) 0 + s / (r : ℚ))

/-- Table lookup version of `R_{k,r}`. -/
def midRTab (D : Array ℚ) (k r : Nat) : ℚ :=
  if 1 ≤ k ∧ k < r then
    D.getD k 0 * D.getD (r - k) 0 / D.getD r 0 /
      (((r - 1 : Nat) : ℚ) * ((Nat.choose (r - 2) (k - 1) : Nat) : ℚ))
  else
    0

/-! ## Exact normalized `X`, `Y`, `S` recurrences -/

/-- Prefix list for `X_r(N) = B_r(N)/(N c_r)`. -/
def midXList (N : Nat) : Nat → List ℚ
  | 0 => [0]
  | 1 => [0, -1]
  | n + 2 =>
      let r := n + 2
      let l := midXList N (r - 1)
      let s : ℚ := ((List.range (r - 1)).map fun j : Nat =>
        let k := j + 1
        (k : ℚ) * midR k r * l.getD (r - k) 0).sum
      l ++ [-1 - ((N : ℚ) / (r : ℚ)) * s]

/-- `X_r(N) = B_r(N)/(N c_r)`. -/
def midX (N r : Nat) : ℚ :=
  (midXList N r).getD r 0

/-- Array-backed prefix table for `X_r(N) = B_r(N)/(N c_r)`. -/
def midXTab (D : Array ℚ) (N : Nat) : Nat → Array ℚ
  | 0 => #[0]
  | 1 => #[0, -1]
  | n + 2 =>
      let r := n + 2
      let T := midXTab D N (r - 1)
      let s : ℚ := ((List.range (r - 1)).map fun j : Nat =>
        let k := j + 1
        (k : ℚ) * midRTab D k r * T.getD (r - k) 0).sum
      T.push (-1 - ((N : ℚ) / (r : ℚ)) * s)

/-- Prefix list for `Y_r(M) = 2^r Q_r(M)/(M c_r)`. -/
def midYList (M : Nat) : Nat → List ℚ
  | 0 => [0]
  | 1 => [0, 1]
  | n + 2 =>
      let r := n + 2
      let l := midYList M (r - 1)
      let s : ℚ := ((List.range (r - 1)).map fun j : Nat =>
        let k := j + 1
        (k : ℚ) * midR k r * l.getD (r - k) 0).sum
      l ++ [1 + ((M : ℚ) / (r : ℚ)) * s]

/-- `Y_r(M) = 2^r Q_r(M)/(M c_r)`. -/
def midY (M r : Nat) : ℚ :=
  (midYList M r).getD r 0

/-- Array-backed prefix table for `Y_r(M) = 2^r Q_r(M)/(M c_r)`. -/
def midYTab (D : Array ℚ) (M : Nat) : Nat → Array ℚ
  | 0 => #[0]
  | 1 => #[0, 1]
  | n + 2 =>
      let r := n + 2
      let T := midYTab D M (r - 1)
      let s : ℚ := ((List.range (r - 1)).map fun j : Nat =>
        let k := j + 1
        (k : ℚ) * midRTab D k r * T.getD (r - k) 0).sum
      T.push (1 + ((M : ℚ) / (r : ℚ)) * s)

/-- `S_r(M) = 2^r R_r(M)/(M c_r)`. -/
def midS (M r : Nat) : ℚ :=
  match r with
  | 0 => 0
  | 1 => 7 / 5
  | n + 2 =>
      let r := n + 2
      2 * ((M : ℚ) + 6 * (r : ℚ) - 6) *
          (midD (r - 1) / midD r / (6 * ((r - 1 : Nat) : ℚ))) *
          midY M (r - 1) -
        midY M r

/-- Table-backed version of `S_r(M) = 2^r R_r(M)/(M c_r)`. -/
def midSTab (D Y : Array ℚ) (M r : Nat) : ℚ :=
  match r with
  | 0 => 0
  | 1 => 7 / 5
  | n + 2 =>
      let r := n + 2
      2 * ((M : ℚ) + 6 * (r : ℚ) - 6) *
          (D.getD (r - 1) 0 / D.getD r 0 / (6 * ((r - 1 : Nat) : ℚ))) *
          Y.getD (r - 1) 0 -
        Y.getD r 0

/-! ## The one-parameter upper bound checker -/

/-- `max(-x, 0)` over `ℚ`. -/
def midNegPart (x : ℚ) : ℚ :=
  if x < 0 then -x else 0

/-- Exact normalized upper bound `U_a(N)/(N c_a)` from the printed proof. -/
def midUNormExact (a N : Nat) : ℚ :=
  let m := M a
  midX N a +
    (m : ℚ) * ((List.range (a - 1)).map fun j : Nat =>
      let k := j + 1
      midR k a * (1 / (2 : ℚ) ^ (a - k)) *
        midNegPart (midX N k) * midS m (a - k)).sum

/-- Array-backed exact normalized upper bound `U_a(N)/(N c_a)`. -/
def midUNormWithTabs (D Y : Array ℚ) (a N : Nat) : ℚ :=
  let m := M a
  let X := midXTab D N a
  X.getD a 0 +
    (m : ℚ) * ((List.range (a - 1)).map fun j : Nat =>
      let k := j + 1
      midRTab D k a * (1 / (2 : ℚ) ^ (a - k)) *
        midNegPart (X.getD k 0) * midSTab D Y m (a - k)).sum

/-- Array-backed exact normalized upper bound `U_a(N)/(N c_a)`. -/
def midUNormFast (a N : Nat) : ℚ :=
  let m := M a
  let D := midDTab a
  let Y := midYTab D m a
  midUNormWithTabs D Y a N

/--
Exact Boolean check for one row of the mid-range rectangle:
`M(a)+1 <= N <= 2M(a)`.
-/
def checkPrintedMidRowExact (a : Nat) : Bool :=
  let m := M a
  (List.range m).all fun i : Nat =>
    let N := m + 1 + i
    decide (midUNormExact a N < 0)

/--
Fast exact Boolean check for one row of the mid-range rectangle:
`M(a)+1 <= N <= 2M(a)`.
-/
def checkPrintedMidRowFast (a : Nat) : Bool :=
  let m := M a
  let D := midDTab a
  let Y := midYTab D m a
  (List.range m).all fun i : Nat =>
    let N := m + 1 + i
    decide (midUNormWithTabs D Y a N < 0)

/-- Exact Boolean check for consecutive `a`-rows. -/
def checkPrintedMidRowsExact (lo len : Nat) : Bool :=
  (List.range len).all fun i : Nat =>
    checkPrintedMidRowExact (lo + i)

/-- Fast exact Boolean check for consecutive `a`-rows. -/
def checkPrintedMidRowsFast (lo len : Nat) : Bool :=
  (List.range len).all fun i : Nat =>
    checkPrintedMidRowFast (lo + i)

theorem checkPrintedMidRowFast_14 :
    checkPrintedMidRowFast 14 = true := by
  native_decide

end Prop52
