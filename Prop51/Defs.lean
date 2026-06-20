/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Definitions for the Chen–Larson Proposition 5.1 coefficient problem

Everything here is *exact rational arithmetic*: the statement layer of the
problem needs no real analysis.  Reference: `paper/prop51.tex` (tenth revision),
Sections 1–2, and Chen–Larson, arXiv:2603.23850, Proposition 5.1.

## Design

All sequences are defined through *prefix lists* (`cList n = [c_0, …, c_n]`)
built by structural recursion.  This single definition family is

* provable-about: each list step is a closed rational expression in the
  previous prefix, so spec lemmas (`c_succ`, positivity, …) follow by
  induction; and
* executable: the same definitions run under `native_decide` for the
  finite certificates (`Prop51/CertificateExact.lean`, …).

The mathematical objects:

* `c r` — coefficients of `log C(t)`, where
  `C(t) = Σ_k (6k)!/((3k)!(2k)!) (t/72)^k`; defined by the Riccati recurrence
  `c_1 = 5/6`, `c_r = 6(r-1)c_{r-1} + (6/r) Σ_{i=1}^{r-2} i(r-1-i) c_i c_{r-1-i}`.
* `expCoeff L a` — the `a`-th coefficient of `exp(Σ_{r≥1} L r · t^r)`,
  characterized by `E_0 = 1`, `n E_n = Σ_{j=1}^n j (L j) E_{n-j}`.
* `bCoeff μ a` — the Chen–Larson coefficient `[t^a] Π_i C(t/q_i) / C(t)^N`
  for the partition `μ`, via its exp-characterization
  `b = exp(-Σ_r D_r c_r t^r)`, `D_r = Σ_i (q_i - q_i^{-r})`, `q_i = m_i + 1`.
* `Unorm a N` — the partition-free majorant `U_a(N)/(N c_a)` of the paper,
  eq. (8)/(11): `b_a(μ) ≤ U_a(N)` for every positive partition of weight
  `N - n` (proved in `Prop51.Majorant`).

The bridge between `bCoeff`/`Unorm` and the official power-series coefficient
(via `Mathlib.RingTheory.PowerSeries`) is formalized in `Prop51.Bridge` and
`Prop51.BCoeffSeries`.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

namespace Prop51

/-! ## The logarithmic coefficients `c r` -/

/-- Prefix list `[c_0, c_1, …, c_n]` of the logarithmic coefficients of
`C(t)`, by the Riccati recurrence.  `c_0 = 0`, `c_1 = 5/6`, and for `r ≥ 2`
`c_r = 6(r-1)·c_{r-1} + (6/r)·Σ_{i=1}^{r-2} i(r-1-i)c_i c_{r-1-i}`. -/
def cList : Nat → List ℚ
  | 0 => [0]
  | 1 => [0, 5/6]
  | (n+2) =>
    let l := cList (n+1)
    let r := n+2
    let conv : ℚ := ((List.range (r-1)).map fun (i : Nat) =>
      (i : ℚ) * ((r-1-i : Nat) : ℚ) * (l.getD i 0) * (l.getD (r-1-i) 0)).sum
    l ++ [6*((r : ℚ)-1) * l.getD (r-1) 0 + 6/(r : ℚ) * conv]

/-- `c r` : the `r`-th logarithmic coefficient of `C(t)`. -/
def c (r : Nat) : ℚ := (cList r).getD r 0

/-! ## Coefficients of `exp(Σ L r · t^r)` -/

/-- Prefix list `[E_0, …, E_n]` of the coefficients of `exp(Σ_{r≥1} L r t^r)`:
`E_0 = 1` and `n·E_n = Σ_{j=1}^{n} j·(L j)·E_{n-j}`.  (`L 0` is ignored.) -/
def expList (L : Nat → ℚ) : Nat → List ℚ
  | 0 => [1]
  | (n+1) =>
    let l := expList L n
    let s : ℚ := ((List.range (n+1)).map fun (t : Nat) =>
      ((t+1 : Nat) : ℚ) * L (t+1) * l.getD (n-t) 0).sum
    l ++ [s / ((n+1 : Nat) : ℚ)]

/-- `expCoeff L a` : the `a`-th coefficient of `exp(Σ_{r≥1} L r t^r)`. -/
def expCoeff (L : Nat → ℚ) (a : Nat) : ℚ := (expList L a).getD a 0

/-! ## The Chen–Larson coefficient of a partition -/

/-- `Dr μ r = Σ_i (q_i - q_i^{-r})` with `q_i = m_i + 1`, for a partition
`μ = [m_1, …, m_n]` (order irrelevant: this is a sum over parts). -/
def Dr (μ : List Nat) (r : Nat) : ℚ :=
  (μ.map fun (mi : Nat) => ((mi+1 : Nat) : ℚ) - 1 / ((mi+1 : Nat) : ℚ)^r).sum

/-- The Chen–Larson Proposition 5.1 coefficient
`b_a(μ) = [t^a] (Π_i C(t/q_i)) / C(t)^N = [t^a] exp(-Σ_r D_r c_r t^r)`,
in its exp-characterized form (the power-series bridge is Layer A of the
roadmap). -/
def bCoeff (μ : List Nat) (a : Nat) : ℚ :=
  let cl := cList a
  expCoeff (fun r => -(Dr μ r) * cl.getD r 0) a

/-! ## The partition-free majorant -/

/-- `[B_0, …, B_a]` with `B_k = [t^k] C(t)^{-N}`. -/
def BListQ (cl : List ℚ) (N a : Nat) : List ℚ :=
  expList (fun r => -(N : ℚ) * cl.getD r 0) a

/-- `[Q_0, …, Q_a]` with `Q_k = [t^k] C(t/2)^{N/2}`. -/
def QListQ (cl : List ℚ) (N a : Nat) : List ℚ :=
  expList (fun r => (N : ℚ)/2 * cl.getD r 0 / 2^r) a

/-- The normalized majorant `U_a(N)/(N c_a)` of the paper (eq. 8/11):
`U_a(N) = B_a + Q_a + Σ_{1≤k<a, B_k>0} B_k Q_{a-k}`. -/
def Unorm (a N : Nat) : ℚ :=
  let cl := cList a
  let B := BListQ cl N a
  let Q := QListQ cl N a
  let pos : ℚ := ((List.range a).map fun (k : Nat) =>
    let bk := B.getD k 0
    if 1 ≤ k ∧ 0 < bk then bk * Q.getD (a-k) 0 else 0).sum
  (B.getD a 0 + Q.getD a 0 + pos) / ((N : ℚ) * cl.getD a 0)

/-! ## Basic spec lemmas -/

/-- Each step of `cList` appends exactly one entry. -/
theorem cList_succ_append : ∀ n : Nat, ∃ x : ℚ, cList (n+1) = cList n ++ [x]
  | 0 => ⟨5/6, rfl⟩
  | (_+1) => ⟨_, rfl⟩

theorem cList_length : ∀ n, (cList n).length = n + 1
  | 0 => rfl
  | (n+1) => by
      obtain ⟨x, hx⟩ := cList_succ_append n
      rw [hx, List.length_append, cList_length n]
      rfl

/-- Prefix stability: entries of `cList` do not change as the list grows. -/
theorem cList_getD_eq (r m : Nat) (h : r ≤ m) :
    (cList m).getD r 0 = c r := by
  induction m with
  | zero =>
      have : r = 0 := by omega
      subst this; rfl
  | succ m ih =>
      rcases Nat.lt_or_ge r (m+1) with hlt | hge
      · obtain ⟨x, hx⟩ := cList_succ_append m
        rw [hx, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by rw [cList_length]; omega),
            ← List.getD_eq_getElem?_getD]
        exact ih (by omega)
      · have : r = m+1 := le_antisymm h hge
        subst this; rfl

@[simp] theorem c_zero : c 0 = 0 := rfl
@[simp] theorem c_one : c 1 = 5/6 := rfl

/-- The defining Riccati recurrence for `c`, in clean form:
`c_r = 6(r-1)·c_{r-1} + (6/r)·Σ_{i<r-1} i·(r-1-i)·c_i·c_{r-1-i}` at `r = n+2`. -/
theorem c_succ_succ (n : Nat) :
    c (n+2) = 6*(((n+2 : Nat) : ℚ) - 1)*c (n+1)
      + 6/((n+2 : Nat) : ℚ) *
        ((List.range (n+1)).map fun (i : Nat) =>
          (i : ℚ) * ((n+1-i : Nat) : ℚ) * c i * c (n+1-i)).sum := by
  have hlen := cList_length (n+1)
  have hgetD : ∀ i, i ≤ n+1 → (cList (n+1)).getD i 0 = c i := fun i hi =>
    cList_getD_eq i (n+1) hi
  show (cList (n+2)).getD (n+2) 0 = _
  have hx : cList (n+2) = cList (n+1) ++
      [6*(((n+2 : Nat) : ℚ)-1) * (cList (n+1)).getD (n+1) 0
        + 6/((n+2 : Nat) : ℚ) *
          ((List.range (n+1)).map fun (i : Nat) =>
            (i : ℚ) * ((n+2-1-i : Nat) : ℚ) * ((cList (n+1)).getD i 0)
              * ((cList (n+1)).getD (n+2-1-i) 0)).sum] := by
    show cList (n+2) = _
    rfl
  rw [hx, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : (cList (n+1)).length ≤ n+2)]
  rw [hlen]
  have h0 : n + 2 - (n + 2) = 0 := by omega
  rw [h0]
  show 6*(((n+2 : Nat) : ℚ)-1) * (cList (n+1)).getD (n+1) 0
      + 6/((n+2 : Nat) : ℚ) * _ = _
  rw [hgetD (n+1) le_rfl]
  congr 2
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  have hi' : i < n+1 := List.mem_range.mp hi
  have e : n + 2 - 1 - i = n + 1 - i := by omega
  rw [e, hgetD i (by omega), hgetD (n+1-i) (by omega)]

end Prop51
