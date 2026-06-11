/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# The interval certificate checker (Layer B)

Verified-interval port of the Arb certificate
(`certificates/prop51_A400_certificate_package.zip`): for every pair
`(a, N)` with `61 ≤ a ≤ 400` and `6a-7 ≤ N ≤ 12a-8`, certify
`Unorm a N < 0` — hence (with `bCoeff_neg_of_unorm`) coefficient negativity
for all genera `g ≤ 1199`.

## Method

Interval tables for the exact rational sequences of `Prop51/Defs.lean`:

* `cTab A`    — encloses `c r` for `r ≤ A` (Riccati recurrence);
* `bTab cT N` — encloses `Bq N k = [X^k] C(X)^{-N}` (exp-recurrence);
* `qTab cT N` — encloses `Qq N j = [X^j] C(X/2)^{N/2}` (exp-recurrence).

Each interval recurrence mirrors its exact counterpart step by step, so
soundness (`mem_cTab`, `mem_bTab`, `mem_qTab`) is a structural induction
using the `mem`-preservation lemmas of `Prop51/Dyadic.lean`.

The positive-part terms `B_k Q_{a-k}` (included in `U_a(N)` only when
`B_k > 0`) are handled *unconditionally* by `DI.hull0`: the hull of the
product interval and `{0}` encloses the contribution whether or not the
exact sign condition holds, so no interval sign decision is ever needed.
This is conservative exactly where the reference Arb run was, and free of
slop where `B_k` is certainly negative (there `hull0` clips to `0`… and the
exact term *is* `0`).

`checkColumn` shares the `B`/`Q` tables across all admissible `a` for a
fixed `N` (the certificate's per-`N` table sharing); `checkRange` folds
columns over a range of `N`.  The `native_decide` instances live in
`Prop51/CertificateInterval*.lean`.
-/

import Prop51Kernel
import Prop51.Majorant
import Prop51.Dyadic

namespace Prop51

/-! ## Array helpers -/

private theorem getD_push_lt (T : Array DI) (x : DI) (r : Nat)
    (h : r < T.size) :
    (T.push x).getD r DI.zero = T.getD r DI.zero := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt h]

private theorem getD_push_size (T : Array DI) (x : DI) (r : Nat)
    (h : r = T.size) :
    (T.push x).getD r DI.zero = x := by
  subst h
  simp [Array.getD_eq_getD_getElem?]

/-! ## The interval `c`-table -/

theorem cTab_size : ∀ A, (cTab A).size = A + 1
  | 0 => rfl
  | 1 => rfl
  | (n+2) => by
      show ((cTab (n+1)).push _).size = _
      rw [Array.size_push, cTab_size (n+1)]

theorem mem_convC (T : Array DI) (m : Nat) (f : Nat → ℚ)
    (hT : ∀ i, i ≤ m → DI.mem (f i) (T.getD i DI.zero)) :
    ∀ j, j ≤ m →
      DI.mem (((List.range j).map fun (i : Nat) =>
          (i : ℚ) * ((m - i : Nat) : ℚ) * f i * f (m-i)).sum)
        (convC T m j)
  | 0, _ => by simpa using DI.mem_zero
  | (j+1), hj => by
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      have ih := mem_convC T m f hT j (by omega)
      have hterm : DI.mem ((j : ℚ) * ((m - j : Nat) : ℚ) * f j * f (m-j))
          (DI.nsmul (j * (m - j))
            ((T.getD j DI.zero).mul (T.getD (m-j) DI.zero))) := by
        rw [show (j : ℚ) * ((m - j : Nat) : ℚ) * f j * f (m-j)
            = ((j * (m - j) : Nat) : ℚ) * (f j * f (m-j)) by push_cast; ring]
        exact DI.mem_nsmul _ (DI.mem_mul (hT j (by omega)) (hT (m-j) (by omega)))
      exact DI.mem_add ih hterm

theorem mem_cTab : ∀ (A r : Nat), r ≤ A →
    DI.mem (c r) ((cTab A).getD r DI.zero)
  | 0, r, hr => by
      have : r = 0 := by omega
      subst this
      exact DI.mem_zero
  | 1, r, hr => by
      match r, hr with
      | 0, _ => exact DI.mem_zero
      | 1, _ =>
          show DI.mem (c 1) ((DI.exact 5).divNat 6)
          rw [show c 1 = ((5 : Nat) : ℚ) / ((6 : Nat) : ℚ) by norm_num]
          exact DI.mem_divNat 6 (by omega) (DI.mem_exact 5)
  | (n+2), r, hr => by
      have hx : cTab (n+2) = (cTab (n+1)).push
          ((DI.nsmul (6*(n+1)) ((cTab (n+1)).getD (n+1) DI.zero)).add
            ((DI.nsmul 6 (convC (cTab (n+1)) (n+1) (n+1))).divNat (n+2))) := rfl
      rcases Nat.lt_or_ge r (n+2) with hlt | hge
      · rw [hx, getD_push_lt _ _ _ (by rw [cTab_size]; omega)]
        exact mem_cTab (n+1) r (by omega)
      · have hr2 : r = n+2 := by omega
        subst hr2
        rw [hx, getD_push_size _ _ _ (by rw [cTab_size])]
        rw [c_succ_succ n]
        refine DI.mem_add ?_ ?_
        · rw [show 6*(((n+2 : Nat) : ℚ) - 1) * c (n+1)
              = ((6*(n+1) : Nat) : ℚ) * c (n+1) by push_cast; ring]
          exact DI.mem_nsmul _ (mem_cTab (n+1) (n+1) le_rfl)
        · rw [show 6/((n+2 : Nat) : ℚ) *
              ((List.range (n+1)).map fun (i : Nat) =>
                (i : ℚ) * ((n+1-i : Nat) : ℚ) * c i * c (n+1-i)).sum
              = (((6 : Nat) : ℚ) *
                ((List.range (n+1)).map fun (i : Nat) =>
                  (i : ℚ) * ((n+1-i : Nat) : ℚ) * c i * c (n+1-i)).sum)
                / ((n+2 : Nat) : ℚ) by push_cast; ring]
          exact DI.mem_divNat (n+2) (by omega)
            (DI.mem_nsmul 6
              (mem_convC (cTab (n+1)) (n+1) c
                (fun i hi => mem_cTab (n+1) i hi) (n+1) le_rfl))

/-! ## The interval `B`- and `Q`-tables -/

theorem bTab_size (cT : Array DI) (N : Nat) :
    ∀ n, (bTab cT N n).size = n + 1
  | 0 => rfl
  | (n+1) => by
      show ((bTab cT N n).push _).size = _
      rw [Array.size_push, bTab_size cT N n]

theorem qTab_size (cT : Array DI) (N : Nat) :
    ∀ n, (qTab cT N n).size = n + 1
  | 0 => rfl
  | (n+1) => by
      show ((qTab cT N n).push _).size = _
      rw [Array.size_push, qTab_size cT N n]

/-- The defining recurrence of `Bq`, division form. -/
private theorem Bq_succ (N n : Nat) :
    Bq N (n+1) = (∑ t ∈ Finset.range (n+1),
        ((t+1 : Nat) : ℚ) * (-(N : ℚ) * c (t+1)) * Bq N (n-t))
      / ((n+1 : Nat) : ℚ) := by
  have h := expCoeff_succ_mul (fun r => -(N : ℚ) * c r) n
  rw [eq_div_iff (by exact_mod_cast (by omega : (0:Nat) < n+1).ne')]
  rw [mul_comm]
  exact h

/-- The defining recurrence of `Qq`, division form. -/
private theorem Qq_succ (N n : Nat) :
    Qq N (n+1) = (∑ t ∈ Finset.range (n+1),
        ((t+1 : Nat) : ℚ) * ((N : ℚ)/2 * c (t+1) / 2^(t+1)) * Qq N (n-t))
      / ((n+1 : Nat) : ℚ) := by
  have h := expCoeff_succ_mul (fun r => (N : ℚ)/2 * c r / 2^r) n
  rw [eq_div_iff (by exact_mod_cast (by omega : (0:Nat) < n+1).ne')]
  rw [mul_comm]
  exact h

theorem mem_convB (cT : Array DI) (N : Nat) {A : Nat}
    (hc : ∀ i, i ≤ A → DI.mem (c i) (cT.getD i DI.zero))
    (T : Array DI) (n : Nat) (hn : n + 1 ≤ A)
    (hT : ∀ i, i ≤ n → DI.mem (Bq N i) (T.getD i DI.zero)) :
    ∀ j, j ≤ n + 1 →
      DI.mem (∑ t ∈ Finset.range j,
          ((t+1 : Nat) : ℚ) * (-(N : ℚ) * c (t+1)) * Bq N (n-t))
        (convB cT T N n j)
  | 0, _ => by simpa using DI.mem_zero
  | (j+1), hj => by
      rw [Finset.sum_range_succ]
      have ih := mem_convB cT N hc T n hn hT j (by omega)
      have hterm : DI.mem (((j+1 : Nat) : ℚ) * (-(N : ℚ) * c (j+1)) * Bq N (n-j))
          ((DI.nsmul ((j+1) * N)
            ((cT.getD (j+1) DI.zero).mul (T.getD (n-j) DI.zero))).neg) := by
        rw [show ((j+1 : Nat) : ℚ) * (-(N : ℚ) * c (j+1)) * Bq N (n-j)
            = -((((j+1) * N : Nat) : ℚ) * (c (j+1) * Bq N (n-j))) by
          push_cast; ring]
        exact DI.mem_neg (DI.mem_nsmul _
          (DI.mem_mul (hc (j+1) (by omega)) (hT (n-j) (by omega))))
      exact DI.mem_add ih hterm

theorem mem_convQ (cT : Array DI) (N : Nat) {A : Nat}
    (hc : ∀ i, i ≤ A → DI.mem (c i) (cT.getD i DI.zero))
    (T : Array DI) (n : Nat) (hn : n + 1 ≤ A)
    (hT : ∀ i, i ≤ n → DI.mem (Qq N i) (T.getD i DI.zero)) :
    ∀ j, j ≤ n + 1 →
      DI.mem (∑ t ∈ Finset.range j,
          ((t+1 : Nat) : ℚ) * ((N : ℚ)/2 * c (t+1) / 2^(t+1)) * Qq N (n-t))
        (convQ cT T N n j)
  | 0, _ => by simpa using DI.mem_zero
  | (j+1), hj => by
      rw [Finset.sum_range_succ]
      have ih := mem_convQ cT N hc T n hn hT j (by omega)
      have hterm : DI.mem
          (((j+1 : Nat) : ℚ) * ((N : ℚ)/2 * c (j+1) / 2^(j+1)) * Qq N (n-j))
          (DI.shr (j+2) (DI.nsmul ((j+1) * N)
            ((cT.getD (j+1) DI.zero).mul (T.getD (n-j) DI.zero)))) := by
        rw [show ((j+1 : Nat) : ℚ) * ((N : ℚ)/2 * c (j+1) / 2^(j+1)) * Qq N (n-j)
            = ((((j+1) * N : Nat) : ℚ) * (c (j+1) * Qq N (n-j))) / 2^(j+2) by
          push_cast; ring]
        exact DI.mem_shr (j+2) (DI.mem_nsmul _
          (DI.mem_mul (hc (j+1) (by omega)) (hT (n-j) (by omega))))
      exact DI.mem_add ih hterm

theorem mem_bTab (cT : Array DI) (N : Nat) {A : Nat}
    (hc : ∀ i, i ≤ A → DI.mem (c i) (cT.getD i DI.zero)) :
    ∀ n, n ≤ A → ∀ k, k ≤ n →
      DI.mem (Bq N k) ((bTab cT N n).getD k DI.zero)
  | 0, _, k, hk => by
      have : k = 0 := by omega
      subst this
      simpa [Bq] using DI.mem_one
  | (n+1), hn, k, hk => by
      have hx : bTab cT N (n+1) = (bTab cT N n).push
          ((convB cT (bTab cT N n) N n (n+1)).divNat (n+1)) := rfl
      rcases Nat.lt_or_ge k (n+1) with hlt | hge
      · rw [hx, getD_push_lt _ _ _ (by rw [bTab_size]; omega)]
        exact mem_bTab cT N hc n (by omega) k (by omega)
      · have hk2 : k = n+1 := by omega
        subst hk2
        rw [hx, getD_push_size _ _ _ (by rw [bTab_size])]
        rw [Bq_succ N n]
        exact DI.mem_divNat (n+1) (by omega)
          (mem_convB cT N hc (bTab cT N n) n hn
            (fun i hi => mem_bTab cT N hc n (by omega) i hi) (n+1) le_rfl)

theorem mem_qTab (cT : Array DI) (N : Nat) {A : Nat}
    (hc : ∀ i, i ≤ A → DI.mem (c i) (cT.getD i DI.zero)) :
    ∀ n, n ≤ A → ∀ k, k ≤ n →
      DI.mem (Qq N k) ((qTab cT N n).getD k DI.zero)
  | 0, _, k, hk => by
      have : k = 0 := by omega
      subst this
      simpa [Qq] using DI.mem_one
  | (n+1), hn, k, hk => by
      have hx : qTab cT N (n+1) = (qTab cT N n).push
          ((convQ cT (qTab cT N n) N n (n+1)).divNat (n+1)) := rfl
      rcases Nat.lt_or_ge k (n+1) with hlt | hge
      · rw [hx, getD_push_lt _ _ _ (by rw [qTab_size]; omega)]
        exact mem_qTab cT N hc n (by omega) k (by omega)
      · have hk2 : k = n+1 := by omega
        subst hk2
        rw [hx, getD_push_size _ _ _ (by rw [qTab_size])]
        rw [Qq_succ N n]
        exact DI.mem_divNat (n+1) (by omega)
          (mem_convQ cT N hc (qTab cT N n) n hn
            (fun i hi => mem_qTab cT N hc n (by omega) i hi) (n+1) le_rfl)

/-! ## The per-pair check -/

theorem mem_uTerms (B Q : Array DI) (N a : Nat)
    (hB : ∀ i, i ≤ a → DI.mem (Bq N i) (B.getD i DI.zero))
    (hQ : ∀ i, i ≤ a → DI.mem (Qq N i) (Q.getD i DI.zero)) :
    ∀ j, j ≤ a →
      DI.mem (∑ k ∈ Finset.range j,
          if 1 ≤ k ∧ 0 < Bq N k then Bq N k * Qq N (a-k) else 0)
        (uTerms B Q a j)
  | 0, _ => by simpa using DI.mem_zero
  | (j+1), hj => by
      rw [Finset.sum_range_succ]
      have ih := mem_uTerms B Q N a hB hQ j (by omega)
      have hterm : DI.mem
          (if 1 ≤ j ∧ 0 < Bq N j then Bq N j * Qq N (a-j) else 0)
          (if j = 0 then DI.zero
           else DI.hull0 ((B.getD j DI.zero).mul (Q.getD (a-j) DI.zero))) := by
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0
          rw [if_pos (rfl : (0:Nat) = 0),
            if_neg (fun hc => (by omega : ¬ (1:Nat) ≤ 0) hc.1)]
          exact DI.mem_zero
        · rw [if_neg (by omega : ¬ j = 0)]
          by_cases hbq : 0 < Bq N j
          · rw [if_pos (⟨by omega, hbq⟩ : 1 ≤ j ∧ 0 < Bq N j)]
            exact DI.mem_hull0_of_mem
              (DI.mem_mul (hB j (by omega)) (hQ (a-j) (by omega)))
          · rw [if_neg (fun hc => hbq hc.2)]
            exact DI.zero_mem_hull0 _
      exact DI.mem_add ih hterm

theorem checkPair_sound (B Q : Array DI) (N a : Nat) (hN : 0 < N) (ha : 1 ≤ a)
    (hB : ∀ i, i ≤ a → DI.mem (Bq N i) (B.getD i DI.zero))
    (hQ : ∀ i, i ≤ a → DI.mem (Qq N i) (Q.getD i DI.zero))
    (h : checkPair B Q a = true) : Unorm a N < 0 := by
  have hmem : DI.mem
      (Bq N a + Qq N a + ∑ k ∈ Finset.range a,
        if 1 ≤ k ∧ 0 < Bq N k then Bq N k * Qq N (a-k) else 0)
      ((((B.getD a DI.zero).add (Q.getD a DI.zero)).add
        (uTerms B Q a a))) :=
    DI.mem_add (DI.mem_add (hB a le_rfl) (hQ a le_rfl))
      (mem_uTerms B Q N a hB hQ a le_rfl)
  have hneg := DF.val_neg_of_m_neg (of_decide_eq_true h)
  have hnum := lt_of_le_of_lt hmem.2 hneg
  rw [Unorm_eq]
  exact div_neg_of_neg_of_pos hnum
    (mul_pos (by exact_mod_cast hN) (c_pos a ha))

/-! ## Columns and ranges -/

theorem checkColumn_sound (N : Nat) (hN : 359 ≤ N)
    (h : checkColumn (cTab 400) N = true) :
    ∀ a, 61 ≤ a → a ≤ 400 → 6*a - 7 ≤ N → N ≤ 12*a - 8 → Unorm a N < 0 := by
  intro a h61 h400 hlo hhi
  unfold checkColumn at h
  dsimp only at h
  have hrm : a ≤ min 400 ((N+7)/6) := by omega
  have halo : max 61 ((N+19)/12) ≤ a := by omega
  have hmem : a ∈ List.range' (max 61 ((N+19)/12))
      (min 400 ((N+7)/6) + 1 - max 61 ((N+19)/12)) :=
    List.mem_range'.mpr ⟨a - max 61 ((N+19)/12), by omega, by omega⟩
  have hpair := List.all_eq_true.mp h a hmem
  refine checkPair_sound _ _ N a (by omega) (by omega) ?_ ?_ hpair
  · intro i hi
    exact mem_bTab (cTab 400) N (fun i hi => mem_cTab 400 i hi)
      (min 400 ((N+7)/6)) (min_le_left _ _) i (by omega)
  · intro i hi
    exact mem_qTab (cTab 400) N (fun i hi => mem_cTab 400 i hi)
      (min 400 ((N+7)/6)) (min_le_left _ _) i (by omega)

theorem checkRange_sound (lo len : Nat) (h : checkRange lo len = true) :
    ∀ a N, 61 ≤ a → a ≤ 400 → 6*a - 7 ≤ N → N ≤ 12*a - 8 →
      lo ≤ N → N < lo + len → Unorm a N < 0 := by
  intro a N h61 h400 hlo hhi hNlo hNhi
  unfold checkRange at h
  dsimp only at h
  have hmem : N ∈ List.range' lo len :=
    List.mem_range'.mpr ⟨N - lo, by omega, by omega⟩
  have hcol := List.all_eq_true.mp h N hmem
  exact checkColumn_sound N (by omega) hcol a h61 h400 hlo hhi

end Prop51
