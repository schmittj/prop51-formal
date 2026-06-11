/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Completeness of the partition generator (Layer A′)

`mem_partitions_iff` characterizes membership in `partitions n`: the
generated lists are exactly the weakly decreasing (`Pairwise (· ≥ ·)`) lists
of positive parts summing to `n`.  Together with permutation-invariance of
`bCoeff`, this upgrades the generator-quantified certificate
`bCoeff_neg_g_le_23` to the predicate form over *all* positive partitions.
-/
import Prop51.Defs
import Prop51.Partitions
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace Prop51

/-- Characterization of `partitionsLe`: weakly decreasing positive lists with
parts at most `p`, summing to `n`. -/
theorem mem_partitionsLe_iff : ∀ (n p : Nat) (μ : List Nat),
    μ ∈ partitionsLe n p ↔
      μ.sum = n ∧ List.Pairwise (· ≥ ·) μ ∧ ∀ x ∈ μ, 1 ≤ x ∧ x ≤ p := by
  intro n p
  induction n, p using partitionsLe.induct with
  | case1 p =>
      intro μ
      constructor
      · intro hμ
        simp only [partitionsLe, List.mem_singleton] at hμ
        subst hμ
        simp
      · rintro ⟨hsum, -, hpos⟩
        match μ with
        | [] => simp [partitionsLe]
        | (x :: t) =>
            exfalso
            have h1 : 1 ≤ x := (hpos x (by simp)).1
            simp only [List.sum_cons] at hsum
            omega
  | case2 n =>
      intro μ
      constructor
      · intro hμ
        simp [partitionsLe] at hμ
      · rintro ⟨hsum, -, hpos⟩
        match μ with
        | [] => simp at hsum
        | (x :: t) =>
            have h2 := (hpos x (by simp)).2
            have h1 := (hpos x (by simp)).1
            omega
  | case3 n p ih1 ih2 =>
      intro μ
      rw [partitionsLe]
      simp only [List.mem_append]
      constructor
      · rintro (hμ | hμ)
        · rcases Nat.decLe (p+1) (n+1) with hle | hle
          · rw [if_neg hle] at hμ; simp at hμ
          · rw [if_pos hle] at hμ
            obtain ⟨ν, hν, rfl⟩ := List.mem_map.mp hμ
            obtain ⟨hsum, hpair, hbnd⟩ := (ih1 hle ν).mp hν
            refine ⟨?_, ?_, ?_⟩
            · simp only [List.sum_cons, hsum]; omega
            · exact List.pairwise_cons.mpr
                ⟨fun y hy => (hbnd y hy).2, hpair⟩
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · omega
              · have := hbnd x hx; omega
        · obtain ⟨hsum, hpair, hbnd⟩ := (ih2 μ).mp hμ
          exact ⟨hsum, hpair, fun x hx => by have := hbnd x hx; omega⟩
      · rintro ⟨hsum, hpair, hbnd⟩
        match μ with
        | [] => simp at hsum
        | (h :: t) =>
            have hh := hbnd h (by simp)
            have hhead := (List.pairwise_cons.mp hpair).1
            have htail := (List.pairwise_cons.mp hpair).2
            rcases Nat.lt_or_ge h (p+1) with hlt | hge
            · right
              refine (ih2 (h :: t)).mpr ⟨hsum, hpair, ?_⟩
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · omega
              · have h1 := (hbnd x (List.mem_cons_of_mem _ hx)).1
                have h2 := hhead x hx
                omega
            · have hh1 : h = p + 1 := by
                have := hh.2; omega
              subst hh1
              left
              have hle : p + 1 ≤ n + 1 := by
                simp only [List.sum_cons] at hsum
                omega
              rw [if_pos hle]
              refine List.mem_map.mpr ⟨t, ?_, rfl⟩
              refine (ih1 hle t).mpr ⟨?_, htail, ?_⟩
              · simp only [List.sum_cons] at hsum
                omega
              · intro x hx
                have h1 := (hbnd x (List.mem_cons_of_mem _ hx)).1
                have h2 := hhead x hx
                omega

/-- Characterization of `partitions n`: exactly the weakly decreasing lists
of positive parts summing to `n`. -/
theorem mem_partitions_iff {n : Nat} {μ : List Nat} :
    μ ∈ partitions n ↔
      μ.sum = n ∧ List.Pairwise (· ≥ ·) μ ∧ ∀ x ∈ μ, 1 ≤ x := by
  rw [partitions, mem_partitionsLe_iff]
  constructor
  · rintro ⟨hs, hc, hb⟩
    exact ⟨hs, hc, fun x hx => (hb x hx).1⟩
  · rintro ⟨hs, hc, hb⟩
    refine ⟨hs, hc, fun x hx => ⟨hb x hx, ?_⟩⟩
    subst hs
    exact List.single_le_sum (fun y _ => Nat.zero_le y) x hx

/-! ## Permutation invariance of `bCoeff` -/

theorem Dr_perm {μ μ' : List Nat} (h : μ.Perm μ') (r : Nat) :
    Dr μ r = Dr μ' r :=
  (h.map _).sum_eq

theorem bCoeff_perm {μ μ' : List Nat} (h : μ.Perm μ') (a : Nat) :
    bCoeff μ a = bCoeff μ' a := by
  have : (fun r => -(Dr μ r) * (cList a).getD r 0)
       = (fun r => -(Dr μ' r) * (cList a).getD r 0) := by
    funext r
    rw [Dr_perm h]
  show expCoeff (fun r => -(Dr μ r) * (cList a).getD r 0) a
     = expCoeff (fun r => -(Dr μ' r) * (cList a).getD r 0) a
  rw [this]

/-- Every list of naturals is a permutation of a weakly decreasing one. -/
theorem exists_sorted_perm (μ : List Nat) :
    ∃ μ', μ.Perm μ' ∧ List.Pairwise (· ≥ ·) μ' :=
  ⟨μ.insertionSort (· ≥ ·), (μ.perm_insertionSort (· ≥ ·)).symm,
    μ.pairwise_insertionSort (· ≥ ·)⟩

end Prop51
