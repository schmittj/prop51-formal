/-
Copyright (c) 2026 the prop51-formal contributors. Released under Apache 2.0.

# Fast Nat-residue checker for corrected Proposition 5.2

This file is the performance-oriented finite-field kernel.  It mirrors the
bundled C++ checker: arithmetic is carried out as natural-number residues
modulo a prime, with inverses and inverse powers precomputed for the fixed
degree.

The current theorems check the first two new finite degrees, `a = 9, 10`,
over all generated partitions.  Larger degrees use the chunk interface below
from separate certificate modules, so adding a new chunk does not force Lean to
re-evaluate the earlier certificates.  A separate soundness bridge will connect
this Nat-level kernel to `Prop52.Modular.correctedCoeffMod` and then to the
rational coefficient.
-/

import Prop52.Modular

namespace Prop52

/-! ## Basic modular arithmetic on natural residues -/

def addMod (p x y : Nat) : Nat :=
  (x + y) % p

def subMod (p x y : Nat) : Nat :=
  if y ≤ x then x - y else x + p - y

def mulMod (p x y : Nat) : Nat :=
  (x * y) % p

def powMod (p x e : Nat) : Nat :=
  if h : e = 0 then
    1 % p
  else
    let y := powMod p x (e / 2)
    let yy := mulMod p y y
    if e % 2 = 0 then yy else mulMod p x yy
termination_by e
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 2)

def invMod (p x : Nat) : Nat :=
  powMod p x (p - 2)

def sumMod (p : Nat) (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => addMod p acc x) 0

/-! ## Precomputed tables -/

def invIntTable (p a : Nat) : Array Nat :=
  (List.range (a + 1)).map (fun r => if r = 0 then 0 else invMod p r) |>.toArray

def invPowTable (p a maxQ : Nat) : Array (Array Nat) :=
  (List.range (maxQ + 1)).map (fun q =>
    let iq := if q = 0 then 0 else invMod p q
    ((List.range (a + 1)).map fun r => powMod p iq r).toArray) |>.toArray

def get2D (table : Array (Array Nat)) (q r : Nat) : Nat :=
  (table.getD q #[]).getD r 0

/-! ## Coefficients modulo `p` -/

def cListModNat (p : Nat) : Nat → List Nat
  | 0 => [0]
  | 1 => [0, mulMod p 5 (invMod p 6)]
  | n + 2 =>
      let l := cListModNat p (n + 1)
      let r := n + 2
      let conv := sumMod p <| (List.range (r - 1)).map fun i =>
        mulMod p (mulMod p i (r - 1 - i))
          (mulMod p (l.getD i 0) (l.getD (r - 1 - i) 0))
      l ++ [addMod p
        (mulMod p (6 * (r - 1)) (l.getD (r - 1) 0))
        (mulMod p (mulMod p 6 ((invIntTable p r).getD r 0)) conv)]

def expListModNat (p : Nat) (invInt : Array Nat) (L : Nat → Nat) : Nat → List Nat
  | 0 => [1 % p]
  | n + 1 =>
      let l := expListModNat p invInt L n
      let s := sumMod p <| (List.range (n + 1)).map fun t =>
        mulMod p (mulMod p (t + 1) (L (t + 1))) (l.getD (n - t) 0)
      l ++ [mulMod p s (invInt.getD (n + 1) 0)]

def sPowerModNat (p : Nat) (invPow : Array (Array Nat)) (μ : List Nat) (r : Nat) : Nat :=
  sumMod p <| μ.map fun mi => get2D invPow (mi + 1) r

def markedWeightModNat (p : Nat) (invPow : Array (Array Nat)) (μ : List Nat) (r : Nat) : Nat :=
  sumMod p <| μ.map fun mi => mulMod p mi (get2D invPow (mi + 1) r)

def correctedCoeffModNatWith
    (p a : Nat) (c invInt : Array Nat) (invPow : Array (Array Nat)) (μ : List Nat) : Nat :=
  let Nmod := N μ % p
  let hCoeff := fun r =>
    mulMod p (c.getD r 0) (subMod p Nmod (sPowerModNat p invPow μ r))
  let bList := expListModNat p invInt (fun r => subMod p 0 (hCoeff r)) a
  let bCoeff := fun r => bList.getD r 0
  let kCoeff := fun r =>
    match r with
    | 0 => 0
    | 1 => mulMod p 2 (markedWeightModNat p invPow μ 1)
    | j + 2 =>
        mulMod p (mulMod p (mulMod p 12 (j + 1)) (c.getD (j + 1) 0))
          (markedWeightModNat p invPow μ (j + 2))
  let conv := sumMod p <| (List.range a).map fun k =>
    mulMod p (kCoeff (k + 1)) (bCoeff (a - (k + 1)))
  subMod p (mulMod p (M a % p) (bCoeff a)) conv

def correctedCoeffModNat (p a : Nat) (μ : List Nat) : Nat :=
  let c := (cListModNat p a).toArray
  let invInt := invIntTable p a
  let invPow := invPowTable p a (M a + 1)
  correctedCoeffModNatWith p a c invInt invPow μ

def checkGeneratedModNat (p a : Nat) : Bool :=
  let c := (cListModNat p a).toArray
  let invInt := invIntTable p a
  let invPow := invPowTable p a (M a + 1)
  (Prop51.partitions (M a)).all fun μ =>
    correctedCoeffModNatWith p a c invInt invPow μ != 0

/-- Chunked variant of `checkGeneratedModNat`, used for the larger finite
degrees so each native certificate has bounded evaluation cost. -/
def checkGeneratedModNatChunk (p a start len : Nat) : Bool :=
  let c := (cListModNat p a).toArray
  let invInt := invIntTable p a
  let invPow := invPowTable p a (M a + 1)
  ((Prop51.partitions (M a)).drop start |>.take len).all fun μ =>
    correctedCoeffModNatWith p a c invInt invPow μ != 0

/-- Generated partitions of `n` whose first part is exactly `first`.

This branch-shaped enumerator avoids repeatedly constructing the full
partition list when large finite certificates are split into chunks. -/
def partitionsWithFirst (n first : Nat) : List (List Nat) :=
  if first = 0 ∨ n < first then
    []
  else
    (Prop51.partitionsLe (n - first) first).map fun μ => first :: μ

def checkGeneratedModNatFirstPartWith
    (p a : Nat) (c invInt : Array Nat) (invPow : Array (Array Nat))
    (first : Nat) : Bool :=
  (partitionsWithFirst (M a) first).all fun μ =>
    correctedCoeffModNatWith p a c invInt invPow μ != 0

def checkGeneratedModNatFirstPart (p a first : Nat) : Bool :=
  let c := (cListModNat p a).toArray
  let invInt := invIntTable p a
  let invPow := invPowTable p a (M a + 1)
  checkGeneratedModNatFirstPartWith p a c invInt invPow first

def checkGeneratedModNatFirstPartRange (p a start len : Nat) : Bool :=
  let c := (cListModNat p a).toArray
  let invInt := invIntTable p a
  let invPow := invPowTable p a (M a + 1)
  (List.range len).all fun j =>
    checkGeneratedModNatFirstPartWith p a c invInt invPow (start + j)

/-- Fast Nat-residue certificate for the first previously open finite degree. -/
theorem checkGeneratedModNat_9_prime1 :
    checkGeneratedModNat finitePrime1 9 = true := by
  native_decide

/-- Fast Nat-residue certificate for degree `a = 10`. -/
theorem checkGeneratedModNat_10_prime1 :
    checkGeneratedModNat finitePrime1 10 = true := by
  native_decide

end Prop52
