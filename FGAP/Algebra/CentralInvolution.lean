/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Ring.Center
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Tactic.NoncommRing

/-!
# Splitting along a central involution

Let `z` be a central element of an algebra such that `z * z = 1`. When two is
invertible in the base ring, the elements

`e₊ = ⅟ 2 • (1 + z)` and `e₋ = ⅟ 2 • (1 - z)`

are complementary central idempotents. This file develops their elementary
algebraic identities before using them as projections on modules.

The mathematical development follows Forest notes `fgap-000W`–`fgap-0013`.
For the relation between idempotents, projections, and generated ideals, see
Ambar N. Sengupta, *Representations of Algebras and Finite Groups*, Section
4.5.
-/

@[expose] public section

open scoped Ring

namespace CentralInvolution

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Invertible (2 : R)]

/-- The positive element associated with an algebra element `z`. -/
def centralPlus (R : Type*) [CommRing R] [Algebra R A] [Invertible (2 : R)] (z : A) : A :=
  (⅟ (2 : R)) • (1 + z)

/-- The negative element associated with an algebra element `z`. -/
def centralMinus (R : Type*) [CommRing R] [Algebra R A] [Invertible (2 : R)] (z : A) : A :=
  (⅟ (2 : R)) • (1 - z)

theorem centralPlus_add_centralMinus (z : A) :
    centralPlus R z + centralMinus R z = 1 := by
  rw [centralPlus, centralMinus, ← smul_add]
  have h : (1 + z) + (1 - z) = (1 : A) + 1 := by abel
  rw [h, smul_add]
  exact invOf_two_smul_add_invOf_two_smul R 1

theorem centralPlus_mul_self (z : A) (hz : z * z = 1) :
    centralPlus R z * centralPlus R z = centralPlus R z := by
  rw [centralPlus, smul_mul_smul]
  have h : (1 + z) * (1 + z) = (2 : R) • (1 + z) := by
    rw [two_smul]
    noncomm_ring [hz]
  rw [h, smul_smul]
  congr 1
  rw [mul_assoc, invOf_mul_self, mul_one]

theorem centralMinus_mul_self (z : A) (hz : z * z = 1) :
    centralMinus R z * centralMinus R z = centralMinus R z := by
  rw [centralMinus, smul_mul_smul]
  have h : (1 - z) * (1 - z) = (2 : R) • (1 - z) := by
    rw [two_smul]
    noncomm_ring [hz]
  rw [h, smul_smul]
  congr 1
  rw [mul_assoc, invOf_mul_self, mul_one]

theorem centralPlus_mul_centralMinus (z : A) (hz : z * z = 1) :
    centralPlus R z * centralMinus R z = 0 := by
  rw [centralPlus, centralMinus, smul_mul_smul]
  have h : (1 + z) * (1 - z) = (0 : A) := by noncomm_ring [hz]
  simp [h]

theorem centralMinus_mul_centralPlus (z : A) (hz : z * z = 1) :
    centralMinus R z * centralPlus R z = 0 := by
  rw [centralPlus, centralMinus, smul_mul_smul]
  have h : (1 - z) * (1 + z) = (0 : A) := by noncomm_ring [hz]
  simp [h]

theorem centralPlus_isIdempotentElem (z : A) (hz : z * z = 1) :
    IsIdempotentElem (centralPlus R z) :=
  centralPlus_mul_self (R := R) z hz

theorem centralMinus_isIdempotentElem (z : A) (hz : z * z = 1) :
    IsIdempotentElem (centralMinus R z) :=
  centralMinus_mul_self (R := R) z hz

theorem centralPlus_mem_center (z : A) (hz : z ∈ Set.center A) :
    centralPlus R z ∈ Set.center A := by
  rw [centralPlus, Algebra.smul_def]
  exact Set.mul_mem_center (Set.algebraMap_mem_center (⅟ (2 : R)))
    (Set.add_mem_center Set.one_mem_center hz)

theorem centralMinus_mem_center (z : A) (hz : z ∈ Set.center A) :
    centralMinus R z ∈ Set.center A := by
  rw [centralMinus, Algebra.smul_def]
  exact Set.mul_mem_center (Set.algebraMap_mem_center (⅟ (2 : R)))
    (by simpa [sub_eq_add_neg] using
      Set.add_mem_center Set.one_mem_center (Set.neg_mem_center hz))

end CentralInvolution
