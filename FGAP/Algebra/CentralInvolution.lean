/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.NoncommRing

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

## Main declarations

* `CentralInvolution.centralPlus` and `CentralInvolution.centralMinus` are the
  complementary elements associated with a square-one element.
* `CentralInvolution.projectionRangesEquiv` decomposes a module into the ranges
  of the two induced projections.
* `CentralInvolution.plusEigenspace` and
  `CentralInvolution.minusEigenspace` identify those ranges as eigenspaces.
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

/-- The positive and negative elements add to one. -/
theorem centralPlus_add_centralMinus (z : A) :
    centralPlus R z + centralMinus R z = 1 := by
  rw [centralPlus, centralMinus, ← smul_add]
  have h : (1 + z) + (1 - z) = (1 : A) + 1 := by abel
  rw [h, smul_add]
  exact invOf_two_smul_add_invOf_two_smul R 1

/-- The negative element is the complement of the positive element. -/
theorem one_sub_centralPlus (z : A) :
    1 - centralPlus R z = centralMinus R z := by
  rw [sub_eq_iff_eq_add, add_comm, centralPlus_add_centralMinus]

/-- The positive element is idempotent when `z` squares to one. -/
theorem centralPlus_mul_self (z : A) (hz : z * z = 1) :
    centralPlus R z * centralPlus R z = centralPlus R z := by
  rw [centralPlus, smul_mul_smul]
  have h : (1 + z) * (1 + z) = (2 : R) • (1 + z) := by
    rw [two_smul]
    noncomm_ring [hz]
  rw [h, smul_smul]
  congr 1
  rw [mul_assoc, invOf_mul_self, mul_one]

/-- The positive element, regarded as an idempotent element. -/
theorem isIdempotentElem_centralPlus (z : A) (hz : z * z = 1) :
    IsIdempotentElem (centralPlus R z) :=
  centralPlus_mul_self (R := R) z hz

/-- The negative element is idempotent when `z` squares to one. -/
theorem centralMinus_mul_self (z : A) (hz : z * z = 1) :
    centralMinus R z * centralMinus R z = centralMinus R z := by
  rw [← one_sub_centralPlus (R := R)]
  exact (isIdempotentElem_centralPlus (R := R) z hz).one_sub

/-- The positive element annihilates the negative element. -/
theorem centralPlus_mul_centralMinus (z : A) (hz : z * z = 1) :
    centralPlus R z * centralMinus R z = 0 := by
  rw [← one_sub_centralPlus (R := R)]
  exact (isIdempotentElem_centralPlus (R := R) z hz).mul_one_sub_self

/-- The negative element annihilates the positive element. -/
theorem centralMinus_mul_centralPlus (z : A) (hz : z * z = 1) :
    centralMinus R z * centralPlus R z = 0 := by
  rw [← one_sub_centralPlus (R := R)]
  exact (isIdempotentElem_centralPlus (R := R) z hz).one_sub_mul_self

private theorem mul_centralPlus (z : A) (hz : z * z = 1) :
    z * centralPlus R z = centralPlus R z := by
  rw [centralPlus, Algebra.mul_smul_comm]
  congr 1
  noncomm_ring [hz]

private theorem mul_centralMinus (z : A) (hz : z * z = 1) :
    z * centralMinus R z = -centralMinus R z := by
  rw [centralMinus, Algebra.mul_smul_comm, ← smul_neg]
  congr 1
  noncomm_ring [hz]

/-- The negative element, regarded as an idempotent element. -/
theorem isIdempotentElem_centralMinus (z : A) (hz : z * z = 1) :
    IsIdempotentElem (centralMinus R z) :=
  centralMinus_mul_self (R := R) z hz

/-- The positive element is central when `z` is central. -/
theorem centralPlus_mem_center (z : A) (hz : z ∈ Set.center A) :
    centralPlus R z ∈ Set.center A := by
  rw [centralPlus, Algebra.smul_def]
  exact Set.mul_mem_center (Set.algebraMap_mem_center (⅟ (2 : R)))
    (Set.add_mem_center Set.one_mem_center hz)

/-- The negative element is central when `z` is central. -/
theorem centralMinus_mem_center (z : A) (hz : z ∈ Set.center A) :
    centralMinus R z ∈ Set.center A := by
  rw [centralMinus, Algebra.smul_def]
  exact Set.mul_mem_center (Set.algebraMap_mem_center (⅟ (2 : R)))
    (by simpa [sub_eq_add_neg] using
      Set.add_mem_center Set.one_mem_center (Set.neg_mem_center hz))

section Module

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- Multiplication by a central algebra element, as an endomorphism of an `A`-module. -/
def centralMul (a : A) (ha : a ∈ Set.center A) : Module.End A M :=
  Module.End.smulLeft a ha

/-- Applying `centralMul a ha` is the action of `a`. -/
@[simp]
theorem centralMul_apply (a : A) (ha : a ∈ Set.center A) (x : M) :
    centralMul a ha x = a • x :=
  rfl

/-- The endomorphism that becomes the positive projection when `z` squares to one. -/
def plusProjection (z : A) (hz : z ∈ Set.center A) : Module.End A M :=
  centralMul (centralPlus R z) (centralPlus_mem_center (R := R) z hz)

/-- The endomorphism that becomes the negative projection when `z` squares to one. -/
def minusProjection (z : A) (hz : z ∈ Set.center A) : Module.End A M :=
  centralMul (centralMinus R z) (centralMinus_mem_center (R := R) z hz)

/-- The positive projection acts by the positive element. -/
@[simp]
theorem plusProjection_apply (z : A) (hz : z ∈ Set.center A) (x : M) :
    plusProjection (R := R) z hz x = centralPlus R z • x :=
  rfl

/-- The negative projection acts by the negative element. -/
@[simp]
theorem minusProjection_apply (z : A) (hz : z ∈ Set.center A) (x : M) :
    minusProjection (R := R) z hz x = centralMinus R z • x :=
  rfl

/-- The positive projection is idempotent when `z` squares to one. -/
theorem isIdempotentElem_plusProjection (z : A) (hz : z ∈ Set.center A)
    (hz2 : z * z = 1) :
    IsIdempotentElem (plusProjection (R := R) (M := M) z hz) := by
  ext x
  simp [plusProjection, centralMul, smul_smul, centralPlus_mul_self (R := R) z hz2]

/-- The negative projection is idempotent when `z` squares to one. -/
theorem isIdempotentElem_minusProjection (z : A) (hz : z ∈ Set.center A)
    (hz2 : z * z = 1) :
    IsIdempotentElem (minusProjection (R := R) (M := M) z hz) := by
  ext x
  simp [minusProjection, centralMul, smul_smul, centralMinus_mul_self (R := R) z hz2]

/-- The positive and negative projections add to the identity. -/
theorem plusProjection_add_minusProjection (z : A) (hz : z ∈ Set.center A) :
    plusProjection (R := R) (M := M) z hz + minusProjection (R := R) (M := M) z hz = 1 := by
  ext x
  change centralPlus R z • x + centralMinus R z • x = x
  rw [← add_smul, centralPlus_add_centralMinus, one_smul]

private theorem one_sub_plusProjection (z : A) (hz : z ∈ Set.center A) :
    1 - plusProjection (R := R) (M := M) z hz = minusProjection (R := R) (M := M) z hz := by
  rw [sub_eq_iff_eq_add, add_comm, plusProjection_add_minusProjection]

private theorem one_sub_minusProjection (z : A) (hz : z ∈ Set.center A) :
    1 - minusProjection (R := R) (M := M) z hz = plusProjection (R := R) (M := M) z hz := by
  rw [sub_eq_iff_eq_add, plusProjection_add_minusProjection]

/-- The positive element fixes exactly the vectors fixed by `z`. -/
theorem centralPlus_smul_eq_iff (z : A) (hz2 : z * z = 1) (x : M) :
    centralPlus R z • x = x ↔ z • x = x := by
  constructor
  · intro hx
    calc
      z • x = z • (centralPlus R z • x) := by rw [hx]
      _ = (z * centralPlus R z) • x := by rw [mul_smul]
      _ = centralPlus R z • x := by rw [mul_centralPlus (R := R) z hz2]
      _ = x := hx
  · intro hx
    rw [centralPlus, Algebra.smul_def, mul_smul, add_smul, one_smul, hx, smul_add, ← add_smul]
    rw [← map_add, invOf_two_add_invOf_two, map_one, one_smul]

/-- The negative element fixes exactly the vectors negated by `z`. -/
theorem centralMinus_smul_eq_iff (z : A) (hz2 : z * z = 1) (x : M) :
    centralMinus R z • x = x ↔ z • x = -x := by
  constructor
  · intro hx
    calc
      z • x = z • (centralMinus R z • x) := by rw [hx]
      _ = (z * centralMinus R z) • x := by rw [mul_smul]
      _ = (-centralMinus R z) • x := by rw [mul_centralMinus (R := R) z hz2]
      _ = -(centralMinus R z • x) := by rw [neg_smul]
      _ = -x := by rw [hx]
  · intro hx
    rw [centralMinus, Algebra.smul_def, mul_smul, sub_smul, one_smul, hx, sub_neg_eq_add,
      smul_add, ← add_smul]
    rw [← map_add, invOf_two_add_invOf_two, map_one, one_smul]

/-- The kernel of the positive projection is the range of the negative projection. -/
theorem ker_plusProjection_eq_range_minusProjection (z : A) (hz : z ∈ Set.center A)
    (hz2 : z * z = 1) :
    LinearMap.ker (plusProjection (R := R) (M := M) z hz) =
      LinearMap.range (minusProjection (R := R) (M := M) z hz) := by
  rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub
      (isIdempotentElem_plusProjection (R := R) (M := M) z hz hz2),
    one_sub_plusProjection]

/-- The kernel of the negative projection is the range of the positive projection. -/
theorem ker_minusProjection_eq_range_plusProjection (z : A) (hz : z ∈ Set.center A)
    (hz2 : z * z = 1) :
    LinearMap.ker (minusProjection (R := R) (M := M) z hz) =
      LinearMap.range (plusProjection (R := R) (M := M) z hz) := by
  rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub
      (isIdempotentElem_minusProjection (R := R) (M := M) z hz hz2),
    one_sub_minusProjection]

/-- The ranges of the positive and negative projections are complementary. -/
theorem isCompl_range_plusProjection_range_minusProjection (z : A) (hz : z ∈ Set.center A)
    (hz2 : z * z = 1) :
    IsCompl (LinearMap.range (plusProjection (R := R) (M := M) z hz))
      (LinearMap.range (minusProjection (R := R) (M := M) z hz)) := by
  rw [← ker_plusProjection_eq_range_minusProjection (R := R) z hz hz2]
  exact LinearMap.IsIdempotentElem.isCompl
    (isIdempotentElem_plusProjection (R := R) (M := M) z hz hz2)

/-- The decomposition of a module into the ranges of the two central projections. -/
noncomputable def projectionRangesEquiv (z : A) (hz : z ∈ Set.center A)
    (hz2 : z * z = 1) :
    (LinearMap.range (plusProjection (R := R) (M := M) z hz) ×
        LinearMap.range (minusProjection (R := R) (M := M) z hz)) ≃ₗ[A] M :=
  Submodule.prodEquivOfIsCompl _ _
    (isCompl_range_plusProjection_range_minusProjection (R := R) z hz hz2) (E := M)

/-- The `+1` eigenspace of the action by `z`. -/
def plusEigenspace (z : A) (hz : z ∈ Set.center A) : Submodule A M :=
  LinearMap.ker (centralMul z hz - 1)

/-- The `-1` eigenspace of the action by `z`. -/
def minusEigenspace (z : A) (hz : z ∈ Set.center A) : Submodule A M :=
  LinearMap.ker (centralMul z hz + 1)

/-- The range of the positive projection is the positive eigenspace. -/
theorem range_plusProjection_eq_plusEigenspace (z : A) (hz : z ∈ Set.center A)
    (hz2 : z * z = 1) :
    LinearMap.range (plusProjection (R := R) (M := M) z hz) =
      plusEigenspace (M := M) z hz := by
  ext x
  rw [LinearMap.IsIdempotentElem.mem_range_iff
    (isIdempotentElem_plusProjection (R := R) (M := M) z hz hz2)]
  simp [plusEigenspace, centralPlus_smul_eq_iff (R := R) z hz2, sub_eq_zero]

/-- The range of the negative projection is the negative eigenspace. -/
theorem range_minusProjection_eq_minusEigenspace (z : A) (hz : z ∈ Set.center A)
    (hz2 : z * z = 1) :
    LinearMap.range (minusProjection (R := R) (M := M) z hz) =
      minusEigenspace (M := M) z hz := by
  ext x
  rw [LinearMap.IsIdempotentElem.mem_range_iff
    (isIdempotentElem_minusProjection (R := R) (M := M) z hz hz2)]
  simp [minusEigenspace, centralMinus_smul_eq_iff (R := R) z hz2, eq_neg_iff_add_eq_zero]

end Module

end CentralInvolution
