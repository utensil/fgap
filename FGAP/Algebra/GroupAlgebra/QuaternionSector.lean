/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.Algebra.GroupAlgebra.CentralInvolution
public import FGAP.Algebra.GroupAlgebra.QuaternionQuotient

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# The central sectors of the real quaternion-group algebra

The central quaternion `-1` splits the real quaternion-group algebra into
positive and negative sectors. The positive sector is exactly the kernel of
the quaternion representation, while the negative sector maps linearly and
bijectively to Hamilton's quaternions.

## Main declarations

* `BinaryTetrahedral.quaternionCentralInvolution`: the central element `-1` in
  the concrete quaternion subgroup.
* `BinaryTetrahedral.ker_quaternionAlgebraMap_eq_quaternionPlusSector`: the
  positive sector is the kernel of the quaternion representation.
* `BinaryTetrahedral.quaternionMinusSectorEquiv`: the negative sector is
  real-linearly equivalent to `ℍ[ℝ]`.

## References

* John Voight, *Quaternion Algebras*, §11.2, p. 166.
  <https://doi.org/10.1007/978-3-030-56694-4>
* Forest note `fgap-001B`.
  <https://github.com/utensil/forest/pull/68>
-/

public section

open scoped Quaternion

namespace BinaryTetrahedral

noncomputable section

local instance : Invertible (2 : ℝ) :=
  invertibleOfNonzero (by norm_num)

/-- The central involution `-1` in the concrete quaternion subgroup. -/
def quaternionCentralInvolution : quaternionSubgroup :=
  quaternionGroupEquiv (QuaternionGroup.a 2)

/-- The concrete quaternion central involution is `-1`. -/
@[simp]
theorem coe_quaternionCentralInvolution :
    (quaternionCentralInvolution.1 : ℍ[ℝ]) = -1 := by
  change ((quaternionGroupEquiv (QuaternionGroup.a 2) : quaternionSubgroup).1 :
    ℍ[ℝ]) = -1
  rw [show (quaternionGroupEquiv (QuaternionGroup.a 2) : quaternionSubgroup).1 =
    quaternionGroupHom (QuaternionGroup.a 2) from quaternionGroupEquiv_apply _]
  rw [quaternionGroupHom_a_two]
  rfl

/-- The distinguished quaternion involution is central. -/
theorem quaternionCentralInvolution_mem_center :
    quaternionCentralInvolution ∈ Set.center quaternionSubgroup := by
  rw [Semigroup.mem_center_iff]
  intro q
  apply Subtype.ext
  change q.1 * quaternionCentralInvolution.1 =
    quaternionCentralInvolution.1 * q.1
  apply Units.ext
  change (q.1 : ℍ[ℝ]) * (quaternionCentralInvolution.1 : ℍ[ℝ]) =
    (quaternionCentralInvolution.1 : ℍ[ℝ]) * (q.1 : ℍ[ℝ])
  rw [coe_quaternionCentralInvolution]
  ext <;>
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

/-- The distinguished quaternion involution squares to one. -/
theorem quaternionCentralInvolution_sq :
    quaternionCentralInvolution * quaternionCentralInvolution = 1 := by
  apply Subtype.ext
  change quaternionCentralInvolution.1 * quaternionCentralInvolution.1 = 1
  apply Units.ext
  change (quaternionCentralInvolution.1 : ℍ[ℝ]) *
    (quaternionCentralInvolution.1 : ℍ[ℝ]) = 1
  rw [coe_quaternionCentralInvolution]
  ext <;>
    norm_num [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

private abbrev quaternionCentralBasis : QuaternionGroupAlgebra :=
  MonoidAlgebra.of ℝ quaternionSubgroup quaternionCentralInvolution

private theorem quaternionCentralBasis_mem_center :
    quaternionCentralBasis ∈ Set.center QuaternionGroupAlgebra :=
  GroupAlgebra.of_mem_center quaternionCentralInvolution
    quaternionCentralInvolution_mem_center

private theorem quaternionCentralBasis_sq :
    quaternionCentralBasis * quaternionCentralBasis = 1 :=
  GroupAlgebra.of_mul_self_eq_one quaternionCentralInvolution
    quaternionCentralInvolution_sq

private abbrev quaternionPlusProjection :
    Module.End QuaternionGroupAlgebra QuaternionGroupAlgebra :=
  CentralInvolution.plusProjection (R := ℝ) quaternionCentralBasis
    quaternionCentralBasis_mem_center

private abbrev quaternionMinusProjection :
    Module.End QuaternionGroupAlgebra QuaternionGroupAlgebra :=
  CentralInvolution.minusProjection (R := ℝ) quaternionCentralBasis
    quaternionCentralBasis_mem_center

/-- The positive central-involution sector, regarded as a real subspace. -/
def quaternionPlusSector : Submodule ℝ QuaternionGroupAlgebra :=
  Submodule.restrictScalars ℝ (LinearMap.range quaternionPlusProjection)

/-- The negative central-involution sector, regarded as a real subspace. -/
def quaternionMinusSector : Submodule ℝ QuaternionGroupAlgebra :=
  Submodule.restrictScalars ℝ (LinearMap.range quaternionMinusProjection)

/-- The quaternion representation kills the positive central idempotent. -/
@[simp]
theorem quaternionAlgebraMap_centralPlus :
    quaternionAlgebraMap
        (GroupAlgebra.centralPlus (R := ℝ) quaternionCentralInvolution) = 0 := by
  rw [GroupAlgebra.centralPlus, CentralInvolution.centralPlus, map_smul,
    map_add, map_one, quaternionAlgebraMap_of,
    coe_quaternionCentralInvolution]
  simp

/-- The quaternion representation sends the negative central idempotent to one. -/
@[simp]
theorem quaternionAlgebraMap_centralMinus :
    quaternionAlgebraMap
        (GroupAlgebra.centralMinus (R := ℝ) quaternionCentralInvolution) = 1 := by
  have h := congrArg quaternionAlgebraMap
    (GroupAlgebra.centralPlus_add_centralMinus (R := ℝ)
      quaternionCentralInvolution)
  rw [map_add, map_one, quaternionAlgebraMap_centralPlus, zero_add] at h
  exact h

private theorem quaternionPlusSector_le_ker :
    quaternionPlusSector ≤ LinearMap.ker quaternionAlgebraMap.toLinearMap := by
  rintro x ⟨y, rfl⟩
  rw [LinearMap.mem_ker]
  change quaternionAlgebraMap
      (GroupAlgebra.centralPlus (R := ℝ) quaternionCentralInvolution * y) = 0
  rw [map_mul, quaternionAlgebraMap_centralPlus, zero_mul]

private inductive QuaternionSectorIndex
  | one | i | j | k
  deriving DecidableEq, Fintype

private def quaternionSectorRepresentativeAbstract :
    QuaternionSectorIndex → QuaternionGroup 2
  | .one => QuaternionGroup.a 0
  | .i => QuaternionGroup.a 1
  | .j => QuaternionGroup.xa 0
  | .k => QuaternionGroup.xa 1

private def quaternionSectorRepresentative :
    QuaternionSectorIndex → quaternionSubgroup :=
  fun a ↦ quaternionGroupEquiv (quaternionSectorRepresentativeAbstract a)

private theorem quaternionSectorRepresentative_injective :
    Function.Injective quaternionSectorRepresentative := by
  exact quaternionGroupEquiv.injective.comp (by
    intro a b
    cases a <;> cases b <;> decide)

private theorem quaternionSectorRepresentativeAbstract_ne_opposite
    (a b : QuaternionSectorIndex) :
    quaternionSectorRepresentativeAbstract a ≠
      QuaternionGroup.a 2 * quaternionSectorRepresentativeAbstract b := by
  cases a <;> cases b <;> decide

private theorem quaternionSectorRepresentative_ne_opposite
    (a b : QuaternionSectorIndex) :
    quaternionSectorRepresentative a ≠
      quaternionCentralInvolution * quaternionSectorRepresentative b := by
  intro h
  apply quaternionSectorRepresentativeAbstract_ne_opposite a b
  apply quaternionGroupEquiv.injective
  simpa [quaternionSectorRepresentative, quaternionCentralInvolution] using h

private def quaternionPlusVector (a : QuaternionSectorIndex) :
    QuaternionGroupAlgebra :=
  (⅟ (2 : ℝ)) •
    (MonoidAlgebra.single (quaternionSectorRepresentative a) 1 +
      MonoidAlgebra.single
        (quaternionCentralInvolution * quaternionSectorRepresentative a) 1)

private theorem quaternionPlusVector_mem_sector (a : QuaternionSectorIndex) :
    quaternionPlusVector a ∈ quaternionPlusSector := by
  refine ⟨MonoidAlgebra.of ℝ quaternionSubgroup
    (quaternionSectorRepresentative a), ?_⟩
  rw [CentralInvolution.plusProjection_apply]
  change GroupAlgebra.centralPlus (R := ℝ) quaternionCentralInvolution *
      MonoidAlgebra.of ℝ quaternionSubgroup (quaternionSectorRepresentative a) =
    quaternionPlusVector a
  rw [GroupAlgebra.centralPlus, CentralInvolution.centralPlus, smul_mul_assoc,
    add_mul, one_mul, ← map_mul]
  rfl

private def quaternionPlusCoordinates :
    QuaternionGroupAlgebra →ₗ[ℝ] QuaternionSectorIndex → ℝ :=
  LinearMap.pi fun a ↦
    (Finsupp.lapply (R := ℝ) (M := ℝ) (quaternionSectorRepresentative a)).comp
      (MonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

private theorem quaternionPlusCoordinates_vector (a : QuaternionSectorIndex) :
    quaternionPlusCoordinates (quaternionPlusVector a) =
      Pi.single a (2 : ℝ)⁻¹ := by
  classical
  funext b
  by_cases hab : a = b
  · subst b
    have hne :
        quaternionCentralInvolution * quaternionSectorRepresentative a ≠
          quaternionSectorRepresentative a :=
      (quaternionSectorRepresentative_ne_opposite a a).symm
    simp [quaternionPlusCoordinates, quaternionPlusVector,
      Pi.single, hne]
  · have hba : b ≠ a := Ne.symm hab
    have hrep :
        quaternionSectorRepresentative a ≠ quaternionSectorRepresentative b :=
      quaternionSectorRepresentative_injective.ne hab
    have hopp :
        quaternionCentralInvolution * quaternionSectorRepresentative a ≠
          quaternionSectorRepresentative b :=
      (quaternionSectorRepresentative_ne_opposite b a).symm
    simp [quaternionPlusCoordinates, quaternionPlusVector,
      Pi.single, hba, hrep, hopp]

private theorem quaternionPlusVector_linearIndependent :
    LinearIndependent ℝ quaternionPlusVector := by
  apply LinearIndependent.of_comp quaternionPlusCoordinates
  simpa [Function.comp_def, quaternionPlusCoordinates_vector] using
    (Pi.linearIndependent_single_of_ne_zero (R := ℝ)
      (v := fun _ : QuaternionSectorIndex ↦ (2 : ℝ)⁻¹) (fun _ ↦ by norm_num))

private theorem four_le_finrank_quaternionPlusSector :
    4 ≤ Module.finrank ℝ quaternionPlusSector := by
  let v : QuaternionSectorIndex → quaternionPlusSector :=
    fun a ↦ ⟨quaternionPlusVector a, quaternionPlusVector_mem_sector a⟩
  have hv : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp quaternionPlusSector.subtype
    simpa [v, Function.comp_def] using quaternionPlusVector_linearIndependent
  have hcard := hv.fintype_card_le_finrank
  simpa only [show Fintype.card QuaternionSectorIndex = 4 by decide] using hcard

/-- The kernel of the quaternion representation is the positive
central-involution sector. -/
theorem ker_quaternionAlgebraMap_eq_quaternionPlusSector :
    LinearMap.ker quaternionAlgebraMap.toLinearMap = quaternionPlusSector := by
  symm
  apply Submodule.eq_of_le_of_finrank_le quaternionPlusSector_le_ker
  rw [finrank_ker_quaternionAlgebraMap]
  exact four_le_finrank_quaternionPlusSector

private def quaternionAlgebraMapOnMinusSector :
    quaternionMinusSector →ₗ[ℝ] ℍ[ℝ] :=
  quaternionAlgebraMap.toLinearMap.domRestrict quaternionMinusSector

private theorem quaternionAlgebraMapOnMinusSector_injective :
    Function.Injective quaternionAlgebraMapOnMinusSector := by
  intro x y h
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hker : (x - y : QuaternionGroupAlgebra) ∈
      LinearMap.ker quaternionAlgebraMap.toLinearMap := by
    rw [LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr h
  rw [ker_quaternionAlgebraMap_eq_quaternionPlusSector] at hker
  have hminus : (x - y : QuaternionGroupAlgebra) ∈ quaternionMinusSector :=
    quaternionMinusSector.sub_mem x.property y.property
  have hcompl := CentralInvolution.isCompl_range_plusProjection_range_minusProjection
    (R := ℝ) (M := QuaternionGroupAlgebra) quaternionCentralBasis
    quaternionCentralBasis_mem_center quaternionCentralBasis_sq
  exact Submodule.disjoint_def.mp hcompl.disjoint _
    (show (x - y : QuaternionGroupAlgebra) ∈
      LinearMap.range quaternionPlusProjection from hker)
    (show (x - y : QuaternionGroupAlgebra) ∈
      LinearMap.range quaternionMinusProjection from hminus)

private theorem quaternionAlgebraMapOnMinusSector_surjective :
    Function.Surjective quaternionAlgebraMapOnMinusSector := by
  intro q
  obtain ⟨x, rfl⟩ := quaternionAlgebraMap_surjective q
  let y : QuaternionGroupAlgebra := quaternionMinusProjection x
  refine ⟨⟨y, ⟨x, rfl⟩⟩, ?_⟩
  change quaternionAlgebraMap
      (GroupAlgebra.centralMinus (R := ℝ) quaternionCentralInvolution * x) =
    quaternionAlgebraMap x
  rw [map_mul, quaternionAlgebraMap_centralMinus, one_mul]

/-- The negative central-involution sector maps real-linearly and bijectively
to Hamilton's quaternions. -/
noncomputable def quaternionMinusSectorEquiv :
    quaternionMinusSector ≃ₗ[ℝ] ℍ[ℝ] :=
  LinearEquiv.ofBijective quaternionAlgebraMapOnMinusSector
    ⟨quaternionAlgebraMapOnMinusSector_injective,
      quaternionAlgebraMapOnMinusSector_surjective⟩

/-- The negative-sector equivalence agrees with the quaternion representation. -/
@[simp]
theorem quaternionMinusSectorEquiv_apply (x : quaternionMinusSector) :
    quaternionMinusSectorEquiv x = quaternionAlgebraMap x :=
  by
    rw [quaternionMinusSectorEquiv, LinearEquiv.ofBijective_apply]
    rfl

end

end BinaryTetrahedral
