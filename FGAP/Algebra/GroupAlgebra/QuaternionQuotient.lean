/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.Algebra.GroupAlgebra.Basic
public import FGAP.GroupTheory.BinaryTetrahedral.QuaternionGroup
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.DeriveFintype

/-!
# The quaternion quotient of the real quaternion-group algebra

The concrete quaternion subgroup of `ℍ[ℝ]ˣ` acts on `ℍ[ℝ]` by multiplication.
Linear extension gives a surjective real-algebra homomorphism from its group
algebra to the quaternions. This file identifies the resulting quotient and
computes the dimension of the kernel.

## Main declarations

* `BinaryTetrahedral.quaternionAlgebraMap`: the linear extension of the concrete
  quaternion representation.
* `BinaryTetrahedral.quaternionAlgebraMap_surjective`: the map is onto.
* `BinaryTetrahedral.finrank_ker_quaternionAlgebraMap`: its kernel has real
  dimension four.
* `BinaryTetrahedral.quaternionAlgebraQuotientEquiv`: the quotient by the kernel
  is isomorphic to `ℍ[ℝ]`.
* `BinaryTetrahedral.quaternionKernelBasis`: an explicit basis of the linear
  kernel by opposite-pair sums.
* `BinaryTetrahedral.restrictScalars_ringHom_ker_quaternionAlgebraMap`: the ideal
  kernel and linear kernel agree as real submodules.

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

/-- The real group algebra of the concrete quaternion subgroup. -/
abbrev QuaternionGroupAlgebra := MonoidAlgebra ℝ quaternionSubgroup

/-- Linear extension of the inclusion of the concrete quaternion subgroup into
Hamilton's quaternions. -/
def quaternionAlgebraMap : QuaternionGroupAlgebra →ₐ[ℝ] ℍ[ℝ] :=
  MonoidAlgebra.lift ℝ (ℍ[ℝ]) quaternionSubgroup
    ((Units.coeHom (ℍ[ℝ])).comp quaternionSubgroup.subtype)

@[simp]
theorem quaternionAlgebraMap_of (q : quaternionSubgroup) :
    quaternionAlgebraMap (MonoidAlgebra.of ℝ quaternionSubgroup q) = (q.1 : ℍ[ℝ]) :=
  MonoidAlgebra.lift_of _ q

@[simp]
theorem quaternionAlgebraMap_single (q : quaternionSubgroup) (r : ℝ) :
    quaternionAlgebraMap (MonoidAlgebra.single q r) = r • (q.1 : ℍ[ℝ]) :=
  MonoidAlgebra.lift_single _ q r

/-- The quaternion representation of the real group algebra is surjective. -/
theorem quaternionAlgebraMap_surjective :
    Function.Surjective quaternionAlgebraMap := by
  intro q
  let x : QuaternionGroupAlgebra :=
    MonoidAlgebra.single 1 q.re +
      MonoidAlgebra.single quaternionSubgroupI q.imI +
      MonoidAlgebra.single quaternionSubgroupJ q.imJ +
      MonoidAlgebra.single (quaternionSubgroupI * quaternionSubgroupJ) q.imK
  refine ⟨x, ?_⟩
  ext <;>
    simp [x, quaternionSubgroupI, quaternionSubgroupJ, quaternionI, quaternionJ,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

/-- The kernel of the quaternion representation has real dimension four. -/
theorem finrank_ker_quaternionAlgebraMap :
    Module.finrank ℝ (LinearMap.ker quaternionAlgebraMap.toLinearMap) = 4 := by
  have h_range :
      LinearMap.range quaternionAlgebraMap.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr quaternionAlgebraMap_surjective
  have h_domain :
      Module.finrank ℝ QuaternionGroupAlgebra = 8 := by
    rw [LinearEquiv.finrank_eq (MonoidAlgebra.coeffLinearEquiv ℝ),
      Module.finrank_finsupp_self, card_quaternionSubgroup]
  have h_codomain : Module.finrank ℝ ℍ[ℝ] = 4 :=
    Quaternion.finrank_eq_four
  have h_rank :
      Module.finrank ℝ (LinearMap.range quaternionAlgebraMap.toLinearMap) = 4 := by
    rw [h_range, finrank_top, h_codomain]
  have h := quaternionAlgebraMap.toLinearMap.finrank_range_add_finrank_ker
  omega

/-- The quotient of the real quaternion-group algebra by the kernel of its
quaternion representation is Hamilton's quaternion algebra. -/
noncomputable def quaternionAlgebraQuotientEquiv :
    (QuaternionGroupAlgebra ⧸ (RingHom.ker quaternionAlgebraMap)) ≃ₐ[ℝ] ℍ[ℝ] :=
  Ideal.quotientKerAlgEquivOfSurjective quaternionAlgebraMap_surjective

/-- The 4 opposite pairs of quaternion-group elements. -/
inductive QuaternionKernelIndex
  | one | i | j | k
  deriving DecidableEq, Fintype

instance : Nonempty QuaternionKernelIndex :=
  ⟨.one⟩

private def quaternionKernelRepresentative : QuaternionKernelIndex → quaternionSubgroup
  | .one => 1
  | .i => quaternionSubgroupI
  | .j => quaternionSubgroupJ
  | .k => quaternionSubgroupI * quaternionSubgroupJ

private def quaternionKernelOpposite : QuaternionKernelIndex → quaternionSubgroup
  | .one => quaternionSubgroupI ^ 2
  | .i => quaternionSubgroupI ^ 3
  | .j => quaternionSubgroupI ^ 2 * quaternionSubgroupJ
  | .k => quaternionSubgroupI ^ 3 * quaternionSubgroupJ

/-- The sum of the 2 Group-Algebra basis elements in an opposite quaternion pair. -/
@[expose]
def quaternionKernelVector : QuaternionKernelIndex → QuaternionGroupAlgebra
  | .one =>
      MonoidAlgebra.of ℝ quaternionSubgroup 1 +
        MonoidAlgebra.of ℝ quaternionSubgroup (quaternionSubgroupI ^ 2)
  | .i =>
      MonoidAlgebra.of ℝ quaternionSubgroup quaternionSubgroupI +
        MonoidAlgebra.of ℝ quaternionSubgroup (quaternionSubgroupI ^ 3)
  | .j =>
      MonoidAlgebra.of ℝ quaternionSubgroup quaternionSubgroupJ +
        MonoidAlgebra.of ℝ quaternionSubgroup
          (quaternionSubgroupI ^ 2 * quaternionSubgroupJ)
  | .k =>
      MonoidAlgebra.of ℝ quaternionSubgroup
          (quaternionSubgroupI * quaternionSubgroupJ) +
        MonoidAlgebra.of ℝ quaternionSubgroup
          (quaternionSubgroupI ^ 3 * quaternionSubgroupJ)

/-- The kernel vector indexed by `1`, as an explicit opposite-pair sum. -/
@[simp]
theorem quaternionKernelVector_one :
    quaternionKernelVector .one =
      MonoidAlgebra.of ℝ quaternionSubgroup 1 +
        MonoidAlgebra.of ℝ quaternionSubgroup (quaternionSubgroupI ^ 2) :=
  rfl

/-- The kernel vector indexed by `i`, as an explicit opposite-pair sum. -/
@[simp]
theorem quaternionKernelVector_i :
    quaternionKernelVector .i =
      MonoidAlgebra.of ℝ quaternionSubgroup quaternionSubgroupI +
        MonoidAlgebra.of ℝ quaternionSubgroup (quaternionSubgroupI ^ 3) :=
  rfl

/-- The kernel vector indexed by `j`, as an explicit opposite-pair sum. -/
@[simp]
theorem quaternionKernelVector_j :
    quaternionKernelVector .j =
      MonoidAlgebra.of ℝ quaternionSubgroup quaternionSubgroupJ +
        MonoidAlgebra.of ℝ quaternionSubgroup
          (quaternionSubgroupI ^ 2 * quaternionSubgroupJ) :=
  rfl

/-- The kernel vector indexed by `k`, as an explicit opposite-pair sum. -/
@[simp]
theorem quaternionKernelVector_k :
    quaternionKernelVector .k =
      MonoidAlgebra.of ℝ quaternionSubgroup
          (quaternionSubgroupI * quaternionSubgroupJ) +
        MonoidAlgebra.of ℝ quaternionSubgroup
          (quaternionSubgroupI ^ 3 * quaternionSubgroupJ) :=
  rfl

private theorem quaternionKernelVector_eq (a : QuaternionKernelIndex) :
    quaternionKernelVector a =
      MonoidAlgebra.of ℝ quaternionSubgroup (quaternionKernelRepresentative a) +
        MonoidAlgebra.of ℝ quaternionSubgroup (quaternionKernelOpposite a) := by
  cases a <;> rfl

/-- Each opposite-pair sum lies in the kernel of the quaternion quotient map. -/
theorem quaternionKernelVector_mem_ker (a : QuaternionKernelIndex) :
    quaternionKernelVector a ∈ LinearMap.ker quaternionAlgebraMap.toLinearMap := by
  rw [LinearMap.mem_ker]
  cases a <;>
    ext <;>
    norm_num [quaternionKernelVector, quaternionKernelRepresentative,
      quaternionKernelOpposite, quaternionSubgroupI, quaternionSubgroupJ,
      pow_succ, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

private def quaternionKernelCoordinates :
    QuaternionGroupAlgebra →ₗ[ℝ] QuaternionKernelIndex → ℝ :=
  LinearMap.pi fun a =>
    (Finsupp.lapply (R := ℝ) (M := ℝ) (quaternionKernelRepresentative a)).comp
      (MonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

private theorem quaternionKernelRepresentative_injective :
    Function.Injective quaternionKernelRepresentative := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals
    exfalso
    have h' := congrArg (fun q : quaternionSubgroup =>
      (((q.1 : ℍ[ℝ]).re, (q.1 : ℍ[ℝ]).imI),
        ((q.1 : ℍ[ℝ]).imJ, (q.1 : ℍ[ℝ]).imK))) h
    norm_num [quaternionKernelRepresentative, quaternionSubgroupI,
      quaternionSubgroupJ, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] at h'

private theorem quaternionKernelRepresentative_ne_opposite (a b : QuaternionKernelIndex) :
    quaternionKernelRepresentative a ≠ quaternionKernelOpposite b := by
  intro h
  cases a <;> cases b
  all_goals
    have h' := congrArg (fun q : quaternionSubgroup =>
      (((q.1 : ℍ[ℝ]).re, (q.1 : ℍ[ℝ]).imI),
        ((q.1 : ℍ[ℝ]).imJ, (q.1 : ℍ[ℝ]).imK))) h
    norm_num [quaternionKernelRepresentative, quaternionKernelOpposite,
      quaternionSubgroupI, quaternionSubgroupJ, pow_succ,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] at h'

private theorem quaternionKernelCoordinates_vector (a : QuaternionKernelIndex) :
    quaternionKernelCoordinates (quaternionKernelVector a) = Pi.single a 1 := by
  classical
  funext b
  have hne : quaternionKernelOpposite a ≠ quaternionKernelRepresentative b :=
    (quaternionKernelRepresentative_ne_opposite b a).symm
  by_cases hab : a = b
  · subst b
    simp [quaternionKernelCoordinates, quaternionKernelVector_eq,
      hne, Pi.single]
  · have hba : b ≠ a := Ne.symm hab
    simp [quaternionKernelCoordinates, quaternionKernelVector_eq,
      quaternionKernelRepresentative_injective.eq_iff, hne, Pi.single, hba]

private theorem quaternionKernelVector_linearIndependent :
    LinearIndependent ℝ quaternionKernelVector := by
  apply LinearIndependent.of_comp quaternionKernelCoordinates
  simpa [Function.comp_def, quaternionKernelCoordinates_vector] using
    Pi.linearIndependent_single_one QuaternionKernelIndex ℝ

private def quaternionKernelVectorInKer (a : QuaternionKernelIndex) :
    LinearMap.ker quaternionAlgebraMap.toLinearMap :=
  ⟨quaternionKernelVector a, quaternionKernelVector_mem_ker a⟩

private theorem quaternionKernelVectorInKer_linearIndependent :
    LinearIndependent ℝ quaternionKernelVectorInKer := by
  apply LinearIndependent.of_comp
    (LinearMap.ker quaternionAlgebraMap.toLinearMap).subtype
  simpa [Function.comp_def, quaternionKernelVectorInKer] using
    quaternionKernelVector_linearIndependent

/-- The opposite-pair sums form a basis of the kernel of the quaternion quotient. -/
noncomputable def quaternionKernelBasis :
    Module.Basis QuaternionKernelIndex ℝ (LinearMap.ker quaternionAlgebraMap.toLinearMap) :=
  basisOfLinearIndependentOfCardEqFinrank
    quaternionKernelVectorInKer_linearIndependent (by
      rw [finrank_ker_quaternionAlgebraMap]
      decide)

/-- Coercing a kernel basis vector gives its explicit opposite-pair sum. -/
@[simp]
theorem coe_quaternionKernelBasis (a : QuaternionKernelIndex) :
    ((quaternionKernelBasis a :
        LinearMap.ker quaternionAlgebraMap.toLinearMap) : QuaternionGroupAlgebra) =
      quaternionKernelVector a := by
  simp [quaternionKernelBasis, quaternionKernelVectorInKer]

/-- The ideal kernel and linear kernel have the same underlying real submodule. -/
theorem restrictScalars_ringHom_ker_quaternionAlgebraMap :
    Submodule.restrictScalars ℝ (RingHom.ker quaternionAlgebraMap) =
      LinearMap.ker quaternionAlgebraMap.toLinearMap := by
  ext x
  simp

end

end BinaryTetrahedral
