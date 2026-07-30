/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.Algebra.GroupAlgebra.Basic
public import FGAP.GroupTheory.BinaryTetrahedral.QuaternionGroup
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

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

private def quaternionSubgroupI : quaternionSubgroup :=
  ⟨quaternionI, by
    rw [quaternionSubgroup_eq_closure]
    exact Subgroup.subset_closure (by simp)⟩

private def quaternionSubgroupJ : quaternionSubgroup :=
  ⟨quaternionJ, by
    rw [quaternionSubgroup_eq_closure]
    exact Subgroup.subset_closure (by simp)⟩

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

end

end BinaryTetrahedral
