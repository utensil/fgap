/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.Algebra.GroupAlgebra.CentralInvolution
public import FGAP.GroupTheory.BinaryTetrahedral.Abstract

import Mathlib.Tactic.NormNum

/-!
# The central split of the binary tetrahedral Group Algebra

The distinguished central involution of the abstract binary tetrahedral group
defines complementary central idempotents in its real Group Algebra. Their
left-multiplication endomorphisms split the regular module into complementary
ranges. The faithful quaternionic realization extends linearly to a
surjective real-algebra map. This map vanishes on the positive range and only
depends on the negative projection.

The central split is developed in Forest notes `fgap-0014` and `fgap-0015`.
The quaternionic map follows the Group-Algebra extension in Sengupta,
Sections 3.1--3.2, pp. 39--41, and the concrete Hurwitz units in Voight,
Section 11.2, p. 166.

## Main declarations

* `BinaryTetrahedral.centralPlus` and `BinaryTetrahedral.centralMinus` are the
  complementary central idempotents.
* `BinaryTetrahedral.plusProjection` and
  `BinaryTetrahedral.minusProjection` are their actions on the regular module.
* `BinaryTetrahedral.isCompl_projection_ranges` proves that the 2 ranges are
  complementary.
* `BinaryTetrahedral.abstractQuaternionAlgebraMap` extends the abstract
  quaternionic realization to the real Group Algebra.
* `BinaryTetrahedral.abstractQuaternionAlgebraMap_surjective` proves that this
  map is onto Hamilton's quaternions.
-/

@[expose] public section

open scoped MonoidAlgebra Quaternion Ring

namespace BinaryTetrahedral

noncomputable local instance : Invertible (2 : ℝ) :=
  invertibleOfNonzero (by norm_num)

/-- The real Group Algebra of the abstract binary tetrahedral group. -/
abbrev RealGroupAlgebra := ℝ[Abstract]

/-- The Group-Algebra basis element of the distinguished central involution. -/
noncomputable def centralBasisInvolution : RealGroupAlgebra :=
  MonoidAlgebra.of ℝ Abstract centralInvolution

/-- The distinguished basis element squares to 1. -/
theorem centralBasisInvolution_mul_self :
    centralBasisInvolution * centralBasisInvolution = 1 :=
  _root_.GroupAlgebra.of_mul_self_eq_one centralInvolution
    (by simpa only [pow_two] using centralInvolution_sq)

/-- The distinguished basis element is central. -/
theorem centralBasisInvolution_mem_center :
    centralBasisInvolution ∈ Set.center RealGroupAlgebra :=
  _root_.GroupAlgebra.of_mem_center centralInvolution centralInvolution_mem_center

/-- The positive central idempotent associated with the distinguished involution. -/
noncomputable def centralPlus : RealGroupAlgebra :=
  CentralInvolution.centralPlus ℝ centralBasisInvolution

/-- The negative central idempotent associated with the distinguished involution. -/
noncomputable def centralMinus : RealGroupAlgebra :=
  CentralInvolution.centralMinus ℝ centralBasisInvolution

/-- The positive central element is idempotent. -/
theorem centralPlus_isIdempotentElem :
    IsIdempotentElem centralPlus :=
  CentralInvolution.isIdempotentElem_centralPlus centralBasisInvolution
    centralBasisInvolution_mul_self

/-- The negative central element is idempotent. -/
theorem centralMinus_isIdempotentElem :
    IsIdempotentElem centralMinus :=
  CentralInvolution.isIdempotentElem_centralMinus centralBasisInvolution
    centralBasisInvolution_mul_self

/-- The positive central element annihilates the negative element. -/
theorem centralPlus_mul_centralMinus :
    centralPlus * centralMinus = 0 :=
  CentralInvolution.centralPlus_mul_centralMinus centralBasisInvolution
    centralBasisInvolution_mul_self

/-- The negative central element annihilates the positive element. -/
theorem centralMinus_mul_centralPlus :
    centralMinus * centralPlus = 0 :=
  CentralInvolution.centralMinus_mul_centralPlus centralBasisInvolution
    centralBasisInvolution_mul_self

/-- The positive and negative central elements add to 1. -/
theorem centralPlus_add_centralMinus :
    centralPlus + centralMinus = 1 :=
  CentralInvolution.centralPlus_add_centralMinus centralBasisInvolution

/-- The positive idempotent lies in the center of the real Group Algebra. -/
theorem centralPlus_mem_center :
    centralPlus ∈ Set.center RealGroupAlgebra :=
  CentralInvolution.centralPlus_mem_center centralBasisInvolution
    centralBasisInvolution_mem_center

/-- The negative idempotent lies in the center of the real Group Algebra. -/
theorem centralMinus_mem_center :
    centralMinus ∈ Set.center RealGroupAlgebra :=
  CentralInvolution.centralMinus_mem_center centralBasisInvolution
    centralBasisInvolution_mem_center

/-- Left multiplication by the positive central idempotent. -/
noncomputable def plusProjection :
    Module.End RealGroupAlgebra RealGroupAlgebra :=
  CentralInvolution.plusProjection centralBasisInvolution
    centralBasisInvolution_mem_center (R := ℝ)

/-- Left multiplication by the negative central idempotent. -/
noncomputable def minusProjection :
    Module.End RealGroupAlgebra RealGroupAlgebra :=
  CentralInvolution.minusProjection centralBasisInvolution
    centralBasisInvolution_mem_center (R := ℝ)

/-- The positive and negative projections add to the identity. -/
theorem plusProjection_add_minusProjection :
    plusProjection + minusProjection = 1 :=
  CentralInvolution.plusProjection_add_minusProjection centralBasisInvolution
    centralBasisInvolution_mem_center (R := ℝ) (M := RealGroupAlgebra)

/-- The positive and negative projection ranges are complementary. -/
theorem isCompl_projection_ranges :
    IsCompl (LinearMap.range plusProjection)
      (LinearMap.range minusProjection) :=
  CentralInvolution.isCompl_range_plusProjection_range_minusProjection
    centralBasisInvolution centralBasisInvolution_mem_center
    centralBasisInvolution_mul_self (R := ℝ) (M := RealGroupAlgebra)

/-- The faithful quaternionic realization of the abstract binary tetrahedral
group, extended linearly to its real Group Algebra. -/
@[no_expose]
noncomputable def abstractQuaternionAlgebraMap : RealGroupAlgebra →ₐ[ℝ] ℍ[ℝ] :=
  MonoidAlgebra.lift ℝ (ℍ[ℝ]) Abstract
    ((Units.coeHom (ℍ[ℝ])).comp quaternionRealization)

/-- The quaternionic algebra map sends a Group-Algebra basis element to its
value under the abstract quaternionic realization. -/
@[simp]
theorem abstractQuaternionAlgebraMap_of (g : Abstract) :
    abstractQuaternionAlgebraMap (MonoidAlgebra.of ℝ Abstract g) =
      (quaternionRealization g : ℍ[ℝ]) :=
  MonoidAlgebra.lift_of _ g

/-- The quaternionic algebra map sends a weighted basis element to the same
weight times its quaternionic value. -/
@[simp]
theorem abstractQuaternionAlgebraMap_single (g : Abstract) (r : ℝ) :
    abstractQuaternionAlgebraMap (MonoidAlgebra.single g r) =
      r • (quaternionRealization g : ℍ[ℝ]) :=
  MonoidAlgebra.lift_single _ g r

/-- The distinguished Group-Algebra basis involution maps to the quaternion
`-1`. -/
@[simp]
theorem abstractQuaternionAlgebraMap_centralBasisInvolution :
    abstractQuaternionAlgebraMap centralBasisInvolution = -1 := by
  rw [centralBasisInvolution, abstractQuaternionAlgebraMap_of,
    quaternionRealization_centralInvolution]
  rfl

/-- The positive central idempotent maps to zero. -/
@[simp]
theorem abstractQuaternionAlgebraMap_centralPlus :
    abstractQuaternionAlgebraMap centralPlus = 0 := by
  simp [centralPlus, CentralInvolution.centralPlus]

/-- The negative central idempotent maps to one. -/
@[simp]
theorem abstractQuaternionAlgebraMap_centralMinus :
    abstractQuaternionAlgebraMap centralMinus = 1 := by
  have h := congrArg abstractQuaternionAlgebraMap
    centralPlus_add_centralMinus
  simpa using h

/-- The quaternionic algebra map vanishes after the positive projection. -/
@[simp]
theorem abstractQuaternionAlgebraMap_plusProjection (x : RealGroupAlgebra) :
    abstractQuaternionAlgebraMap (plusProjection x) = 0 := by
  change abstractQuaternionAlgebraMap (centralPlus * x) = 0
  rw [map_mul, abstractQuaternionAlgebraMap_centralPlus, zero_mul]

/-- The quaternionic algebra map equals its value on the negative projection. -/
theorem abstractQuaternionAlgebraMap_eq_minusProjection (x : RealGroupAlgebra) :
    abstractQuaternionAlgebraMap x =
      abstractQuaternionAlgebraMap (minusProjection x) := by
  change abstractQuaternionAlgebraMap x =
    abstractQuaternionAlgebraMap (centralMinus * x)
  rw [map_mul, abstractQuaternionAlgebraMap_centralMinus, one_mul]

private noncomputable def abstractQuaternionPreimage
    (q : quaternionSubgroup) : Abstract :=
  abstractEquiv.symm
    ⟨q, quaternionSubgroup_le_binaryTetrahedral q.property⟩

@[simp]
private theorem quaternionRealization_abstractQuaternionPreimage
    (q : quaternionSubgroup) :
    (quaternionRealization (abstractQuaternionPreimage q) : ℍ[ℝ]) =
      (q.1 : ℍ[ℝ]) := by
  rw [abstractQuaternionPreimage, quaternionRealization_eq_abstractEquiv,
    MulEquiv.apply_symm_apply]

/-- The quaternionic algebra map is surjective. Explicit preimages are built
from the abstract elements corresponding to the quaternion basis
`1`, `i`, `j`, and `k`. -/
theorem abstractQuaternionAlgebraMap_surjective :
    Function.Surjective abstractQuaternionAlgebraMap := by
  intro q
  let x : RealGroupAlgebra :=
    MonoidAlgebra.single (abstractQuaternionPreimage 1) q.re +
      MonoidAlgebra.single (abstractQuaternionPreimage quaternionSubgroupI) q.imI +
      MonoidAlgebra.single (abstractQuaternionPreimage quaternionSubgroupJ) q.imJ +
      MonoidAlgebra.single
        (abstractQuaternionPreimage (quaternionSubgroupI * quaternionSubgroupJ)) q.imK
  refine ⟨x, ?_⟩
  simp only [x, map_add, abstractQuaternionAlgebraMap_single,
    quaternionRealization_abstractQuaternionPreimage]
  ext <;>
    simp [quaternionSubgroupI, quaternionSubgroupJ, quaternionI, quaternionJ,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

end BinaryTetrahedral
