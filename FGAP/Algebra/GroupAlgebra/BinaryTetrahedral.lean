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
ranges.

The mathematics is developed in Forest notes `fgap-0014` and `fgap-0015`.

## Main declarations

* `BinaryTetrahedral.centralPlus` and `BinaryTetrahedral.centralMinus` are the
  complementary central idempotents.
* `BinaryTetrahedral.plusProjection` and
  `BinaryTetrahedral.minusProjection` are their actions on the regular module.
* `BinaryTetrahedral.isCompl_projection_ranges` proves that the 2 ranges are
  complementary.
-/

@[expose] public section

open scoped MonoidAlgebra Ring

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

end BinaryTetrahedral
