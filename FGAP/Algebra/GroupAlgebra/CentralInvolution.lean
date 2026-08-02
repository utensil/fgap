/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.Algebra.CentralInvolution
public import FGAP.Algebra.GroupAlgebra.Basic

/-!
# Central involutions in Group Algebras

A central square-one group element gives a central square-one basis element in
its Group Algebra. The generic construction in `FGAP.Algebra.CentralInvolution`
therefore supplies two complementary central idempotents.

See Forest notes `fgap-000X` and `fgap-000Y`. The distinction between a group
element and its Group-Algebra basis element follows Ambar N. Sengupta,
*Representations of Algebras and Finite Groups*, Sections 3.1–3.3.

## Main declarations

* `GroupAlgebra.centralPlus` and `GroupAlgebra.centralMinus` specialize the
  generic complementary elements to a Group-Algebra basis element.
* `GroupAlgebra.isIdempotentElem_centralPlus` and
  `GroupAlgebra.isIdempotentElem_centralMinus` provide the resulting
  idempotents.
-/

@[expose] public section

open scoped MonoidAlgebra Ring

namespace GroupAlgebra

variable {R G : Type*} [CommRing R] [Group G] [Invertible (2 : R)]

/-- The positive Group-Algebra element associated with a group element. -/
noncomputable def centralPlus (z : G) : R[G] :=
  CentralInvolution.centralPlus R (MonoidAlgebra.of R G z)

/-- The negative Group-Algebra element associated with a group element. -/
noncomputable def centralMinus (z : G) : R[G] :=
  CentralInvolution.centralMinus R (MonoidAlgebra.of R G z)

omit [Invertible (2 : R)] in
/-- A square-one group element maps to a square-one Group-Algebra basis element. -/
theorem of_mul_self_eq_one (z : G) (hz2 : z * z = 1) :
    MonoidAlgebra.of R G z * MonoidAlgebra.of R G z = 1 := by
  rw [← map_mul, hz2, map_one]

omit [Invertible (2 : R)] in
/-- A central group element maps to a central Group-Algebra basis element. -/
theorem of_mem_center (z : G) (hz : z ∈ Set.center G) :
    MonoidAlgebra.of R G z ∈ Set.center R[G] :=
  Semigroup.mem_center_iff.mpr fun f =>
    (MonoidAlgebra.of_commute (fun g ↦ hz.comm g) f).eq.symm

/-- The positive and negative Group-Algebra elements add to 1. -/
theorem centralPlus_add_centralMinus (z : G) :
    centralPlus (R := R) z + centralMinus (R := R) z = 1 :=
  CentralInvolution.centralPlus_add_centralMinus (R := R) (MonoidAlgebra.of R G z)

/-- The positive Group-Algebra element is idempotent when `z` squares to 1. -/
theorem isIdempotentElem_centralPlus (z : G) (hz2 : z * z = 1) :
    IsIdempotentElem (centralPlus (R := R) z) :=
  CentralInvolution.isIdempotentElem_centralPlus (R := R) _
    (of_mul_self_eq_one (R := R) z hz2)

/-- The negative Group-Algebra element is idempotent when `z` squares to 1. -/
theorem isIdempotentElem_centralMinus (z : G) (hz2 : z * z = 1) :
    IsIdempotentElem (centralMinus (R := R) z) :=
  CentralInvolution.isIdempotentElem_centralMinus (R := R) _
    (of_mul_self_eq_one (R := R) z hz2)

/-- The positive Group-Algebra element annihilates the negative element. -/
theorem centralPlus_mul_centralMinus (z : G) (hz2 : z * z = 1) :
    centralPlus (R := R) z * centralMinus (R := R) z = 0 :=
  CentralInvolution.centralPlus_mul_centralMinus (R := R) _
    (of_mul_self_eq_one (R := R) z hz2)

/-- The negative Group-Algebra element annihilates the positive element. -/
theorem centralMinus_mul_centralPlus (z : G) (hz2 : z * z = 1) :
    centralMinus (R := R) z * centralPlus (R := R) z = 0 :=
  CentralInvolution.centralMinus_mul_centralPlus (R := R) _
    (of_mul_self_eq_one (R := R) z hz2)

/-- The positive Group-Algebra element is central when `z` is central. -/
theorem centralPlus_mem_center (z : G) (hz : z ∈ Set.center G) :
    centralPlus (R := R) z ∈ Set.center R[G] :=
  CentralInvolution.centralPlus_mem_center (R := R) _ (of_mem_center (R := R) z hz)

/-- The negative Group-Algebra element is central when `z` is central. -/
theorem centralMinus_mem_center (z : G) (hz : z ∈ Set.center G) :
    centralMinus (R := R) z ∈ Set.center R[G] :=
  CentralInvolution.centralMinus_mem_center (R := R) _ (of_mem_center (R := R) z hz)

end GroupAlgebra
