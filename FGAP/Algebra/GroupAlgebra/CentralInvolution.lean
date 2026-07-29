/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.Algebra.CentralInvolution
public import FGAP.Algebra.GroupAlgebra.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Central involutions in Group Algebras

A central square-one group element gives a central square-one basis element in
its Group Algebra. The generic construction in `FGAP.Algebra.CentralInvolution`
therefore supplies two complementary central idempotents.

See Forest notes `fgap-000X` and `fgap-0011`. The distinction between a group
element and its Group-Algebra basis element follows Ambar N. Sengupta,
*Representations of Algebras and Finite Groups*, Sections 3.1–3.3.
-/

@[expose] public section

open scoped MonoidAlgebra Ring

namespace GroupAlgebra

variable {R G : Type*} [CommRing R] [Group G] [Invertible (2 : R)]

/-- The positive central element associated with a group element. -/
noncomputable def centralPlus (z : G) : R[G] :=
  CentralInvolution.centralPlus R (MonoidAlgebra.of R G z)

/-- The negative central element associated with a group element. -/
noncomputable def centralMinus (z : G) : R[G] :=
  CentralInvolution.centralMinus R (MonoidAlgebra.of R G z)

omit [Invertible (2 : R)] in
theorem of_mul_self (z : G) (hz2 : z * z = 1) :
    MonoidAlgebra.of R G z * MonoidAlgebra.of R G z = 1 := by
  rw [← map_mul, hz2, map_one]

omit [Invertible (2 : R)] in
theorem of_mem_center (z : G) (hz : z ∈ Set.center G) :
    MonoidAlgebra.of R G z ∈ Set.center R[G] :=
  Semigroup.mem_center_iff.mpr fun f =>
    (MonoidAlgebra.of_commute (fun g ↦ hz.comm g) f).eq.symm

theorem centralPlus_add_centralMinus (z : G) :
    centralPlus (R := R) z + centralMinus (R := R) z = 1 :=
  CentralInvolution.centralPlus_add_centralMinus (R := R) (MonoidAlgebra.of R G z)

theorem centralPlus_isIdempotentElem (z : G) (hz2 : z * z = 1) :
    IsIdempotentElem (centralPlus (R := R) z) :=
  CentralInvolution.centralPlus_isIdempotentElem (R := R) _
    (of_mul_self (R := R) z hz2)

theorem centralMinus_isIdempotentElem (z : G) (hz2 : z * z = 1) :
    IsIdempotentElem (centralMinus (R := R) z) :=
  CentralInvolution.centralMinus_isIdempotentElem (R := R) _
    (of_mul_self (R := R) z hz2)

theorem centralPlus_mul_centralMinus (z : G) (hz2 : z * z = 1) :
    centralPlus (R := R) z * centralMinus (R := R) z = 0 :=
  CentralInvolution.centralPlus_mul_centralMinus (R := R) _
    (of_mul_self (R := R) z hz2)

theorem centralMinus_mul_centralPlus (z : G) (hz2 : z * z = 1) :
    centralMinus (R := R) z * centralPlus (R := R) z = 0 :=
  CentralInvolution.centralMinus_mul_centralPlus (R := R) _
    (of_mul_self (R := R) z hz2)

theorem centralPlus_mem_center (z : G) (hz : z ∈ Set.center G) :
    centralPlus (R := R) z ∈ Set.center R[G] :=
  CentralInvolution.centralPlus_mem_center (R := R) _ (of_mem_center (R := R) z hz)

theorem centralMinus_mem_center (z : G) (hz : z ∈ Set.center G) :
    centralMinus (R := R) z ∈ Set.center R[G] :=
  CentralInvolution.centralMinus_mem_center (R := R) _ (of_mem_center (R := R) z hz)

section C2

/-- The nonidentity element of the cyclic group of order two. -/
def c2Generator : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd 1

theorem c2Generator_mul_self : c2Generator * c2Generator = 1 := by
  change (1 : ZMod 2) + 1 = 0
  decide

theorem c2Generator_mem_center : c2Generator ∈ Set.center (Multiplicative (ZMod 2)) :=
  Semigroup.mem_center_iff.mpr fun g => mul_comm g c2Generator

theorem c2_centralPlus_isIdempotentElem :
    IsIdempotentElem (centralPlus (R := R) c2Generator) :=
  centralPlus_isIdempotentElem (R := R) c2Generator c2Generator_mul_self

theorem c2_centralMinus_isIdempotentElem :
    IsIdempotentElem (centralMinus (R := R) c2Generator) :=
  centralMinus_isIdempotentElem (R := R) c2Generator c2Generator_mul_self

theorem c2_centralPlus_mul_centralMinus :
    centralPlus (R := R) c2Generator * centralMinus (R := R) c2Generator = 0 :=
  centralPlus_mul_centralMinus (R := R) c2Generator c2Generator_mul_self

end C2

end GroupAlgebra
