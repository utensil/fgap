/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.Algebra.GroupAlgebra.CentralInvolution
public import Mathlib.Data.ZMod.Basic

/-!
# The central split for the cyclic group of order two

The nonidentity element of the cyclic group of order 2 is central and
squares to 1. This file uses it to calibrate the complementary central
idempotents in its Group Algebra.

See Forest note `fgap-0011` for the complete algebra isomorphism
`R[C₂] ≃ₐ[R] R × R`.

## Main declarations

* `GroupAlgebra.c2Generator` is the nonidentity element of the cyclic group of
  order 2.
* `GroupAlgebra.isIdempotentElem_c2_centralPlus` and
  `GroupAlgebra.isIdempotentElem_c2_centralMinus` specialize the generic
  idempotence results.
-/

@[expose] public section

open scoped MonoidAlgebra Ring

namespace GroupAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The nonidentity element of the cyclic group of order 2. -/
def c2Generator : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd 1

/-- The nonidentity element of the cyclic group of order 2 squares to 1. -/
theorem c2Generator_mul_self : c2Generator * c2Generator = 1 := by
  change (1 : ZMod 2) + 1 = 0
  decide

/-- The nonidentity element of the cyclic group of order 2 is central. -/
theorem c2Generator_mem_center : c2Generator ∈ Set.center (Multiplicative (ZMod 2)) :=
  Semigroup.mem_center_iff.mpr fun g => mul_comm g c2Generator

/-- The positive central element for `C₂` is idempotent. -/
theorem isIdempotentElem_c2_centralPlus :
    IsIdempotentElem (centralPlus (R := R) c2Generator) :=
  isIdempotentElem_centralPlus (R := R) c2Generator c2Generator_mul_self

/-- The negative central element for `C₂` is idempotent. -/
theorem isIdempotentElem_c2_centralMinus :
    IsIdempotentElem (centralMinus (R := R) c2Generator) :=
  isIdempotentElem_centralMinus (R := R) c2Generator c2Generator_mul_self

/-- The positive central element for `C₂` annihilates the negative element. -/
theorem c2_centralPlus_mul_centralMinus :
    centralPlus (R := R) c2Generator * centralMinus (R := R) c2Generator = 0 :=
  centralPlus_mul_centralMinus (R := R) c2Generator c2Generator_mul_self

end GroupAlgebra
