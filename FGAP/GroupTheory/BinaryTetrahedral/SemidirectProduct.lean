/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.GroupTheory.BinaryTetrahedral.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# A semidirect-product presentation of the binary tetrahedral subgroup

This file presents the concrete binary tetrahedral subgroup as an external
semidirect product. Its action is conjugation by the internal Hurwitz factor
on the normal quaternion factor.

## Main declarations

* `BinaryTetrahedral.semidirectProductAction`: the conjugation action of the
  internal Hurwitz factor.
* `BinaryTetrahedral.semidirectProductEquiv`: the multiplication equivalence
  from the external semidirect product to the concrete subgroup.

## References

* John Voight, *Quaternion Algebras*, §11.2.4, p. 168.
  <https://doi.org/10.1007/978-3-030-56694-4>
* Forest notes `fgap-000E` through `fgap-000L`.
-/

public section

namespace BinaryTetrahedral

noncomputable section

/-- Conjugation by the internal Hurwitz factor on the internal quaternion
factor. -/
abbrev semidirectProductAction :
    binaryTetrahedralCyclic →* MulAut binaryTetrahedralQuaternion :=
  (binaryTetrahedralQuaternion.normalizerMonoidHom).comp
    (Subgroup.inclusion
      (binaryTetrahedralQuaternion.normalizer_eq_top ▸ le_top))

/-- The external semidirect product determined by Hurwitz conjugation is
equivalent to the concrete binary tetrahedral subgroup. The source consists
of pairs of internal-factor elements; the target is the concrete
`binaryTetrahedral` subgroup. -/
@[expose]
noncomputable def semidirectProductEquiv :
    binaryTetrahedralQuaternion ⋊[semidirectProductAction]
      binaryTetrahedralCyclic ≃* binaryTetrahedral :=
  SemidirectProduct.mulEquivSubgroup binaryTetrahedral_isComplement

/-- The semidirect-product equivalence maps a pair of factors to their product. -/
@[simp]
theorem semidirectProductEquiv_apply
    (x : binaryTetrahedralQuaternion ⋊[semidirectProductAction]
      binaryTetrahedralCyclic) :
    semidirectProductEquiv x =
      (x.left : binaryTetrahedral) * (x.right : binaryTetrahedral) :=
  rfl

end

end BinaryTetrahedral
