/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.GroupTheory.BinaryTetrahedral.SemidirectProduct
public import Mathlib.GroupTheory.Subgroup.Center

import Mathlib.Tactic.NormNum

/-!
# The abstract binary tetrahedral group

This file transports the concrete Hurwitz conjugation action to the standard
abstract factors `QuaternionGroup 2` and `Multiplicative (ZMod 3)`. The
resulting semidirect product is identified with the concrete subgroup of the
invertible real quaternions.

## Main declarations

* `BinaryTetrahedral.abstractAction`: the transported action on the abstract
  quaternion group.
* `BinaryTetrahedral.Abstract`: the canonical abstract semidirect-product
  model.
* `BinaryTetrahedral.abstractEquiv`: its equivalence with the concrete binary
  tetrahedral subgroup.
* `BinaryTetrahedral.centralInvolution`: its central element of order two.

## References

* John Voight, *Quaternion Algebras*, §11.2.4, p. 168.
  <https://doi.org/10.1007/978-3-030-56694-4>
* Forest notes `fgap-000D` and `fgap-000L`.
-/

public section

open scoped Quaternion

namespace BinaryTetrahedral

noncomputable section

/-- The standard quaternion group identified with the internal quaternion
factor of the concrete binary tetrahedral subgroup. -/
noncomputable def quaternionFactorEquiv :
    QuaternionGroup 2 ≃* binaryTetrahedralQuaternion :=
  quaternionGroupEquiv.trans
    (Subgroup.subgroupOfEquivOfLe
      quaternionSubgroup_le_binaryTetrahedral).symm

@[simp]
theorem coe_quaternionFactorEquiv (x : QuaternionGroup 2) :
    ((quaternionFactorEquiv x : binaryTetrahedralQuaternion) :
        binaryTetrahedral) =
      quaternionGroupHom x := by
  rw [quaternionFactorEquiv, MulEquiv.trans_apply]
  change (↑↑((Subgroup.subgroupOfEquivOfLe
    quaternionSubgroup_le_binaryTetrahedral).symm
      (quaternionGroupEquiv x)) : InvertibleQuaternions) =
        quaternionGroupHom x
  rw [
    Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe,
    quaternionGroupEquiv_apply]

/-- The standard cyclic group of order three identified with the internal
Hurwitz factor of the concrete binary tetrahedral subgroup. -/
noncomputable def cyclicFactorEquiv :
    Multiplicative (ZMod 3) ≃* binaryTetrahedralCyclic :=
  hurwitzCyclicEquiv.trans
    (Subgroup.subgroupOfEquivOfLe
      hurwitzCyclic_le_binaryTetrahedral).symm

/-- The Hurwitz conjugation action transported to the standard abstract
factors. -/
abbrev abstractAction :
    Multiplicative (ZMod 3) →* MulAut (QuaternionGroup 2) :=
  (MulAut.congr quaternionFactorEquiv.symm).toMonoidHom.comp
    (semidirectProductAction.comp cyclicFactorEquiv.toMonoidHom)

@[simp]
theorem abstractAction_apply (c : Multiplicative (ZMod 3))
    (q : QuaternionGroup 2) :
    abstractAction c q =
      quaternionFactorEquiv.symm
        (semidirectProductAction (cyclicFactorEquiv c)
          (quaternionFactorEquiv q)) := by
  simp [abstractAction]

/-- The canonical abstract model of the binary tetrahedral group. -/
abbrev Abstract :=
  QuaternionGroup 2 ⋊[abstractAction] Multiplicative (ZMod 3)

/-- The abstract binary tetrahedral group is equivalent to its concrete
internal semidirect-product presentation. -/
@[expose]
noncomputable def abstractFactorEquiv :
    Abstract ≃*
      (binaryTetrahedralQuaternion ⋊[semidirectProductAction]
        binaryTetrahedralCyclic) :=
  (SemidirectProduct.congr'
    quaternionFactorEquiv.symm cyclicFactorEquiv.symm).symm

@[simp]
theorem abstractFactorEquiv_apply (x : Abstract) :
    abstractFactorEquiv x =
      ⟨quaternionFactorEquiv x.left, cyclicFactorEquiv x.right⟩ := by
  apply SemidirectProduct.ext
  · exact SemidirectProduct.congr'_symm_apply_left _ _ _
  · exact SemidirectProduct.congr'_symm_apply_right _ _ _

/-- The abstract binary tetrahedral group is equivalent to its concrete
quaternionic realization. -/
@[expose]
noncomputable def abstractEquiv : Abstract ≃* binaryTetrahedral :=
  abstractFactorEquiv.trans semidirectProductEquiv

@[simp]
theorem abstractEquiv_apply (x : Abstract) :
    abstractEquiv x =
      semidirectProductEquiv
        ⟨quaternionFactorEquiv x.left, cyclicFactorEquiv x.right⟩ := by
  change semidirectProductEquiv (abstractFactorEquiv x) = _
  rw [abstractFactorEquiv_apply]

/-- The faithful realization of the abstract binary tetrahedral group in the
invertible real quaternions. -/
noncomputable def quaternionRealization : Abstract →* InvertibleQuaternions :=
  binaryTetrahedral.subtype.comp abstractEquiv

@[simp]
theorem quaternionRealization_apply (x : Abstract) :
    quaternionRealization x =
      (quaternionFactorEquiv x.left : binaryTetrahedral) *
        (cyclicFactorEquiv x.right : binaryTetrahedral) := by
  calc
    quaternionRealization x = (abstractEquiv x : InvertibleQuaternions) := rfl
    _ = (semidirectProductEquiv
        ⟨quaternionFactorEquiv x.left, cyclicFactorEquiv x.right⟩ :
          InvertibleQuaternions) :=
      congrArg (fun y : binaryTetrahedral => (y : InvertibleQuaternions))
        (abstractEquiv_apply x)
    _ = _ := by rw [semidirectProductEquiv_apply]; rfl

theorem quaternionRealization_injective :
    Function.Injective quaternionRealization :=
  binaryTetrahedral.subtype_injective.comp abstractEquiv.injective

/-- The central involution inherited from the abstract quaternion factor. -/
def centralInvolution : Abstract :=
  SemidirectProduct.inl (QuaternionGroup.a 2)

@[simp]
theorem quaternionRealization_centralInvolution :
    quaternionRealization centralInvolution = -1 := by
  simp [centralInvolution]

/-- The distinguished involution lies in the center of the abstract binary
tetrahedral group. -/
theorem centralInvolution_mem_center :
    centralInvolution ∈ Set.center Abstract := by
  rw [Semigroup.mem_center_iff]
  intro g
  apply quaternionRealization_injective
  rw [map_mul, map_mul, quaternionRealization_centralInvolution]
  apply Units.ext
  simp

@[simp]
theorem centralInvolution_sq :
    centralInvolution ^ 2 = 1 := by
  apply quaternionRealization_injective
  rw [map_pow, quaternionRealization_centralInvolution]
  apply Units.ext
  simp

@[simp]
theorem centralInvolution_ne_one :
    centralInvolution ≠ 1 := by
  intro h
  have h' := congrArg quaternionRealization h
  rw [quaternionRealization_centralInvolution, map_one] at h'
  have h'' := congrArg (fun u : InvertibleQuaternions => (u : ℍ[ℝ]).re) h'
  norm_num at h''

end

end BinaryTetrahedral
