/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.Algebra.GroupAlgebra.QuaternionDecomposition

import Mathlib.Algebra.Algebra.Subalgebra.Prod
import Mathlib.Tactic.Linarith

/-!
# Center of the real quaternion group algebra

The explicit real-algebra decomposition

`ℝ[Q₈] ≃ₐ[ℝ] (QuaternionCharacterIndex → ℝ) × ℍ[ℝ]`

identifies the center with the 4 real character coordinates together with the
real scalar coordinate in the quaternion factor. This gives the typed form

`Z(ℝ[Q₈]) ≃ₐ[ℝ] (QuaternionCharacterIndex → ℝ) × ℝ`

of the 5-real-factor center calculation.

## Main declarations

* `BinaryTetrahedral.quaternionGroupAlgebraCenterEquiv`: the center equivalence.
* `BinaryTetrahedral.quaternionGroupAlgebraCenterEquiv_apply`: its coordinates.

## References

* Forest note `fgap-000O`.
  <https://github.com/utensil/forest/tree/fgap>
* Forest note `fgap-001B`.
  <https://github.com/utensil/forest/tree/fgap>
-/

public section

open scoped Quaternion

namespace BinaryTetrahedral

noncomputable section

private theorem quaternion_mem_center_eq_re
    (q : ℍ[ℝ]) (hq : q ∈ Subalgebra.center ℝ ℍ[ℝ]) :
    q = q.re := by
  have hI := Subalgebra.mem_center_iff.mp hq
    (⟨0, 1, 0, 0⟩ : ℍ[ℝ])
  have hJ := Subalgebra.mem_center_iff.mp hq
    (⟨0, 0, 1, 0⟩ : ℍ[ℝ])
  have hImJ := congrArg (fun x : ℍ[ℝ] => x.imJ) hI
  have hImKI := congrArg (fun x : ℍ[ℝ] => x.imK) hI
  have hImKJ := congrArg (fun x : ℍ[ℝ] => x.imK) hJ
  simp only [Quaternion.imJ_mul, Quaternion.imK_mul] at hImJ hImKI hImKJ
  have hqI : q.imI = 0 := by linarith
  have hqJ : q.imJ = 0 := by linarith
  have hqK : q.imK = 0 := by linarith
  ext <;> simp [hqI, hqJ, hqK]

private theorem quaternion_center_eq_bot :
    Subalgebra.center ℝ ℍ[ℝ] = ⊥ :=
  eq_bot_iff.mpr fun q hq => by
    rw [Algebra.mem_bot]
    exact ⟨q.re, (quaternion_mem_center_eq_re q hq).symm⟩

private noncomputable def quaternionCenterEquiv :
    Subalgebra.center ℝ ℍ[ℝ] ≃ₐ[ℝ] ℝ :=
  (Subalgebra.equivOfEq _ _ quaternion_center_eq_bot).trans
    (Algebra.botEquiv ℝ ℍ[ℝ])

@[simp]
private theorem quaternionCenterEquiv_apply
    (q : Subalgebra.center ℝ ℍ[ℝ]) :
    quaternionCenterEquiv q = q.1.re := by
  have h := congrArg Subtype.val (quaternionCenterEquiv.symm_apply_apply q)
  have hre := congrArg (fun x : ℍ[ℝ] => x.re) h
  change quaternionCenterEquiv q = q.1.re at hre
  exact hre

private theorem center_map_algEquiv
    {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring B] [Algebra R B] (e : A ≃ₐ[R] B) :
    (Subalgebra.center R A).map e.toAlgHom = Subalgebra.center R B := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    change a ∈ Subalgebra.center R A at ha
    change e a ∈ Subalgebra.center R B
    rw [Subalgebra.mem_center_iff] at ha ⊢
    intro b
    obtain ⟨b, rfl⟩ := e.surjective b
    simpa using congrArg e (ha b)
  · intro b hb
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    change b ∈ Subalgebra.center R B at hb
    change e.symm b ∈ Subalgebra.center R A
    rw [Subalgebra.mem_center_iff] at hb ⊢
    intro a
    apply e.injective
    simpa using hb (e a)

private noncomputable def centerEquivOfAlgEquiv
    {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring B] [Algebra R B] (e : A ≃ₐ[R] B) :
    Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B :=
  (e.subalgebraMap (Subalgebra.center R A)).trans
    (Subalgebra.equivOfEq _ _ (center_map_algEquiv e))

private def subalgebraProdEquiv
    {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring B] [Algebra R B]
    (S : Subalgebra R A) (T : Subalgebra R B) :
    S.prod T ≃ₐ[R] S × T where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The center of the real quaternion group algebra is the product of its 4
real-character coordinates and the real center of the quaternion factor. -/
noncomputable def quaternionGroupAlgebraCenterEquiv :
    Subalgebra.center ℝ QuaternionGroupAlgebra ≃ₐ[ℝ]
      (QuaternionCharacterIndex → ℝ) × ℝ :=
  (centerEquivOfAlgEquiv quaternionRealBlocksEquiv).trans <|
    (Subalgebra.equivOfEq _ _ Subalgebra.center_prod).trans <|
      (subalgebraProdEquiv
        (Subalgebra.center ℝ (QuaternionCharacterIndex → ℝ))
        (Subalgebra.center ℝ ℍ[ℝ])).trans <|
        AlgEquiv.prodCongr
          ((Subalgebra.equivOfEq _ _
            (Subalgebra.center_eq_top (R := ℝ)
              (QuaternionCharacterIndex → ℝ))).trans
              Subalgebra.topEquiv)
          quaternionCenterEquiv

/-- The center equivalence retains the character coordinates and takes the
real part of the quaternion coordinate. -/
@[simp]
theorem quaternionGroupAlgebraCenterEquiv_apply
    (z : Subalgebra.center ℝ QuaternionGroupAlgebra) :
    quaternionGroupAlgebraCenterEquiv z =
      ((quaternionRealBlocksEquiv z.1).1,
        (quaternionRealBlocksEquiv z.1).2.re) := by
  simp [quaternionGroupAlgebraCenterEquiv, centerEquivOfAlgEquiv,
    subalgebraProdEquiv]

end

end BinaryTetrahedral
