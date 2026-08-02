/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Quaternion-group universal mapping interface

This module temporarily stages a universal mapping interface for generalized
quaternion groups. It should be deleted, with its consumers switched
atomically, when the pinned mathlib revision provides equivalent declarations.

## Main declarations

* `QuaternionGroup.lift`: the homomorphism determined by images of the 2
  presentation generators.
* `QuaternionGroup.hom_ext`: homomorphisms out of a quaternion group agree
  when they agree on the 2 generators.
* `QuaternionGroup.lift_unique`: uniqueness of the lifted homomorphism.
-/

@[expose] public section

namespace QuaternionGroup

variable {n : ℕ} {G : Type*} [Group G]

private noncomputable def liftCyclicData (a : G) (ha : a ^ (2 * n) = 1) :
    { f : ℤ →+ Additive G // f (2 * n) = 0 } :=
  ⟨zmultiplesHom (Additive G) (Additive.ofMul a), by
    rw [zmultiplesHom_apply]
    change Additive.ofMul (a ^ ((2 * n : ℕ) : ℤ)) = 0
    rw [zpow_natCast, ha]
    rfl⟩

private noncomputable def liftCyclicHomAdd (a : G) (ha : a ^ (2 * n) = 1) :
    ZMod (2 * n) →+ Additive G :=
  ZMod.lift (2 * n) (liftCyclicData a ha)

set_option backward.privateInPublic true in
private noncomputable def liftCyclicHom (a : G) (ha : a ^ (2 * n) = 1) :
    Multiplicative (ZMod (2 * n)) →* G :=
  (liftCyclicHomAdd a ha).toMultiplicativeLeft

set_option backward.privateInPublic true in
@[simp]
private theorem liftCyclicHom_intCast (a : G) (ha : a ^ (2 * n) = 1) (m : ℤ) :
    liftCyclicHom a ha (Multiplicative.ofAdd (m : ZMod (2 * n))) = a ^ m := by
  change Additive.toMul (liftCyclicHomAdd a ha (m : ZMod (2 * n))) = a ^ m
  have h : liftCyclicHomAdd a ha (m : ZMod (2 * n)) = Additive.ofMul (a ^ m) := by
    rw [liftCyclicHomAdd, ZMod.lift_coe]
    simp [liftCyclicData, zmultiplesHom_apply]
  rw [h]
  rfl

private theorem lift_generator_commutation (a x : G) (hconj : x⁻¹ * a * x = a⁻¹) :
    a * x = x * a⁻¹ := by
  calc
    a * x = x * (x⁻¹ * a * x) := by simp [mul_assoc]
    _ = x * a⁻¹ := congrArg (x * ·) hconj

private theorem lift_generator_commutation_zpow (a x : G)
    (hconj : x⁻¹ * a * x = a⁻¹) (m : ℤ) :
    a ^ m * x = x * a ^ (-m) := by
  have hax : a * x = x * a⁻¹ := lift_generator_commutation a x hconj
  have hsemi : SemiconjBy x a⁻¹ a := hax.symm
  simpa [SemiconjBy, inv_zpow] using (hsemi.zpow_right m).symm

set_option backward.privateInPublic true in
private theorem liftCyclicHom_commutation (a x : G) (ha : a ^ (2 * n) = 1)
    (hconj : x⁻¹ * a * x = a⁻¹) (r : ZMod (2 * n)) :
    liftCyclicHom a ha (Multiplicative.ofAdd r) * x =
      x * liftCyclicHom a ha (Multiplicative.ofAdd (-r)) := by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective r
  simpa using lift_generator_commutation_zpow a x hconj m

set_option backward.privateInPublic true in
private def liftCyclic (f : Multiplicative (ZMod (2 * n)) →* G) (x : G)
    (hsq : x * x = f (Multiplicative.ofAdd (n : ZMod (2 * n))))
    (hcomm : ∀ r, f (Multiplicative.ofAdd r) * x =
      x * f (Multiplicative.ofAdd (-r))) : QuaternionGroup n →* G where
  toFun
    | QuaternionGroup.a r => f (Multiplicative.ofAdd r)
    | QuaternionGroup.xa r => x * f (Multiplicative.ofAdd r)
  map_one' := by
    change f (Multiplicative.ofAdd (0 : ZMod (2 * n))) = 1
    exact map_one f
  map_mul' := by
    rintro (r | r) (s | s)
    · exact map_mul f _ _
    · simp only [QuaternionGroup.a_mul_xa]
      rw [← mul_assoc, hcomm, mul_assoc, ← map_mul f]
      apply congrArg (x * ·)
      apply congrArg f
      apply Multiplicative.toAdd.injective
      change s - r = -r + s
      simp [sub_eq_add_neg, add_comm]
    · simp only [QuaternionGroup.xa_mul_a]
      rw [mul_assoc]
      apply congrArg (x * ·)
      rw [← map_mul f]
      rfl
    · simp only [QuaternionGroup.xa_mul_xa]
      rw [mul_assoc x, ← mul_assoc (f (Multiplicative.ofAdd r)), hcomm,
        ← mul_assoc x (x * f (Multiplicative.ofAdd (-r))), ← mul_assoc x x, hsq,
        ← map_mul f, ← map_mul f]
      apply congrArg f
      apply Multiplicative.toAdd.injective
      change n + s - r = n + -r + s
      simp [sub_eq_add_neg, add_comm, add_assoc]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The homomorphism from `QuaternionGroup n` determined by elements `a` and
`x` satisfying the standard presentation relations. -/
noncomputable def lift (a x : G) (ha : a ^ (2 * n) = 1)
    (hx : x ^ 2 = a ^ n) (hconj : x⁻¹ * a * x = a⁻¹) :
    QuaternionGroup n →* G :=
  liftCyclic (liftCyclicHom a ha) x
    (by
      rw [← pow_two, hx]
      simpa [zpow_natCast] using (liftCyclicHom_intCast a ha (n : ℤ)).symm)
    (liftCyclicHom_commutation a x ha hconj)

@[simp]
private theorem lift_a (a x : G) (ha : a ^ (2 * n) = 1)
    (hx : x ^ 2 = a ^ n) (hconj : x⁻¹ * a * x = a⁻¹)
    (r : ZMod (2 * n)) :
    lift a x ha hx hconj (QuaternionGroup.a r) =
      liftCyclicHom a ha (Multiplicative.ofAdd r) := rfl

@[simp]
private theorem lift_xa (a x : G) (ha : a ^ (2 * n) = 1)
    (hx : x ^ 2 = a ^ n) (hconj : x⁻¹ * a * x = a⁻¹)
    (r : ZMod (2 * n)) :
    lift a x ha hx hconj (QuaternionGroup.xa r) =
      x * liftCyclicHom a ha (Multiplicative.ofAdd r) := rfl

/-- The lift sends an integral power of the cyclic generator to the same
power of its prescribed image. -/
@[simp]
theorem lift_a_intCast (a x : G) (ha : a ^ (2 * n) = 1)
    (hx : x ^ 2 = a ^ n) (hconj : x⁻¹ * a * x = a⁻¹) (m : ℤ) :
    lift a x ha hx hconj (QuaternionGroup.a (m : ZMod (2 * n))) = a ^ m := by
  exact liftCyclicHom_intCast a ha m

/-- The lift sends a reflected integral power to the image of `x` times the
corresponding power of the image of `a`. -/
@[simp]
theorem lift_xa_intCast (a x : G) (ha : a ^ (2 * n) = 1)
    (hx : x ^ 2 = a ^ n) (hconj : x⁻¹ * a * x = a⁻¹) (m : ℤ) :
    lift a x ha hx hconj (QuaternionGroup.xa (m : ZMod (2 * n))) = x * a ^ m := by
  rw [lift_xa, liftCyclicHom_intCast]

/-- The lift sends the cyclic presentation generator to its prescribed image. -/
@[simp]
theorem lift_a_one (a x : G) (ha : a ^ (2 * n) = 1)
    (hx : x ^ 2 = a ^ n) (hconj : x⁻¹ * a * x = a⁻¹) :
    lift a x ha hx hconj (QuaternionGroup.a 1) = a := by
  simpa using lift_a_intCast a x ha hx hconj 1

/-- The lift sends the second presentation generator to its prescribed image. -/
@[simp]
theorem lift_xa_zero (a x : G) (ha : a ^ (2 * n) = 1)
    (hx : x ^ 2 = a ^ n) (hconj : x⁻¹ * a * x = a⁻¹) :
    lift a x ha hx hconj (QuaternionGroup.xa 0) = x := by
  rw [lift_xa]
  change x * liftCyclicHom a ha 1 = x
  rw [map_one, mul_one]

private theorem lift_inv_a (r : ZMod (2 * n)) :
    (QuaternionGroup.a r)⁻¹ = QuaternionGroup.a (-r) := by
  apply inv_eq_of_mul_eq_one_right
  simp

private theorem lift_a_one_zpow (m : ℤ) :
    (QuaternionGroup.a 1 : QuaternionGroup n) ^ m = QuaternionGroup.a m := by
  cases m with
  | ofNat k => simp [zpow_natCast]
  | negSucc k =>
      simp only [zpow_negSucc, QuaternionGroup.a_one_pow, lift_inv_a]
      congr
      norm_cast

/-- 2 homomorphisms out of a generalized quaternion group are equal if they
agree on the 2 presentation generators. -/
@[ext high]
theorem hom_ext {f g : QuaternionGroup n →* G}
    (ha : f (QuaternionGroup.a 1) = g (QuaternionGroup.a 1))
    (hx : f (QuaternionGroup.xa 0) = g (QuaternionGroup.xa 0)) : f = g := by
  apply MonoidHom.ext
  rintro (r | r)
  · obtain ⟨m, rfl⟩ := ZMod.intCast_surjective r
    rw [← lift_a_one_zpow, map_zpow, map_zpow, ha]
  · have hdecomp : QuaternionGroup.xa r = QuaternionGroup.xa 0 * QuaternionGroup.a r := by
      simp
    rw [hdecomp, map_mul, map_mul, hx]
    congr 1
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective r
    rw [← lift_a_one_zpow, map_zpow, map_zpow, ha]

/-- The lift is the unique homomorphism with the prescribed values on the 2
presentation generators. -/
theorem lift_unique (a x : G) (ha : a ^ (2 * n) = 1)
    (hx : x ^ 2 = a ^ n) (hconj : x⁻¹ * a * x = a⁻¹)
    (F : QuaternionGroup n →* G)
    (Fa : F (QuaternionGroup.a 1) = a)
    (Fx : F (QuaternionGroup.xa 0) = x) : F = lift a x ha hx hconj := by
  apply hom_ext
  · rw [lift_a_one]
    exact Fa
  · rw [lift_xa_zero]
    exact Fx

end QuaternionGroup
