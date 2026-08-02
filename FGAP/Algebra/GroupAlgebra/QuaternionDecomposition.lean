/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.Algebra.GroupAlgebra.QuaternionCharacters
public import Mathlib.Algebra.Algebra.Prod

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Real decomposition of the quaternion group algebra

The 4 real characters recover the sums of coefficients at opposite elements
of `Q₈` by the inverse Hadamard transform. The concrete quaternion
representation recovers their differences. Together these 8 coordinates make
the product of the character and quaternion maps injective, hence bijective by
dimension, and give the real-algebra decomposition

`ℝ[Q₈] ≃ₐ[ℝ] (QuaternionCharacterIndex → ℝ) × ℍ[ℝ]`.

The selected abstract representative of `k` remains
`QuaternionGroup.a 1 * QuaternionGroup.xa 0`, preserving the orientation
`i * j = k`.

## Main declarations

* `BinaryTetrahedral.quaternionCoefficientSum*_inverseHadamard`: recovery of
  the 4 opposite-pair coefficient sums.
* `BinaryTetrahedral.quaternionRealBlocksMap`: the combined character and
  quaternion algebra map.
* `BinaryTetrahedral.quaternionRealBlocksEquiv`: the complete real-algebra
  decomposition.

## References

* Forest note `fgap-001B`.
  <https://github.com/utensil/forest/tree/fgap>
* John Voight, *Quaternion Algebras*, §11.2, p. 166.
  <https://doi.org/10.1007/978-3-030-56694-4>
* Ambar N. Sengupta, *Representing Finite Groups*, §§3.1--3.2, pp. 39--41.
  <https://doi.org/10.1007/978-1-4419-6316-5>
* Pavel Etingof et al., *Introduction to Representation Theory*, §4.3,
  pp. 63--64, and Example 4.8.1, p. 73.
  <https://bookstore.ams.org/stml-59/>
-/

public section

open scoped Quaternion

namespace BinaryTetrahedral

noncomputable section

/-- The inverse Hadamard formula recovering the coefficient-pair sum at
`±1`. -/
theorem quaternionCoefficientSumOne_inverseHadamard
    (x : QuaternionGroupAlgebra) :
    quaternionCoefficientSumOne x =
      (1 / 4 : ℝ) *
        (quaternionCharacterMap x (false, false) +
          quaternionCharacterMap x (true, false) +
          quaternionCharacterMap x (false, true) +
          quaternionCharacterMap x (true, true)) := by
  rw [quaternionCharacterMap_plus_plus, quaternionCharacterMap_minus_plus,
    quaternionCharacterMap_plus_minus, quaternionCharacterMap_minus_minus]
  ring

/-- The inverse Hadamard formula recovering the coefficient-pair sum at
`±i`. -/
theorem quaternionCoefficientSumI_inverseHadamard
    (x : QuaternionGroupAlgebra) :
    quaternionCoefficientSumI x =
      (1 / 4 : ℝ) *
        (quaternionCharacterMap x (false, false) -
          quaternionCharacterMap x (true, false) +
          quaternionCharacterMap x (false, true) -
          quaternionCharacterMap x (true, true)) := by
  rw [quaternionCharacterMap_plus_plus, quaternionCharacterMap_minus_plus,
    quaternionCharacterMap_plus_minus, quaternionCharacterMap_minus_minus]
  ring

/-- The inverse Hadamard formula recovering the coefficient-pair sum at
`±j`. -/
theorem quaternionCoefficientSumJ_inverseHadamard
    (x : QuaternionGroupAlgebra) :
    quaternionCoefficientSumJ x =
      (1 / 4 : ℝ) *
        (quaternionCharacterMap x (false, false) +
          quaternionCharacterMap x (true, false) -
          quaternionCharacterMap x (false, true) -
          quaternionCharacterMap x (true, true)) := by
  rw [quaternionCharacterMap_plus_plus, quaternionCharacterMap_minus_plus,
    quaternionCharacterMap_plus_minus, quaternionCharacterMap_minus_minus]
  ring

/-- The inverse Hadamard formula recovering the coefficient-pair sum at
`±k`, with `k = i * j`. -/
theorem quaternionCoefficientSumK_inverseHadamard
    (x : QuaternionGroupAlgebra) :
    quaternionCoefficientSumK x =
      (1 / 4 : ℝ) *
        (quaternionCharacterMap x (false, false) -
          quaternionCharacterMap x (true, false) -
          quaternionCharacterMap x (false, true) +
          quaternionCharacterMap x (true, true)) := by
  rw [quaternionCharacterMap_plus_plus, quaternionCharacterMap_minus_plus,
    quaternionCharacterMap_plus_minus, quaternionCharacterMap_minus_minus]
  ring

/-- The difference of coefficients at `q` and its central negative `-q`. -/
def quaternionCoefficientPairDifference (q : QuaternionGroup 2)
    (x : QuaternionGroupAlgebra) : ℝ :=
  (MonoidAlgebra.coeff x) (quaternionGroupEquiv q) -
    (MonoidAlgebra.coeff x)
      (quaternionGroupEquiv (QuaternionGroup.a 2 * q))

/-- Expanding a coefficient-pair difference gives the 2 coefficients at `q`
and its central negative `-q`. -/
theorem quaternionCoefficientPairDifference_apply (q : QuaternionGroup 2)
    (x : QuaternionGroupAlgebra) :
    quaternionCoefficientPairDifference q x =
      (MonoidAlgebra.coeff x) (quaternionGroupEquiv q) -
        (MonoidAlgebra.coeff x)
          (quaternionGroupEquiv (QuaternionGroup.a 2 * q)) := by
  rfl

@[simp]
private theorem coeff_of_quaternionGroupEquiv (g h : QuaternionGroup 2) :
    (MonoidAlgebra.coeff
      (MonoidAlgebra.of ℝ quaternionSubgroup (quaternionGroupEquiv g)))
      (quaternionGroupEquiv h) = if g = h then 1 else 0 := by
  classical
  simp [Finsupp.single_apply]

private theorem quaternionAlgebraMap_re_of (g : QuaternionGroup 2) :
    (quaternionAlgebraMap
      (MonoidAlgebra.of ℝ quaternionSubgroup (quaternionGroupEquiv g))).re =
        quaternionCoefficientPairDifference (QuaternionGroup.a 0)
          (MonoidAlgebra.of ℝ quaternionSubgroup (quaternionGroupEquiv g)) := by
  rw [quaternionAlgebraMap_of]
  simp only [quaternionCoefficientPairDifference_apply,
    coeff_of_quaternionGroupEquiv]
  cases g with
  | a r =>
      fin_cases r
      all_goals
        repeat first
          | rw [if_pos (by decide)]
          | rw [if_neg (by decide)]
        norm_num [quaternionGroupHom_a_val, ZMod.val, pow_succ,
          Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul]
  | xa r =>
      fin_cases r
      all_goals
        repeat first
          | rw [if_pos (by decide)]
          | rw [if_neg (by decide)]
        norm_num [quaternionGroupHom_xa_val, ZMod.val, pow_succ,
          Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem quaternionAlgebraMap_imI_of (g : QuaternionGroup 2) :
    (quaternionAlgebraMap
      (MonoidAlgebra.of ℝ quaternionSubgroup (quaternionGroupEquiv g))).imI =
        quaternionCoefficientPairDifference (QuaternionGroup.a 1)
          (MonoidAlgebra.of ℝ quaternionSubgroup (quaternionGroupEquiv g)) := by
  rw [quaternionAlgebraMap_of]
  simp only [quaternionCoefficientPairDifference_apply,
    coeff_of_quaternionGroupEquiv]
  cases g with
  | a r =>
      fin_cases r
      all_goals
        repeat first
          | rw [if_pos (by decide)]
          | rw [if_neg (by decide)]
        norm_num [quaternionGroupHom_a_val, ZMod.val, pow_succ,
          Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul]
  | xa r =>
      fin_cases r
      all_goals
        repeat first
          | rw [if_pos (by decide)]
          | rw [if_neg (by decide)]
        norm_num [quaternionGroupHom_xa_val, ZMod.val, pow_succ,
          Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem quaternionAlgebraMap_imJ_of (g : QuaternionGroup 2) :
    (quaternionAlgebraMap
      (MonoidAlgebra.of ℝ quaternionSubgroup (quaternionGroupEquiv g))).imJ =
        quaternionCoefficientPairDifference (QuaternionGroup.xa 0)
          (MonoidAlgebra.of ℝ quaternionSubgroup (quaternionGroupEquiv g)) := by
  rw [quaternionAlgebraMap_of]
  simp only [quaternionCoefficientPairDifference_apply,
    coeff_of_quaternionGroupEquiv]
  cases g with
  | a r =>
      fin_cases r
      all_goals
        repeat first
          | rw [if_pos (by decide)]
          | rw [if_neg (by decide)]
        norm_num [quaternionGroupHom_a_val, ZMod.val, pow_succ,
          Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul]
  | xa r =>
      fin_cases r
      all_goals
        repeat first
          | rw [if_pos (by decide)]
          | rw [if_neg (by decide)]
        norm_num [quaternionGroupHom_xa_val, ZMod.val, pow_succ,
          Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem quaternionAlgebraMap_imK_of (g : QuaternionGroup 2) :
    (quaternionAlgebraMap
      (MonoidAlgebra.of ℝ quaternionSubgroup (quaternionGroupEquiv g))).imK =
        quaternionCoefficientPairDifference
          (QuaternionGroup.a 1 * QuaternionGroup.xa 0)
          (MonoidAlgebra.of ℝ quaternionSubgroup (quaternionGroupEquiv g)) := by
  rw [quaternionAlgebraMap_of]
  simp only [quaternionCoefficientPairDifference_apply,
    coeff_of_quaternionGroupEquiv]
  cases g with
  | a r =>
      fin_cases r
      all_goals
        repeat first
          | rw [if_pos (by decide)]
          | rw [if_neg (by decide)]
        norm_num [quaternionGroupHom_a_val, ZMod.val, pow_succ,
          Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul]
  | xa r =>
      fin_cases r
      all_goals
        repeat first
          | rw [if_pos (by decide)]
          | rw [if_neg (by decide)]
        norm_num [quaternionGroupHom_xa_val, ZMod.val, pow_succ,
          Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul]

/-- The real coordinate of the quaternion map recovers the coefficient
difference at `±1`. -/
theorem quaternionAlgebraMap_re (x : QuaternionGroupAlgebra) :
    (quaternionAlgebraMap x).re =
      quaternionCoefficientPairDifference (QuaternionGroup.a 0) x := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | hM q =>
      obtain ⟨g, rfl⟩ := quaternionGroupEquiv.surjective q
      exact quaternionAlgebraMap_re_of g
  | hadd x y hx hy =>
      simp only [map_add, Quaternion.re_add,
        quaternionCoefficientPairDifference, MonoidAlgebra.coeff_add,
        Finsupp.add_apply] at hx hy ⊢
      linarith
  | hsmul r x hx =>
      simp only [map_smul, Quaternion.re_smul,
        quaternionCoefficientPairDifference,
        MonoidAlgebra.coeff_smul_apply, smul_eq_mul] at hx ⊢
      rw [hx]
      ring

/-- The `i` coordinate of the quaternion map recovers the coefficient
difference at `±i`. -/
theorem quaternionAlgebraMap_imI (x : QuaternionGroupAlgebra) :
    (quaternionAlgebraMap x).imI =
      quaternionCoefficientPairDifference (QuaternionGroup.a 1) x := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | hM q =>
      obtain ⟨g, rfl⟩ := quaternionGroupEquiv.surjective q
      exact quaternionAlgebraMap_imI_of g
  | hadd x y hx hy =>
      simp only [map_add, Quaternion.imI_add,
        quaternionCoefficientPairDifference, MonoidAlgebra.coeff_add,
        Finsupp.add_apply] at hx hy ⊢
      linarith
  | hsmul r x hx =>
      simp only [map_smul, Quaternion.imI_smul,
        quaternionCoefficientPairDifference,
        MonoidAlgebra.coeff_smul_apply, smul_eq_mul] at hx ⊢
      rw [hx]
      ring

/-- The `j` coordinate of the quaternion map recovers the coefficient
difference at `±j`. -/
theorem quaternionAlgebraMap_imJ (x : QuaternionGroupAlgebra) :
    (quaternionAlgebraMap x).imJ =
      quaternionCoefficientPairDifference (QuaternionGroup.xa 0) x := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | hM q =>
      obtain ⟨g, rfl⟩ := quaternionGroupEquiv.surjective q
      exact quaternionAlgebraMap_imJ_of g
  | hadd x y hx hy =>
      simp only [map_add, Quaternion.imJ_add,
        quaternionCoefficientPairDifference, MonoidAlgebra.coeff_add,
        Finsupp.add_apply] at hx hy ⊢
      linarith
  | hsmul r x hx =>
      simp only [map_smul, Quaternion.imJ_smul,
        quaternionCoefficientPairDifference,
        MonoidAlgebra.coeff_smul_apply, smul_eq_mul] at hx ⊢
      rw [hx]
      ring

/-- The `k` coordinate of the quaternion map recovers the coefficient
difference at `±k`, with `k = i * j`. -/
theorem quaternionAlgebraMap_imK (x : QuaternionGroupAlgebra) :
    (quaternionAlgebraMap x).imK =
      quaternionCoefficientPairDifference
        (QuaternionGroup.a 1 * QuaternionGroup.xa 0) x := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | hM q =>
      obtain ⟨g, rfl⟩ := quaternionGroupEquiv.surjective q
      exact quaternionAlgebraMap_imK_of g
  | hadd x y hx hy =>
      simp only [map_add, Quaternion.imK_add,
        quaternionCoefficientPairDifference, MonoidAlgebra.coeff_add,
        Finsupp.add_apply] at hx hy ⊢
      linarith
  | hsmul r x hx =>
      simp only [map_smul, Quaternion.imK_smul,
        quaternionCoefficientPairDifference,
        MonoidAlgebra.coeff_smul_apply, smul_eq_mul] at hx ⊢
      rw [hx]
      ring

/-- The quaternion coordinate map paired with all 4 real character
coordinates. -/
def quaternionRealBlocksMap :
    QuaternionGroupAlgebra →ₐ[ℝ]
      (QuaternionCharacterIndex → ℝ) × ℍ[ℝ] :=
  quaternionCharacterMap.prod quaternionAlgebraMap

/-- The combined map has the character map and quaternion map as its 2
coordinates. -/
@[simp]
theorem quaternionRealBlocksMap_apply (x : QuaternionGroupAlgebra) :
    quaternionRealBlocksMap x =
      (quaternionCharacterMap x, quaternionAlgebraMap x) := by
  rfl

private theorem zmod_four_cases (r : ZMod 4) :
    r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by
  fin_cases r
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

private theorem eq_zero_of_pair_sums_and_differences_eq_zero
    (x : QuaternionGroupAlgebra)
    (hsOne : quaternionCoefficientSumOne x = 0)
    (hsI : quaternionCoefficientSumI x = 0)
    (hsJ : quaternionCoefficientSumJ x = 0)
    (hsK : quaternionCoefficientSumK x = 0)
    (hdOne : quaternionCoefficientPairDifference (QuaternionGroup.a 0) x = 0)
    (hdI : quaternionCoefficientPairDifference (QuaternionGroup.a 1) x = 0)
    (hdJ : quaternionCoefficientPairDifference (QuaternionGroup.xa 0) x = 0)
    (hdK : quaternionCoefficientPairDifference
      (QuaternionGroup.a 1 * QuaternionGroup.xa 0) x = 0) :
    x = 0 := by
  classical
  rw [quaternionCoefficientSumOne_apply,
    quaternionCoefficientPairSum_apply] at hsOne
  rw [quaternionCoefficientSumI_apply,
    quaternionCoefficientPairSum_apply] at hsI
  rw [quaternionCoefficientSumJ_apply,
    quaternionCoefficientPairSum_apply] at hsJ
  rw [quaternionCoefficientSumK_apply,
    quaternionCoefficientPairSum_apply] at hsK
  simp only [quaternionCoefficientPairDifference_apply] at hdOne hdI hdJ hdK
  have hOne :
      (MonoidAlgebra.coeff x)
        (quaternionGroupEquiv (QuaternionGroup.a 0)) = 0 := by
    linarith [hsOne, hdOne]
  have hNegOne :
      (MonoidAlgebra.coeff x)
        (quaternionGroupEquiv
          (QuaternionGroup.a 2 * QuaternionGroup.a 0)) = 0 := by
    linarith [hsOne, hdOne]
  have hI :
      (MonoidAlgebra.coeff x)
        (quaternionGroupEquiv (QuaternionGroup.a 1)) = 0 := by
    linarith [hsI, hdI]
  have hNegI :
      (MonoidAlgebra.coeff x)
        (quaternionGroupEquiv
          (QuaternionGroup.a 2 * QuaternionGroup.a 1)) = 0 := by
    linarith [hsI, hdI]
  have hJ :
      (MonoidAlgebra.coeff x)
        (quaternionGroupEquiv (QuaternionGroup.xa 0)) = 0 := by
    linarith [hsJ, hdJ]
  have hNegJ :
      (MonoidAlgebra.coeff x)
        (quaternionGroupEquiv
          (QuaternionGroup.a 2 * QuaternionGroup.xa 0)) = 0 := by
    linarith [hsJ, hdJ]
  have hK :
      (MonoidAlgebra.coeff x)
        (quaternionGroupEquiv
          (QuaternionGroup.a 1 * QuaternionGroup.xa 0)) = 0 := by
    linarith [hsK, hdK]
  have hNegK :
      (MonoidAlgebra.coeff x)
        (quaternionGroupEquiv
          (QuaternionGroup.a 2 *
            (QuaternionGroup.a 1 * QuaternionGroup.xa 0))) = 0 := by
    linarith [hsK, hdK]
  ext q
  obtain ⟨g, rfl⟩ := quaternionGroupEquiv.surjective q
  simp only [MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  cases g with
  | a r =>
      have hr := zmod_four_cases r
      rcases hr with rfl | rfl | rfl | rfl
      · exact hOne
      · exact hI
      · rw [show (QuaternionGroup.a 2 * QuaternionGroup.a 0 :
            QuaternionGroup 2) = QuaternionGroup.a 2 by decide] at hNegOne
        exact hNegOne
      · rw [show (QuaternionGroup.a 2 * QuaternionGroup.a 1 :
            QuaternionGroup 2) = QuaternionGroup.a 3 by decide] at hNegI
        exact hNegI
  | xa r =>
      have hr := zmod_four_cases r
      rcases hr with rfl | rfl | rfl | rfl
      · exact hJ
      · rw [show (QuaternionGroup.a 2 *
            (QuaternionGroup.a 1 * QuaternionGroup.xa 0) :
              QuaternionGroup 2) = QuaternionGroup.xa 1 by decide] at hNegK
        exact hNegK
      · rw [show (QuaternionGroup.a 2 * QuaternionGroup.xa 0 :
            QuaternionGroup 2) = QuaternionGroup.xa 2 by decide] at hNegJ
        exact hNegJ
      · rw [show (QuaternionGroup.a 1 * QuaternionGroup.xa 0 :
            QuaternionGroup 2) = QuaternionGroup.xa 3 by decide] at hK
        exact hK

/-- The character and quaternion coordinates together determine every
coefficient of the real quaternion group algebra. -/
theorem quaternionRealBlocksMap_injective :
    Function.Injective quaternionRealBlocksMap := by
  intro x y hxy
  let z := x - y
  have hChar : quaternionCharacterMap z = 0 := by
    rw [show quaternionCharacterMap z =
        quaternionCharacterMap x - quaternionCharacterMap y by simp [z]]
    exact sub_eq_zero.mpr (congrArg Prod.fst hxy)
  have hQuaternion : quaternionAlgebraMap z = 0 := by
    rw [show quaternionAlgebraMap z =
        quaternionAlgebraMap x - quaternionAlgebraMap y by simp [z]]
    exact sub_eq_zero.mpr (congrArg Prod.snd hxy)
  have hsOne : quaternionCoefficientSumOne z = 0 := by
    rw [quaternionCoefficientSumOne_inverseHadamard, hChar]
    norm_num
  have hsI : quaternionCoefficientSumI z = 0 := by
    rw [quaternionCoefficientSumI_inverseHadamard, hChar]
    norm_num
  have hsJ : quaternionCoefficientSumJ z = 0 := by
    rw [quaternionCoefficientSumJ_inverseHadamard, hChar]
    norm_num
  have hsK : quaternionCoefficientSumK z = 0 := by
    rw [quaternionCoefficientSumK_inverseHadamard, hChar]
    norm_num
  have hdOne :
      quaternionCoefficientPairDifference (QuaternionGroup.a 0) z = 0 := by
    rw [← quaternionAlgebraMap_re, hQuaternion]
    rfl
  have hdI :
      quaternionCoefficientPairDifference (QuaternionGroup.a 1) z = 0 := by
    rw [← quaternionAlgebraMap_imI, hQuaternion]
    rfl
  have hdJ :
      quaternionCoefficientPairDifference (QuaternionGroup.xa 0) z = 0 := by
    rw [← quaternionAlgebraMap_imJ, hQuaternion]
    rfl
  have hdK : quaternionCoefficientPairDifference
      (QuaternionGroup.a 1 * QuaternionGroup.xa 0) z = 0 := by
    rw [← quaternionAlgebraMap_imK, hQuaternion]
    rfl
  have hz := eq_zero_of_pair_sums_and_differences_eq_zero z
    hsOne hsI hsJ hsK hdOne hdI hdJ hdK
  exact sub_eq_zero.mp hz

private theorem finrank_quaternionRealBlocks :
    Module.finrank ℝ QuaternionGroupAlgebra =
      Module.finrank ℝ ((QuaternionCharacterIndex → ℝ) × ℍ[ℝ]) := by
  rw [LinearEquiv.finrank_eq (MonoidAlgebra.coeffLinearEquiv ℝ),
    Module.finrank_finsupp_self, card_quaternionSubgroup,
    Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    card_quaternionCharacterIndex, Quaternion.finrank_eq_four]

/-- The combined character and quaternion map is bijective. -/
theorem quaternionRealBlocksMap_bijective :
    Function.Bijective quaternionRealBlocksMap := by
  refine ⟨quaternionRealBlocksMap_injective, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    finrank_quaternionRealBlocks
      (f := quaternionRealBlocksMap.toLinearMap)).mp
        quaternionRealBlocksMap_injective

/-- The explicit real-algebra decomposition of the quaternion group algebra
into its 4 real character coordinates and its chosen quaternion coordinate. -/
noncomputable def quaternionRealBlocksEquiv :
    QuaternionGroupAlgebra ≃ₐ[ℝ]
      (QuaternionCharacterIndex → ℝ) × ℍ[ℝ] :=
  AlgEquiv.ofBijective quaternionRealBlocksMap
    quaternionRealBlocksMap_bijective

/-- The decomposition equivalence evaluates through the combined character
and quaternion map. -/
@[simp]
theorem quaternionRealBlocksEquiv_apply (x : QuaternionGroupAlgebra) :
    quaternionRealBlocksEquiv x =
      (quaternionCharacterMap x, quaternionAlgebraMap x) := by
  rfl

end

end BinaryTetrahedral
