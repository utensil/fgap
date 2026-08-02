/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FGAP.Algebra.GroupAlgebra.QuaternionQuotient
public import FGAP.Mathlib.GroupTheory.SpecificGroups.Quaternion

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Real characters of the quaternion group algebra

The quotient `Q₈ / {±1}` has 4 real sign characters. We index them by
`Bool × Bool`, using `false` for `+1` and `true` for `-1`. Their algebraic
extensions give the forward Hadamard coordinates of the coefficient-pair
sums in the real quaternion group algebra.

The abstract normal-form representative of `k` is
`QuaternionGroup.a 1 * QuaternionGroup.xa 0`. This records the orientation
`i * j = k` used by the concrete equivalence.

## Main declarations

* `BinaryTetrahedral.quaternionCharacter`: the 4 real sign characters of the
  abstract quaternion group.
* `BinaryTetrahedral.quaternionCharacterMap`: their combined algebra map on
  the concrete quaternion group algebra.
* `BinaryTetrahedral.quaternionCharacterMap_hadamard`: the indexed forward
  Hadamard formula.

## References

* Pavel Etingof et al., *Introduction to Representation Theory*, §4.3,
  pp. 63--64, and Example 4.8.1, p. 73.
  <https://bookstore.ams.org/stml-59/>
* Forest note `fgap-001B`.
  <https://github.com/utensil/forest/pull/68>
-/

public section

namespace BinaryTetrahedral

noncomputable section

/-- The 4 real sign characters, with `false` denoting `+1` and `true`
denoting `-1` in each coordinate. -/
abbrev QuaternionCharacterIndex := Bool × Bool

/-- There are 4 real sign-character indices. -/
@[simp]
theorem card_quaternionCharacterIndex :
    Fintype.card QuaternionCharacterIndex = 4 := by
  simp [QuaternionCharacterIndex]

/-- The real sign selected by a Boolean index: `false ↦ +1` and
`true ↦ -1`. -/
def quaternionCharacterSign : Bool → ℝ
  | false => 1
  | true => -1

/-- The unit-valued sign selected by a Boolean index. -/
def quaternionCharacterSignUnit : Bool → ℝˣ
  | false => 1
  | true => -1

/-- Coercing the unit-valued sign to `ℝ` gives the corresponding real sign. -/
@[simp]
theorem coe_quaternionCharacterSignUnit (e : Bool) :
    (quaternionCharacterSignUnit e : ℝ) = quaternionCharacterSign e := by
  cases e <;> rfl

@[simp]
private theorem quaternionCharacterSignUnit_sq (e : Bool) :
    quaternionCharacterSignUnit e ^ 2 = 1 := by
  cases e <;> ext <;> norm_num [quaternionCharacterSignUnit]

@[simp]
private theorem quaternionCharacterSignUnit_pow_four (e : Bool) :
    quaternionCharacterSignUnit e ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by norm_num, pow_mul, quaternionCharacterSignUnit_sq, one_pow]

/-- The real sign character indexed by `χ`, defined through the quaternion-group
presentation. -/
def quaternionCharacter (χ : QuaternionCharacterIndex) : QuaternionGroup 2 →* ℝˣ :=
  QuaternionGroup.lift (quaternionCharacterSignUnit χ.1)
    (quaternionCharacterSignUnit χ.2)
    (quaternionCharacterSignUnit_pow_four χ.1)
    (by rw [quaternionCharacterSignUnit_sq, quaternionCharacterSignUnit_sq])
    (by
      cases χ.1 <;>
        cases χ.2 <;>
        ext <;>
        norm_num [quaternionCharacterSignUnit])

/-- A real sign character sends the abstract representative of `i` to its
1st indexed sign. -/
@[simp]
theorem quaternionCharacter_a_one (χ : QuaternionCharacterIndex) :
    quaternionCharacter χ (QuaternionGroup.a 1) = quaternionCharacterSignUnit χ.1 := by
  apply QuaternionGroup.lift_a_one

/-- A real sign character sends the abstract representative of `j` to its
2nd indexed sign. -/
@[simp]
theorem quaternionCharacter_xa_zero (χ : QuaternionCharacterIndex) :
    quaternionCharacter χ (QuaternionGroup.xa 0) = quaternionCharacterSignUnit χ.2 := by
  apply QuaternionGroup.lift_xa_zero

/-- The sign pair uniquely determines its real quaternion-group character. -/
theorem quaternionCharacter_injective : Function.Injective quaternionCharacter := by
  rintro ⟨e, d⟩ ⟨e', d'⟩ h
  have heValue := congrArg
    (fun f : QuaternionGroup 2 →* ℝˣ => f (QuaternionGroup.a 1)) h
  rw [quaternionCharacter_a_one, quaternionCharacter_a_one] at heValue
  have heCoe := congrArg (fun u : ℝˣ => (u : ℝ)) heValue
  have he : e = e' := by
    cases e <;> cases e'
    · rfl
    · norm_num [quaternionCharacterSignUnit] at heCoe
    · norm_num [quaternionCharacterSignUnit] at heCoe
    · rfl
  have hdValue := congrArg
    (fun f : QuaternionGroup 2 →* ℝˣ => f (QuaternionGroup.xa 0)) h
  rw [quaternionCharacter_xa_zero, quaternionCharacter_xa_zero] at hdValue
  have hdCoe := congrArg (fun u : ℝˣ => (u : ℝ)) hdValue
  have hd : d = d' := by
    cases d <;> cases d'
    · rfl
    · norm_num [quaternionCharacterSignUnit] at hdCoe
    · norm_num [quaternionCharacterSignUnit] at hdCoe
    · rfl
  exact congrArg₂ Prod.mk he hd

/-- Every real sign character sends the central element `-1` to `1`. -/
@[simp]
theorem quaternionCharacter_a_two (χ : QuaternionCharacterIndex) :
    quaternionCharacter χ (QuaternionGroup.a 2) = 1 := by
  change QuaternionGroup.lift (quaternionCharacterSignUnit χ.1)
      (quaternionCharacterSignUnit χ.2) _ _ _ (QuaternionGroup.a 2) = 1
  rw [show (2 : ZMod 4) = ((2 : ℤ) : ZMod 4) by norm_num,
    QuaternionGroup.lift_a_intCast]
  exact quaternionCharacterSignUnit_sq χ.1

/-- The central sign subgroup lies in the kernel of every real sign character. -/
theorem quaternionCentralSignSubgroup_le_ker (χ : QuaternionCharacterIndex) :
    Subgroup.closure {QuaternionGroup.a 2} ≤ MonoidHom.ker (quaternionCharacter χ) := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst g
  change quaternionCharacter χ (QuaternionGroup.a 2) = 1
  exact quaternionCharacter_a_two χ

/-- A real sign character sends the oriented representative `i * j = k` to
the product of its 2 indexed signs. -/
@[simp]
theorem quaternionCharacter_k (χ : QuaternionCharacterIndex) :
    quaternionCharacter χ (QuaternionGroup.a 1 * QuaternionGroup.xa 0) =
      quaternionCharacterSignUnit χ.1 * quaternionCharacterSignUnit χ.2 := by
  rw [map_mul, quaternionCharacter_a_one, quaternionCharacter_xa_zero]

@[simp]
private theorem quaternionCharacter_a_three (χ : QuaternionCharacterIndex) :
    quaternionCharacter χ (QuaternionGroup.a 3) = quaternionCharacterSignUnit χ.1 := by
  rw [show (QuaternionGroup.a 3 : QuaternionGroup 2) =
      QuaternionGroup.a 2 * QuaternionGroup.a 1 by decide,
    map_mul, quaternionCharacter_a_two, quaternionCharacter_a_one, one_mul]

@[simp]
private theorem quaternionCharacter_xa_one (χ : QuaternionCharacterIndex) :
    quaternionCharacter χ (QuaternionGroup.xa 1) =
      quaternionCharacterSignUnit χ.2 * quaternionCharacterSignUnit χ.1 := by
  rw [show (QuaternionGroup.xa 1 : QuaternionGroup 2) =
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 by decide,
    map_mul, quaternionCharacter_xa_zero, quaternionCharacter_a_one]

@[simp]
private theorem quaternionCharacter_xa_two (χ : QuaternionCharacterIndex) :
    quaternionCharacter χ (QuaternionGroup.xa 2) = quaternionCharacterSignUnit χ.2 := by
  rw [show (QuaternionGroup.xa 2 : QuaternionGroup 2) =
      QuaternionGroup.a 2 * QuaternionGroup.xa 0 by decide,
    map_mul, quaternionCharacter_a_two, quaternionCharacter_xa_zero, one_mul]

@[simp]
private theorem quaternionCharacter_xa_three (χ : QuaternionCharacterIndex) :
    quaternionCharacter χ (QuaternionGroup.xa 3) =
      quaternionCharacterSignUnit χ.2 * quaternionCharacterSignUnit χ.1 := by
  rw [show (QuaternionGroup.xa 3 : QuaternionGroup 2) =
      QuaternionGroup.a 2 * (QuaternionGroup.xa 0 * QuaternionGroup.a 1) by decide,
    map_mul, map_mul, quaternionCharacter_a_two, quaternionCharacter_xa_zero,
    quaternionCharacter_a_one, one_mul]

@[simp]
private theorem quaternionCharacter_a_val (χ : QuaternionCharacterIndex) (r : ZMod 4) :
    quaternionCharacter χ (QuaternionGroup.a r) =
      quaternionCharacterSignUnit χ.1 ^ r.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val r]
  rw [← QuaternionGroup.a_one_pow, map_pow, quaternionCharacter_a_one]

@[simp]
private theorem quaternionCharacter_xa_val (χ : QuaternionCharacterIndex) (r : ZMod 4) :
    quaternionCharacter χ (QuaternionGroup.xa r) =
      quaternionCharacterSignUnit χ.2 * quaternionCharacterSignUnit χ.1 ^ r.val := by
  rw [show (QuaternionGroup.xa r : QuaternionGroup 2) =
      QuaternionGroup.xa 0 * QuaternionGroup.a r by simp]
  rw [map_mul, quaternionCharacter_xa_zero, quaternionCharacter_a_val]

/-- The real sign character transported to the concrete quaternion subgroup. -/
def quaternionSubgroupCharacter (χ : QuaternionCharacterIndex) :
    quaternionSubgroup →* ℝˣ :=
  (quaternionCharacter χ).comp quaternionGroupEquiv.symm.toMonoidHom

/-- The algebraic extension of 1 real sign character to the concrete real
quaternion group algebra. -/
def quaternionCharacterAlgebraMap (χ : QuaternionCharacterIndex) :
    QuaternionGroupAlgebra →ₐ[ℝ] ℝ :=
  MonoidAlgebra.lift ℝ ℝ quaternionSubgroup
    ((Units.coeHom ℝ).comp (quaternionSubgroupCharacter χ))

/-- On a group-algebra basis element, the extended character evaluates the
corresponding abstract quaternion-group element. -/
@[simp]
theorem quaternionCharacterAlgebraMap_of (χ : QuaternionCharacterIndex)
    (q : quaternionSubgroup) :
    quaternionCharacterAlgebraMap χ (MonoidAlgebra.of ℝ quaternionSubgroup q) =
      quaternionCharacter χ (quaternionGroupEquiv.symm q) := by
  rw [quaternionCharacterAlgebraMap, MonoidAlgebra.lift_of]
  rfl

/-- The 4 real sign characters combined into a function-valued algebra map. -/
def quaternionCharacterMap :
    QuaternionGroupAlgebra →ₐ[ℝ] (QuaternionCharacterIndex → ℝ) :=
  AlgHom.pi quaternionCharacterAlgebraMap

/-- Evaluation of the combined character map at an index is the corresponding
extended character. -/
@[simp]
theorem quaternionCharacterMap_apply (x : QuaternionGroupAlgebra)
    (χ : QuaternionCharacterIndex) :
    quaternionCharacterMap x χ = quaternionCharacterAlgebraMap χ x := by
  apply AlgHom.pi_apply

/-- The sum of coefficients at `q` and its central negative `-q`. -/
def quaternionCoefficientPairSum (q : QuaternionGroup 2)
    (x : QuaternionGroupAlgebra) : ℝ :=
  (MonoidAlgebra.coeff x) (quaternionGroupEquiv q) +
    (MonoidAlgebra.coeff x)
      (quaternionGroupEquiv (QuaternionGroup.a 2 * q))

/-- Expanding a coefficient-pair sum gives the 2 coefficients at `q` and its
central negative `-q`. -/
theorem quaternionCoefficientPairSum_apply (q : QuaternionGroup 2)
    (x : QuaternionGroupAlgebra) :
    quaternionCoefficientPairSum q x =
      (MonoidAlgebra.coeff x) (quaternionGroupEquiv q) +
        (MonoidAlgebra.coeff x)
          (quaternionGroupEquiv (QuaternionGroup.a 2 * q)) := by
  rfl

/-- The coefficient-pair sum at `±1`. -/
def quaternionCoefficientSumOne (x : QuaternionGroupAlgebra) : ℝ :=
  quaternionCoefficientPairSum (QuaternionGroup.a 0) x

/-- The coefficient-pair sum at `±1` is the generic sum at the identity
representative. -/
theorem quaternionCoefficientSumOne_apply (x : QuaternionGroupAlgebra) :
    quaternionCoefficientSumOne x =
      quaternionCoefficientPairSum (QuaternionGroup.a 0) x := by
  rfl

/-- The coefficient-pair sum at `±i`. -/
def quaternionCoefficientSumI (x : QuaternionGroupAlgebra) : ℝ :=
  quaternionCoefficientPairSum (QuaternionGroup.a 1) x

/-- The coefficient-pair sum at `±i` is the generic sum at the selected
`i` representative. -/
theorem quaternionCoefficientSumI_apply (x : QuaternionGroupAlgebra) :
    quaternionCoefficientSumI x =
      quaternionCoefficientPairSum (QuaternionGroup.a 1) x := by
  rfl

/-- The coefficient-pair sum at `±j`. -/
def quaternionCoefficientSumJ (x : QuaternionGroupAlgebra) : ℝ :=
  quaternionCoefficientPairSum (QuaternionGroup.xa 0) x

/-- The coefficient-pair sum at `±j` is the generic sum at the selected
`j` representative. -/
theorem quaternionCoefficientSumJ_apply (x : QuaternionGroupAlgebra) :
    quaternionCoefficientSumJ x =
      quaternionCoefficientPairSum (QuaternionGroup.xa 0) x := by
  rfl

/-- The coefficient-pair sum at `±k`, with `k` represented by `i * j`. -/
def quaternionCoefficientSumK (x : QuaternionGroupAlgebra) : ℝ :=
  quaternionCoefficientPairSum
    (QuaternionGroup.a 1 * QuaternionGroup.xa 0) x

/-- The coefficient-pair sum at `±k` is the generic sum at the oriented
representative `i * j`. -/
theorem quaternionCoefficientSumK_apply (x : QuaternionGroupAlgebra) :
    quaternionCoefficientSumK x =
      quaternionCoefficientPairSum
        (QuaternionGroup.a 1 * QuaternionGroup.xa 0) x := by
  rfl

@[simp]
private theorem coeff_of_quaternionGroupEquiv (g h : QuaternionGroup 2) :
    (MonoidAlgebra.coeff
      (MonoidAlgebra.of ℝ quaternionSubgroup (quaternionGroupEquiv g)))
      (quaternionGroupEquiv h) = if g = h then 1 else 0 := by
  classical
  simp [Finsupp.single_apply]

private theorem quaternionCharacterMap_hadamard_of
    (χ : QuaternionCharacterIndex) (q : quaternionSubgroup) :
    quaternionCharacterMap (MonoidAlgebra.of ℝ quaternionSubgroup q) χ =
      quaternionCoefficientSumOne (MonoidAlgebra.of ℝ quaternionSubgroup q) +
        quaternionCharacterSign χ.1 *
          quaternionCoefficientSumI (MonoidAlgebra.of ℝ quaternionSubgroup q) +
        quaternionCharacterSign χ.2 *
          quaternionCoefficientSumJ (MonoidAlgebra.of ℝ quaternionSubgroup q) +
        (quaternionCharacterSign χ.1 * quaternionCharacterSign χ.2) *
          quaternionCoefficientSumK (MonoidAlgebra.of ℝ quaternionSubgroup q) := by
  rcases χ with ⟨e, d⟩
  obtain ⟨g, rfl⟩ := quaternionGroupEquiv.surjective q
  rw [quaternionCharacterMap_apply, quaternionCharacterAlgebraMap_of]
  simp only [MulEquiv.symm_apply_apply]
  simp only [quaternionCoefficientSumOne, quaternionCoefficientSumI,
    quaternionCoefficientSumJ, quaternionCoefficientSumK,
    quaternionCoefficientPairSum, coeff_of_quaternionGroupEquiv]
  cases g with
  | a r =>
      rw [quaternionCharacter_a_val]
      fin_cases r <;>
        cases e <;>
        cases d
      all_goals
        repeat first
          | rw [if_pos (by decide)]
          | rw [if_neg (by decide)]
        norm_num [quaternionCharacterSign, quaternionCharacterSignUnit, ZMod.val]
  | xa r =>
      rw [quaternionCharacter_xa_val]
      fin_cases r <;>
        cases e <;>
        cases d
      all_goals
        repeat first
          | rw [if_pos (by decide)]
          | rw [if_neg (by decide)]
        norm_num [quaternionCharacterSign, quaternionCharacterSignUnit, ZMod.val]

/-- The indexed forward Hadamard formula for the 4 real character
coordinates. -/
theorem quaternionCharacterMap_hadamard (x : QuaternionGroupAlgebra)
    (χ : QuaternionCharacterIndex) :
    quaternionCharacterMap x χ =
      quaternionCoefficientSumOne x +
        quaternionCharacterSign χ.1 * quaternionCoefficientSumI x +
        quaternionCharacterSign χ.2 * quaternionCoefficientSumJ x +
        (quaternionCharacterSign χ.1 * quaternionCharacterSign χ.2) *
          quaternionCoefficientSumK x := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | hM q => exact quaternionCharacterMap_hadamard_of χ q
  | hadd x y hx hy =>
      simp only [map_add, Pi.add_apply, quaternionCoefficientSumOne,
        quaternionCoefficientSumI, quaternionCoefficientSumJ,
        quaternionCoefficientSumK, quaternionCoefficientPairSum,
        MonoidAlgebra.coeff_add, Finsupp.add_apply] at hx hy ⊢
      rw [hx, hy]
      ring
  | hsmul r x hx =>
      simp only [map_smul, Pi.smul_apply,
        quaternionCoefficientSumOne, quaternionCoefficientSumI,
        quaternionCoefficientSumJ, quaternionCoefficientSumK,
        quaternionCoefficientPairSum, MonoidAlgebra.coeff_smul_apply,
        smul_eq_mul] at hx ⊢
      rw [hx]
      ring

/-- The forward Hadamard coordinate at the sign pair `(+1, +1)`, exposed as
the Boolean pair `(false, false)`. -/
theorem quaternionCharacterMap_plus_plus (x : QuaternionGroupAlgebra) :
    quaternionCharacterMap x (false, false) =
      quaternionCoefficientSumOne x + quaternionCoefficientSumI x +
        quaternionCoefficientSumJ x + quaternionCoefficientSumK x := by
  simpa [quaternionCharacterSign] using
    quaternionCharacterMap_hadamard x (false, false)

/-- The forward Hadamard coordinate at the sign pair `(-1, +1)`, exposed as
the Boolean pair `(true, false)`. -/
theorem quaternionCharacterMap_minus_plus (x : QuaternionGroupAlgebra) :
    quaternionCharacterMap x (true, false) =
      quaternionCoefficientSumOne x - quaternionCoefficientSumI x +
        quaternionCoefficientSumJ x - quaternionCoefficientSumK x := by
  simpa [quaternionCharacterSign, sub_eq_add_neg] using
    quaternionCharacterMap_hadamard x (true, false)

/-- The forward Hadamard coordinate at the sign pair `(+1, -1)`, exposed as
the Boolean pair `(false, true)`. -/
theorem quaternionCharacterMap_plus_minus (x : QuaternionGroupAlgebra) :
    quaternionCharacterMap x (false, true) =
      quaternionCoefficientSumOne x + quaternionCoefficientSumI x -
        quaternionCoefficientSumJ x - quaternionCoefficientSumK x := by
  simpa [quaternionCharacterSign, sub_eq_add_neg] using
    quaternionCharacterMap_hadamard x (false, true)

/-- The forward Hadamard coordinate at the sign pair `(-1, -1)`, exposed as
the Boolean pair `(true, true)`. -/
theorem quaternionCharacterMap_minus_minus (x : QuaternionGroupAlgebra) :
    quaternionCharacterMap x (true, true) =
      quaternionCoefficientSumOne x - quaternionCoefficientSumI x -
        quaternionCoefficientSumJ x + quaternionCoefficientSumK x := by
  simpa [quaternionCharacterSign, sub_eq_add_neg] using
    quaternionCharacterMap_hadamard x (true, true)

end

end BinaryTetrahedral
