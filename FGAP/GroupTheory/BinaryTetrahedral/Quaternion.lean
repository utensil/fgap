/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.Real.Basic

import Mathlib.Tactic.NormNum

/-!
# Quaternion realization

This file records the quaternion arithmetic used to construct the binary
tetrahedral group. It defines the quaternion units and the selected Hurwitz
unit, then verifies its cube and conjugation action by coordinate calculation.

## Main declarations

* `BinaryTetrahedral.quaternionI`, `BinaryTetrahedral.quaternionJ`, and
  `BinaryTetrahedral.quaternionK`: the standard quaternion units.
* `BinaryTetrahedral.hurwitzCycle`: the Hurwitz unit
  `(-1 + i + j + k) / 2`.
* `BinaryTetrahedral.hurwitzCycle_pow_three` and
  `BinaryTetrahedral.hurwitzCycle_ne_one`: its cube is one, but it is not the
  identity.
* `BinaryTetrahedral.hurwitzCycle_conj_quaternionI`,
  `BinaryTetrahedral.hurwitzCycle_conj_quaternionJ`, and
  `BinaryTetrahedral.hurwitzCycle_conj_quaternionK`: conjugation cyclically
  permutes the quaternion units.

## References

* John Voight, *Quaternion Algebras*, Chapter 11, pp. 165–168.
  <https://doi.org/10.1007/978-3-030-56694-4>
* Robert A. Wilson, “Finite symmetry groups in physics,” §1.4 and §2.1.
  <https://arxiv.org/abs/2102.02817>
* Forest notes `fgap-0001` through `fgap-0006`, introduced by
  <https://github.com/utensil/forest/pull/56>.
-/

public section

open scoped Quaternion

namespace BinaryTetrahedral

noncomputable section

/-- The group of invertible Hamiltonian quaternions. -/
abbrev InvertibleQuaternions := (ℍ[ℝ])ˣ

/-- The quaternion unit `i`. -/
@[expose]
def quaternionI : InvertibleQuaternions :=
  Units.mk0 (⟨0, 1, 0, 0⟩ : ℍ[ℝ])
    (Quaternion.normSq_ne_zero.mp (by norm_num [Quaternion.normSq_def']))

/-- The quaternion value represented by `quaternionI`. -/
@[simp]
theorem coe_quaternionI :
    (quaternionI : ℍ[ℝ]) = ⟨0, 1, 0, 0⟩ :=
  rfl

/-- The quaternion unit `j`. -/
@[expose]
def quaternionJ : InvertibleQuaternions :=
  Units.mk0 (⟨0, 0, 1, 0⟩ : ℍ[ℝ])
    (Quaternion.normSq_ne_zero.mp (by norm_num [Quaternion.normSq_def']))

/-- The quaternion value represented by `quaternionJ`. -/
@[simp]
theorem coe_quaternionJ :
    (quaternionJ : ℍ[ℝ]) = ⟨0, 0, 1, 0⟩ :=
  rfl

/-- The quaternion unit `k`. -/
@[expose]
def quaternionK : InvertibleQuaternions :=
  Units.mk0 (⟨0, 0, 0, 1⟩ : ℍ[ℝ])
    (Quaternion.normSq_ne_zero.mp (by norm_num [Quaternion.normSq_def']))

/-- The quaternion value represented by `quaternionK`. -/
@[simp]
theorem coe_quaternionK :
    (quaternionK : ℍ[ℝ]) = ⟨0, 0, 0, 1⟩ :=
  rfl

/-- The quaternion underlying the selected Hurwitz unit. -/
def hurwitzCycleValue : ℍ[ℝ] :=
  ⟨-(1 / 2), 1 / 2, 1 / 2, 1 / 2⟩

/-- The Hurwitz unit `(-1 + i + j + k) / 2`. -/
def hurwitzCycle : InvertibleQuaternions :=
  Units.mk0 hurwitzCycleValue
    (Quaternion.normSq_ne_zero.mp (by norm_num [hurwitzCycleValue, Quaternion.normSq_def']))

/-- The selected Hurwitz unit has cube one. -/
theorem hurwitzCycle_pow_three : hurwitzCycle ^ 3 = 1 := by
  ext <;> norm_num [hurwitzCycle, hurwitzCycleValue, pow_succ,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

/-- The selected Hurwitz unit is not the identity quaternion. -/
theorem hurwitzCycle_ne_one : hurwitzCycle ≠ 1 := by
  intro h
  have hRe := congrArg (fun q : InvertibleQuaternions => (q : ℍ[ℝ]).re) h
  norm_num [hurwitzCycle, hurwitzCycleValue] at hRe

private theorem hurwitzCycle_mul_quaternionI :
    hurwitzCycle * quaternionI = quaternionK * hurwitzCycle := by
  ext <;> norm_num [hurwitzCycle, hurwitzCycleValue, quaternionI, quaternionK,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem hurwitzCycle_mul_quaternionJ :
    hurwitzCycle * quaternionJ = quaternionI * hurwitzCycle := by
  ext <;> norm_num [hurwitzCycle, hurwitzCycleValue, quaternionI, quaternionJ,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem hurwitzCycle_mul_quaternionK :
    hurwitzCycle * quaternionK = quaternionJ * hurwitzCycle := by
  ext <;> norm_num [hurwitzCycle, hurwitzCycleValue, quaternionJ, quaternionK,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

/-- Conjugation by the selected Hurwitz unit sends `i` to `k`. -/
theorem hurwitzCycle_conj_quaternionI :
    hurwitzCycle * quaternionI * hurwitzCycle⁻¹ = quaternionK := by
  rw [hurwitzCycle_mul_quaternionI]
  simp

/-- Conjugation by the selected Hurwitz unit sends `j` to `i`. -/
theorem hurwitzCycle_conj_quaternionJ :
    hurwitzCycle * quaternionJ * hurwitzCycle⁻¹ = quaternionI := by
  rw [hurwitzCycle_mul_quaternionJ]
  simp

/-- Conjugation by the selected Hurwitz unit sends `k` to `j`. -/
theorem hurwitzCycle_conj_quaternionK :
    hurwitzCycle * quaternionK * hurwitzCycle⁻¹ = quaternionJ := by
  rw [hurwitzCycle_mul_quaternionK]
  simp

end

end BinaryTetrahedral
