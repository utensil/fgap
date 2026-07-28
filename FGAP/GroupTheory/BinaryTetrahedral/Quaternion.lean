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

* `BinaryTetrahedral.hurwitzCycle`: the Hurwitz unit
  `(-1 + i + j + k) / 2`.
* `BinaryTetrahedral.hurwitzCycle_pow_three`: its cube is one.
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
def quaternionI : InvertibleQuaternions :=
  Units.mk0 (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) (by
    intro h
    have him := congrArg (fun q : ℍ[ℝ] => q.imI) h
    norm_num at him)

/-- The quaternion unit `j`. -/
def quaternionJ : InvertibleQuaternions :=
  Units.mk0 (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) (by
    intro h
    have hjm := congrArg (fun q : ℍ[ℝ] => q.imJ) h
    norm_num at hjm)

/-- The quaternion unit `k`. -/
def quaternionK : InvertibleQuaternions :=
  Units.mk0 (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) (by
    intro h
    have hkm := congrArg (fun q : ℍ[ℝ] => q.imK) h
    norm_num at hkm)

/-- The quaternion underlying the selected Hurwitz unit. -/
def hurwitzCycleValue : ℍ[ℝ] :=
  ⟨-(1 / 2), 1 / 2, 1 / 2, 1 / 2⟩

/-- The Hurwitz unit `(-1 + i + j + k) / 2`. -/
def hurwitzCycle : InvertibleQuaternions :=
  Units.mk0 hurwitzCycleValue (by
    intro h
    have hre := congrArg (fun q : ℍ[ℝ] => q.re) h
    norm_num [hurwitzCycleValue] at hre)

/-- The selected Hurwitz unit has cube one. -/
theorem hurwitzCycle_pow_three : hurwitzCycle ^ 3 = 1 := by
  apply Units.ext
  ext <;> norm_num [hurwitzCycle, hurwitzCycleValue, pow_succ,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem hurwitzCycle_mul_quaternionI :
    hurwitzCycle * quaternionI = quaternionK * hurwitzCycle := by
  apply Units.ext
  ext <;> norm_num [hurwitzCycle, hurwitzCycleValue, quaternionI, quaternionK,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem hurwitzCycle_mul_quaternionJ :
    hurwitzCycle * quaternionJ = quaternionI * hurwitzCycle := by
  apply Units.ext
  ext <;> norm_num [hurwitzCycle, hurwitzCycleValue, quaternionI, quaternionJ,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem hurwitzCycle_mul_quaternionK :
    hurwitzCycle * quaternionK = quaternionJ * hurwitzCycle := by
  apply Units.ext
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
