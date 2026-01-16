/-
Copyright (c) 2025 Brieuc de La Fournière. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brieuc de La Fournière
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The Golden Ratio

This file defines the golden ratio φ = (1 + √5)/2 and proves its fundamental properties,
including connections to Fibonacci and Lucas sequences.

## Main definitions

* `phi` - The golden ratio φ = (1 + √5)/2
* `psi` - The conjugate golden ratio ψ = (1 - √5)/2
* `binet` - Binet's formula for Fibonacci: F_n = (φⁿ - ψⁿ)/√5
* `lucas` - Lucas sequence: L_0 = 2, L_1 = 1, L_{n+2} = L_{n+1} + L_n

## Main results

* `phi_squared` - φ² = φ + 1 (defining property)
* `phi_psi_sum` - φ + ψ = 1
* `phi_psi_product` - φ × ψ = -1
* `fib_recurrence` - F_{n+2} = F_{n+1} + F_n
* `lucas_recurrence` - L_{n+2} = L_{n+1} + L_n

## References

* Hardy & Wright, "An Introduction to the Theory of Numbers"
-/

namespace PhysLean.G2.Algebra.GoldenRatio

open Real

/-!
## The Golden Ratio

φ = (1 + √5)/2 ≈ 1.618...

Satisfies: φ² = φ + 1
-/

/-- The golden ratio φ = (1 + √5)/2. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- The conjugate golden ratio ψ = (1 - √5)/2. -/
noncomputable def psi : ℝ := (1 - Real.sqrt 5) / 2

/-!
## Fundamental Properties
-/

/-- φ + ψ = 1. -/
theorem phi_psi_sum : phi + psi = 1 := by
  unfold phi psi
  ring

/-- φ × ψ = -1. -/
theorem phi_psi_product : phi * psi = -1 := by
  unfold phi psi
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have h' : Real.sqrt 5 * Real.sqrt 5 = 5 := by rw [← sq, h]
  ring_nf
  linarith

/-- φ² = φ + 1 (defining property). -/
theorem phi_squared : phi ^ 2 = phi + 1 := by
  unfold phi
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have h' : Real.sqrt 5 * Real.sqrt 5 = 5 := by rw [← sq, h]
  ring_nf
  linarith

/-- ψ² = ψ + 1. -/
theorem psi_squared : psi ^ 2 = psi + 1 := by
  unfold psi
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have h' : Real.sqrt 5 * Real.sqrt 5 = 5 := by rw [← sq, h]
  ring_nf
  linarith

/-!
## Binet's Formula

F_n = (φⁿ - ψⁿ)/√5

This connects Fibonacci numbers to the golden ratio algebraically.
-/

/-- Binet's formula for Fibonacci numbers. -/
noncomputable def binet (n : ℕ) : ℝ := (phi ^ n - psi ^ n) / Real.sqrt 5

/-- Binet's formula for F_0. -/
theorem binet_0 : binet 0 = 0 := by
  unfold binet
  simp

/-- Binet's formula for F_1. -/
theorem binet_1 : binet 1 = 1 := by
  unfold binet phi psi
  have h5pos : (0 : ℝ) < 5 := by norm_num
  have hsqrt5 : Real.sqrt 5 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h5pos)
  field_simp
  ring

/-!
## Lucas Numbers

L_n = φⁿ + ψⁿ

Lucas numbers satisfy the same recurrence as Fibonacci with different initial conditions.
-/

/-- Lucas sequence definition. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- L_0 = 2. -/
theorem lucas_0 : lucas 0 = 2 := rfl

/-- L_1 = 1. -/
theorem lucas_1 : lucas 1 = 1 := rfl

/-- L_2 = 3. -/
theorem lucas_2 : lucas 2 = 3 := rfl

/-- L_3 = 4. -/
theorem lucas_3 : lucas 3 = 4 := rfl

/-- L_4 = 7. -/
theorem lucas_4 : lucas 4 = 7 := rfl

/-- L_5 = 11. -/
theorem lucas_5 : lucas 5 = 11 := rfl

/-- L_6 = 18. -/
theorem lucas_6 : lucas 6 = 18 := rfl

/-- L_7 = 29. -/
theorem lucas_7 : lucas 7 = 29 := rfl

/-- L_8 = 47. -/
theorem lucas_8 : lucas 8 = 47 := rfl

/-- L_9 = 76. -/
theorem lucas_9 : lucas 9 = 76 := rfl

/-!
## Recurrence Relations
-/

/-- Fibonacci recurrence: F_{n+2} = F_{n+1} + F_n. -/
theorem fib_recurrence (n : ℕ) : Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by
  rw [Nat.fib_add_two, Nat.add_comm]

/-- Lucas recurrence: L_{n+2} = L_{n+1} + L_n. -/
theorem lucas_recurrence (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := by
  cases n <;> rfl

end PhysLean.G2.Algebra.GoldenRatio
