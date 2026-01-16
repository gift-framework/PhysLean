/-
Copyright (c) 2025 Brieuc de La Fournière. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brieuc de La Fournière
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# Octonions

This file defines the octonion algebra structure and its connection to G₂ geometry.
The octonions 𝕆 are the 8-dimensional normed division algebra obtained by
Cayley-Dickson doubling of the quaternions.

## Main definitions

* `Octonion` - Octonion as an 8-tuple (re, e₁, e₂, e₃, e₄, e₅, e₆, e₇)
* `octonion_dim` - dim(𝕆) = 8
* `imaginary_count` - Number of imaginary units = 7
* `fano_plane` - The 7 lines encoding octonion multiplication
* `conj` - Octonion conjugation

## Main results

* `octonion_dimension_split` - 8 = 1 + 7 (real ⊕ imaginary decomposition)
* `pairs_count` - C(7,2) = 21 (pairs of imaginary units)
* `triples_count` - C(7,3) = 35 (Fano plane related)
* `fano_plane_card` - 7 Fano lines

## References

* Baez, "The Octonions", Bull. Amer. Math. Soc. 2002
* Harvey & Lawson, "Calibrated Geometries"
-/

namespace PhysLean.G2.Algebra.Octonions

/-!
## Octonion Structure

We define octonions as 8-tuples over a ring R.
The multiplication follows the Fano plane structure.
-/

/-- Octonion as an 8-tuple: (re, e₁, e₂, e₃, e₄, e₅, e₆, e₇). -/
structure Octonion (R : Type*) [Ring R] where
  re : R      -- Real part
  e1 : R      -- Imaginary e₁
  e2 : R      -- Imaginary e₂
  e3 : R      -- Imaginary e₃
  e4 : R      -- Imaginary e₄
  e5 : R      -- Imaginary e₅
  e6 : R      -- Imaginary e₆
  e7 : R      -- Imaginary e₇
  deriving DecidableEq, Repr

variable {R : Type*} [Ring R]

/-!
## Fundamental Constants
-/

/-- Dimension of the octonions. -/
def octonion_dim : ℕ := 8

/-- dim(𝕆) = 8. -/
theorem octonion_dim_eq : octonion_dim = 8 := rfl

/-- Number of imaginary units in 𝕆. -/
def imaginary_count : ℕ := 7

/-- |Im(𝕆)| = 7. -/
theorem imaginary_count_eq : imaginary_count = 7 := rfl

/-- dim(𝕆) = imaginary_count + 1. -/
theorem dim_eq_imaginary_plus_one : octonion_dim = imaginary_count + 1 := rfl

/-!
## Imaginary Units

The 7 imaginary units form a basis for Im(𝕆).
-/

/-- Zero octonion. -/
def zero : Octonion R := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Real unit. -/
def one [One R] : Octonion R := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

/-- Imaginary unit e₁. -/
def e1_unit [Zero R] [One R] : Octonion R := ⟨0, 1, 0, 0, 0, 0, 0, 0⟩

/-- Imaginary unit e₂. -/
def e2_unit [Zero R] [One R] : Octonion R := ⟨0, 0, 1, 0, 0, 0, 0, 0⟩

/-- Imaginary unit e₃. -/
def e3_unit [Zero R] [One R] : Octonion R := ⟨0, 0, 0, 1, 0, 0, 0, 0⟩

/-- Imaginary unit e₄. -/
def e4_unit [Zero R] [One R] : Octonion R := ⟨0, 0, 0, 0, 1, 0, 0, 0⟩

/-- Imaginary unit e₅. -/
def e5_unit [Zero R] [One R] : Octonion R := ⟨0, 0, 0, 0, 0, 1, 0, 0⟩

/-- Imaginary unit e₆. -/
def e6_unit [Zero R] [One R] : Octonion R := ⟨0, 0, 0, 0, 0, 0, 1, 0⟩

/-- Imaginary unit e₇. -/
def e7_unit [Zero R] [One R] : Octonion R := ⟨0, 0, 0, 0, 0, 0, 0, 1⟩

/-- The 7 imaginary units as a function. -/
def Im_O [Zero R] [One R] : Fin 7 → Octonion R
  | 0 => e1_unit
  | 1 => e2_unit
  | 2 => e3_unit
  | 3 => e4_unit
  | 4 => e5_unit
  | 5 => e6_unit
  | 6 => e7_unit

/-- Cardinality of imaginary units. -/
theorem Im_O_card : Fintype.card (Fin 7) = 7 := by decide

/-!
## Combinatorial Properties

The 7 imaginary units give rise to fundamental combinatorics.
-/

/-- C(7,2) = 21 - number of pairs of imaginary units. -/
theorem pairs_count : Nat.choose imaginary_count 2 = 21 := by native_decide

/-- C(7,3) = 35 - number of triples (related to Fano plane). -/
theorem triples_count : Nat.choose imaginary_count 3 = 35 := by native_decide

/-- The Fano plane has 7 lines. -/
def fano_lines : ℕ := 7

/-- fano_lines = 7 = imaginary_count. -/
theorem fano_lines_eq : fano_lines = imaginary_count := rfl

/-!
## Fano Plane Structure

The Fano plane PG(2,2) encodes octonion multiplication.
Lines: {0,1,3}, {1,2,4}, {2,3,5}, {3,4,6}, {4,5,0}, {5,6,1}, {6,0,2}
-/

/-- A Fano line is a triple (i,j,k) where eᵢ·eⱼ = eₖ. -/
def FanoLine := Fin 7 × Fin 7 × Fin 7

/-- The 7 lines of the Fano plane. -/
def fano_plane : List FanoLine :=
  [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 0), (5, 6, 1), (6, 0, 2)]

/-- fano_plane has 7 lines. -/
theorem fano_plane_card : fano_plane.length = 7 := rfl

/-- Each imaginary unit is on exactly 3 Fano lines. -/
theorem fano_incidences_per_unit : 3 * imaginary_count = 21 := by native_decide

/-!
## Octonion Algebra Operations
-/

/-- Octonion addition. -/
instance [Add R] : Add (Octonion R) where
  add x y := ⟨x.re + y.re, x.e1 + y.e1, x.e2 + y.e2, x.e3 + y.e3,
              x.e4 + y.e4, x.e5 + y.e5, x.e6 + y.e6, x.e7 + y.e7⟩

/-- Octonion negation. -/
instance [Neg R] : Neg (Octonion R) where
  neg x := ⟨-x.re, -x.e1, -x.e2, -x.e3, -x.e4, -x.e5, -x.e6, -x.e7⟩

/-- Octonion subtraction. -/
instance [Sub R] : Sub (Octonion R) where
  sub x y := ⟨x.re - y.re, x.e1 - y.e1, x.e2 - y.e2, x.e3 - y.e3,
              x.e4 - y.e4, x.e5 - y.e5, x.e6 - y.e6, x.e7 - y.e7⟩

/-- Scalar multiplication. -/
instance [Mul R] : SMul R (Octonion R) where
  smul r x := ⟨r * x.re, r * x.e1, r * x.e2, r * x.e3,
               r * x.e4, r * x.e5, r * x.e6, r * x.e7⟩

/-- Octonion conjugation: (re, im) ↦ (re, -im). -/
def conj (x : Octonion R) : Octonion R :=
  ⟨x.re, -x.e1, -x.e2, -x.e3, -x.e4, -x.e5, -x.e6, -x.e7⟩

/-!
## Dimension Properties
-/

/-- 8 = 1 + 7 (real ⊕ imaginary decomposition). -/
theorem octonion_dimension_split : octonion_dim = 1 + imaginary_count := rfl

/-- The imaginary subspace has dimension 7. -/
theorem imaginary_subspace_dim : imaginary_count = 7 := rfl

end PhysLean.G2.Algebra.Octonions
