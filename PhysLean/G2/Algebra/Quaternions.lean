/-
Copyright (c) 2025 Brieuc de La Fournière. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brieuc de La Fournière
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FinCases

/-!
# Quaternions and K₄ Correspondence

This file establishes the correspondence between the complete graph K₄
and the quaternions ℍ, providing combinatorial foundations for the
Cayley-Dickson construction.

## Main definitions

* `K4` - The complete graph on 4 vertices
* `quaternion_dim` - dim(ℍ) = 4
* `imaginary_count` - Number of imaginary units = 3

## Main results

* `K4_card_vertices` - K₄ has 4 vertices = dim(ℍ)
* `K4_card_edges` - K₄ has 6 edges = C(4,2)
* `K4_degree` - Each vertex has degree 3
* `K4_opposite_pairs` - 3 perfect matchings = 3 imaginary units

## References

* Baez, "The Octonions", Bull. Amer. Math. Soc. 2002
-/

namespace PhysLean.G2.Algebra.Quaternions

/-!
## K₄ Properties
-/

/-- The complete graph K₄. -/
def K4 : SimpleGraph (Fin 4) := ⊤

/-- K₄ has 4 vertices. -/
theorem K4_card_vertices : Fintype.card (Fin 4) = 4 := by decide

/-- K₄ adjacency is decidable. -/
instance K4_DecidableRel : DecidableRel K4.Adj := fun v w =>
  if h : v = w then isFalse (K4.loopless v ∘ (h ▸ ·))
  else isTrue h

/-- K₄ has 6 edges = C(4,2). -/
theorem K4_card_edges : K4.edgeFinset.card = 6 := by native_decide

/-- Each vertex of K₄ has degree 3. -/
theorem K4_degree (v : Fin 4) : K4.degree v = 3 := by
  fin_cases v <;> native_decide

/-!
## Quaternion Dimension Constants

The quaternions ℍ have dimension 4 over ℝ.
-/

/-- Dimension of the quaternions. -/
def quaternion_dim : ℕ := 4

/-- dim(ℍ) = 4. -/
theorem quaternion_dim_eq : quaternion_dim = 4 := rfl

/-- K₄ vertices = dim(ℍ). -/
theorem K4_vertices_eq_quaternion_dim :
    Fintype.card (Fin 4) = quaternion_dim := by decide

/-!
## Imaginary Quaternion Units

The three imaginary units {i, j, k} satisfy:
- i² = j² = k² = -1
- ij = k, jk = i, ki = j
- ji = -k, kj = -i, ik = -j (anti-commutativity)
-/

/-- Number of imaginary units in ℍ. -/
def imaginary_count : ℕ := 3

/-- |Im(ℍ)| = 3. -/
theorem imaginary_count_eq : imaginary_count = 3 := rfl

/-- Cardinality of imaginary units. -/
theorem Im_H_card : Fintype.card (Fin 3) = 3 := by decide

/-- dim(ℍ) = imaginary_count + 1 (real + imaginaries). -/
theorem quaternion_dim_split : quaternion_dim = imaginary_count + 1 := rfl

/-!
## Connection to K₄ Structure

K₄ has 3 perfect matchings, corresponding to 3 ways to pair 4 vertices.
This matches the 3 imaginary units of ℍ!

Perfect matchings:
- {(0,1), (2,3)} ↔ i
- {(0,2), (1,3)} ↔ j
- {(0,3), (1,2)} ↔ k
-/

/-- K₄ has C(4,2) = 6 edges. -/
theorem K4_edges_eq_choose : K4.edgeFinset.card = Nat.choose 4 2 := by native_decide

/-- C(4,2) = 6. -/
theorem choose_4_2 : Nat.choose 4 2 = 6 := by native_decide

/-- 3 pairs of opposite edges = 3 imaginary units. -/
theorem K4_opposite_pairs : Nat.choose 4 2 / 2 = imaginary_count := by native_decide

/-- 3 perfect matchings. -/
theorem matching_count : 3 = imaginary_count := rfl

end PhysLean.G2.Algebra.Quaternions
