/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

VENDORED BASE MODULE.  This file is copied verbatim (apart from its import
paths and this header) from the author's Version 2.0 formalization at
https://github.com/DiarHaidary/Nelson-Nguyen-conjecture-upper-bound-palomar
(`SparseFockFormal/SparseStackDistribution.lean`).  The sketch distribution, the Parseval-frame
encoding of `U`, the finite-probability API and the operator-norm/trace
bridge are unchanged between Version 2.0 and Version 3.0 of the manuscript,
so they are reused rather than reproved.
-/
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Base.SparseStackModel
import Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v8aed2e66dcc8.SparseStackV3.Base.FiniteProbability
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SparseFock
namespace SparseStackDistribution
open SparseStackModel
noncomputable section
instance : Fintype Sign where
  elems := {.plus, .minus}
  complete x := by cases x <;> simp
@[simp] theorem card_sign : Fintype.card Sign = 2 := by decide
/-- One primitive, fully independent signed-hash selector. -/
abbrev SignedHash (b : ℕ) := Fin b × Sign
/-- The primitive selector law: uniform row and independent Rademacher sign. -/
def selectorLaw (b : ℕ) (hb : 0 < b) : FiniteLaw (SignedHash b) where
  weight := fun _ => 1 / (((2 : ℕ) : ℝ) * (b : ℝ))
  weight_nonneg := by
    intro _
    exact div_nonneg zero_le_one
      (mul_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg b))
  sum_weight := by
    simp [Fintype.card_prod]
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    field_simp
/-- Literal sample space for all primitive selectors. -/
abbrev RawSample (s b n : ℕ) := (Fin s × Fin n) → SignedHash b
/-- The actual product law.  Independence is supplied by the explicit product
weight, not by a proposition attached later. -/
def rawSampleLaw (s b n : ℕ) (hb : 0 < b) : FiniteLaw (RawSample s b n) :=
  FiniteLaw.independentProduct (fun _ : Fin s × Fin n => selectorLaw b hb)
/-- Forget the paired presentation and obtain the exact `Sample` consumed by
the deterministic SparseStack matrix definitions. -/
def toSample {s b n : ℕ} (z : RawSample s b n) : Sample s b n where
  h := fun p => (z p).1
  sign := fun p => (z p).2
@[simp] theorem toSample_hash {s b n : ℕ} (z : RawSample s b n)
    (g : Fin s) (i : Fin n) :
    (toSample z).hash g i = (z (g, i)).1 := rfl
@[simp] theorem toSample_sign {s b n : ℕ} (z : RawSample s b n)
    (g : Fin s) (i : Fin n) :
    (toSample z).sgn g i = (z (g, i)).2 := rfl
/-- Each signed row choice has probability exactly `1/(2b)`. -/
theorem selector_singleton {b : ℕ} (hb : 0 < b) (x : SignedHash b) :
    (selectorLaw b hb).prob {x} = 1 / (2 * (b : ℝ)) := by
  rw [FiniteLaw.prob_singleton]
  rfl
/-- Each primitive selector in the full sample has the prescribed marginal. -/
theorem rawSample_coordinate_singleton {s b n : ℕ} (hb : 0 < b)
    (p : Fin s × Fin n) (x : SignedHash b) :
    (rawSampleLaw s b n hb).prob {z | z p = x} = 1 / (2 * (b : ℝ)) := by
  simpa [rawSampleLaw, selectorLaw] using
    (FiniteLaw.prob_independentProduct_eq
      (fun _ : Fin s × Fin n => selectorLaw b hb) p x)
/-- Exact factorization of arbitrary coordinate events for the SparseStack
primitive sample. -/
theorem rawSample_cylinder {s b n : ℕ} (hb : 0 < b)
    (events : (Fin s × Fin n) → Set (SignedHash b)) :
    (rawSampleLaw s b n hb).prob (FiniteLaw.cylinder events) =
      ∏ p, (selectorLaw b hb).prob (events p) := by
  exact FiniteLaw.prob_independentProduct_cylinder
    (fun _ : Fin s × Fin n => selectorLaw b hb) events
/-- The hash marginal is uniform. -/
theorem selector_hash_uniform {b : ℕ} (hb : 0 < b) (a : Fin b) :
    (selectorLaw b hb).prob {x | x.1 = a} = 1 / (b : ℝ) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  simp only [FiniteLaw.prob, FiniteLaw.expect, FiniteLaw.indicator, selectorLaw,
    Set.mem_setOf_eq]
  rw [Fintype.sum_prod_type]
  simp
  field_simp
/-- The sign marginal is Rademacher. -/
theorem selector_sign_uniform {b : ℕ} (hb : 0 < b) (e : Sign) :
    (selectorLaw b hb).prob {x | x.2 = e} = 1 / 2 := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  cases e <;>
    simp only [FiniteLaw.prob, FiniteLaw.expect, FiniteLaw.indicator, selectorLaw,
      Set.mem_setOf_eq] <;>
    rw [Fintype.sum_prod_type] <;>
    simp <;>
    field_simp
end
end SparseStackDistribution
end SparseFock
