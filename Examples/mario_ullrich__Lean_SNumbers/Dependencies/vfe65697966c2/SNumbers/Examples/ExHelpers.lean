/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Examples.mario_ullrich__Lean_SNumbers.Dependencies.vfe65697966c2.SNumbers.Basic
import Examples.mario_ullrich__Lean_SNumbers.Dependencies.vfe65697966c2.SNumbers.PiLpCoordinates
import Mathlib.Analysis.Convex.KreinMilman
/-!
# Shared helpers for the worked examples

Geometric and rank ingredients used by more than one of the worked examples
(`SNumbers.Examples.Identity`, `SNumbers.Examples.DiagonalMatrices`), collected
here so that each statement is proved once.

## Main contents

* `rank_id_piLp` — the identity on `ℓ^p_k` has rank `k` (as a `Cardinal`); the
  standard way to bound the rank of an approximant that factors through `ℓ^p_k`.
* `exists_mem_ker_coords` — **coordinate pigeonhole**: a subspace of `𝕜^m` whose
  dimension exceeds the size of a coordinate set contains a nonzero vector
  vanishing on that set.
* `exists_flat_vector_weighted` — **weighted flatness lemma**: a subspace of
  dimension `≥ k` contains a vector dominated by a nonnegative weight `w` that
  attains `w` on at least `k` coordinates.
* `exists_flat_vector` — the unweighted case `w ≡ 1`, with nonvanishing.

The flatness lemmas are the geometric heart of the Gelfand-width lower bounds
(Pietsch, *Eigenvalues and s-numbers*, §11.11): they produce, inside any
subspace of large enough dimension, a vector that is "flat" in the sense of
saturating a prescribed coordinate bound on many coordinates. The proof is an
extreme-point argument (Krein–Milman) combined with the pigeonhole lemma.
-/
universe u
open scoped ENNReal
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
/-! ## Exponents -/
/-- A finite exponent `p` with `1 ≤ p` has `0 < p.toReal`. The `Fact (1 ≤ p)`
instance is how `PiLp` carries the admissibility of the exponent, so this is the
standard way to enter the `rpow` computations. -/
lemma toReal_pos_of_ne_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) : 0 < p.toReal :=
  ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one Fact.out).ne' hp
/-! ## Rank of the identity on `ℓ^p_k` -/
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
/-- The rank of the identity on `ℓ^p_k` is `k` (as a `Cardinal`). Used to bound
the rank of finite-rank approximants that factor through `ℓ^p_k`. -/
lemma rank_id_piLp (k : ℕ) :
    (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin k => 𝕜))).rank = (k : Cardinal) := by
  have h1 : (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin k => 𝕜))).rank
      = Module.rank 𝕜 (PiLp p (fun _ : Fin k => 𝕜)) := by
    rw [ContinuousLinearMap.rank, ContinuousLinearMap.coe_id]
    show Module.rank 𝕜 (LinearMap.range (LinearMap.id : _ →ₗ[𝕜] _)) = _
    rw [LinearMap.range_id]; exact Submodule.topEquiv.rank_eq
  rw [h1, ← Module.finrank_eq_rank, finrank_piLp]
/-! ## The coordinate pigeonhole -/
end SNumbers
