/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/MonotoneLimit.lean
-/
/-
# Strong limits of bounded monotone operator sequences (WP-B7, stage B)

A pointwise-convergent sequence of uniformly bounded operators has a bounded
pointwise limit (`pointwiseLimit`, no Banach–Steinhaus needed), and a
monotone sequence of positive contractions `0 ≤ Tₙ ≤ Tₙ₊₁ ≤ 1` converges
strongly: `‖(Tₙ − Tₘ)ξ‖² ≤ ⟪ξ, (Tₙ − Tₘ)ξ⟫` because `0 ≤ Tₙ − Tₘ ≤ 1`, and the
real sequence `⟪ξ, Tₙξ⟫` is monotone and bounded. The limit is a positive
contraction dominating every `Tₙ`. This is the analytic engine of the Borel
functional calculus (stage C). Infrastructure only; no manuscript statement.
-/
module
public import Mathlib
public import Examples.vidick__MIPRE_formalization.Dependencies.vb56476c3629b.MIPRE.Background.Repetition.CommutingRepetition.Resolver.Resolvent
public import Examples.vidick__MIPRE_formalization.Dependencies.vb56476c3629b.MIPRE.Background.Repetition.CommutingRepetition.Resolver.Douglas
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true
@[expose] public section
namespace CommutingRepetition
namespace StrongLimit
open scoped InnerProductSpace Topology
open Filter
set_option linter.unusedSectionVars false
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
/-! ## Pointwise limits of uniformly bounded sequences -/
section Pointwise
variable (T : ℕ → 𝓗 →L[ℂ] 𝓗) (C : ℝ) (hC : ∀ n, ‖T n‖ ≤ C)
  (hex : ∀ ξ, ∃ l, Tendsto (fun n => T n ξ) atTop (𝓝 l))
end Pointwise
/-! ## Positive contractions -/
variable (T : ℕ → 𝓗 →L[ℂ] 𝓗) (hmono : Monotone T) (h0 : 0 ≤ T 0) (h1 : ∀ n, T n ≤ 1)
include hmono h0 h1
end StrongLimit
end CommutingRepetition
end
