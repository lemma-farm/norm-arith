module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Geometry.Manifold.PartitionOfUnity
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth cutoffs and uniform mollification

Two elementary approximation facts in a finite-dimensional real normed space, used to build
the smooth majorants of the kinetic Aleksandrov maximum principle.

* `exists_smooth_cutoff`: a compact set `K` inside an open set `U` carries a smooth cutoff
  `χ : E → [0,1]` equal to `1` on `K` and vanishing off `cthickening ε₀ K`, where
  `cthickening (2 * ε₀) K ⊆ U`.
* `exists_smooth_uniform_approx`: a continuous compactly supported nonnegative function is
  uniformly approximated, within any `η > 0`, by a nonnegative smooth function that vanishes
  off an arbitrarily small thickening of the support set.
-/
@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Metric
open scoped Pointwise Convolution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
/-- A compact set inside an open set carries a smooth `[0,1]`-valued cutoff equal to `1` on
the set and vanishing off a thickening whose double still lies in the open set. -/
theorem exists_smooth_cutoff {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ cthickening (2 * ε₀) K ⊆ U ∧
      ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
        (∀ z ∈ K, χ z = 1) ∧ ∀ z, z ∉ cthickening ε₀ K → χ z = 0 := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ / 2, half_pos hδ, by rwa [mul_div_cancel₀ _ two_ne_zero], ?_⟩
  have hs : IsClosed (thickening (δ / 2) K)ᶜ := isOpen_thickening.isClosed_compl
  have hd : Disjoint (thickening (δ / 2) K)ᶜ K :=
    disjoint_compl_left_iff.2 (self_subset_thickening (half_pos hδ) K)
  obtain ⟨χ, hχ, hrange, hzero, hone⟩ :=
    exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞)) hs hK.isClosed hd
  refine ⟨χ, hχ, fun z => hrange (mem_range_self z), fun z hz => (hone z).1 hz, fun z hz => ?_⟩
  refine (hzero z).1 ?_
  exact fun hz' => hz (thickening_subset_cthickening _ _ hz')
variable [MeasurableSpace E] [BorelSpace E]
end HypoellipticAleksandrov.KineticAleksandrov
