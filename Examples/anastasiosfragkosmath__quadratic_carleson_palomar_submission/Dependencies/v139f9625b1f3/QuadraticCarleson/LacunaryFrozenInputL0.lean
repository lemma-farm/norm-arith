import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.LacunaryMiddleOperator
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The genuine frozen block input belongs to the paper's test domain

Every stopping cell meets the support of the original input and has length
at most the data-dependent root length. Thus all stopping cells lie in one
bounded enlargement of a compact set supporting the original input. Exact
disjointness also gives a pointwise `2 A_k` bound for any frozen scale block,
with no factor depending on its number of scales.
-/
open MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace LacunaryFrozenInputL0
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms CanonicalScaleAtoms
open PositiveEndpointOptimization LacunaryMiddleRange LacunaryMiddleOperator
set_option autoImplicit false
theorem norm_canonicalLevelBadPart_le_two_mul
    {A : ℕ → ℝ} (f : ℝ → ℂ) {k : ℕ} (hAk : 0 ≤ A k) (x : ℝ) :
    ‖canonicalLevelBadPart A f k x‖ ≤ 2 * A k := by
  by_cases hx : x ∈ stoppingBadUnion f
  · obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    rw [canonicalLevelBadPart_eq_atom_of_mem A c hc]
    exact norm_levelAtom_le_two_mul hAk (stoppingLength_pos c) x
  · rw [canonicalLevelBadPart_eq_zero_of_notMem A hx, norm_zero]
    positivity
end LacunaryFrozenInputL0
end QuadraticCarleson
