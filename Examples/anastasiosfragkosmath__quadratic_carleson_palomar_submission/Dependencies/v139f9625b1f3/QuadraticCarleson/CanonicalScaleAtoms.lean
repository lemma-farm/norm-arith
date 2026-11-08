import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveStoppingBadRecombination
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Canonical stopping atoms sliced by their exact dyadic lengths

The scale class is exactly `2^j ≤ length < 2^(j+1)`. The construction is
generic in the magnitude amplitudes and therefore covers both the full and
lacunary partitions. No interval family is supplied as an assumption.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace CanonicalScaleAtoms
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms CalderonZygmundLevelRecombination
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate
open PositiveStoppingBadEstimate
noncomputable def canonicalLevelBadPart (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  disjointLevelAtomSum A f k (stoppingCenter (f := f)) stoppingLength
theorem canonicalLevelBadPart_eq_atom_of_mem (A : ℕ → ℝ) {f : ℝ → ℂ}
    (c : stoppingCell f) {x : ℝ} (hx : x ∈ c.1.interval (rootLength f)) (k : ℕ) :
    canonicalLevelBadPart A f k x =
      levelAtom A f k (stoppingCenter c) (stoppingLength c) x := by
  classical
  unfold canonicalLevelBadPart disjointLevelAtomSum
  apply tsum_eq_single c
  intro d hdc
  exact levelAtom_eq_zero_of_other_mem centeredStoppingIntervals_pairwiseDisjoint hdc
    (by simpa only [centeredInterval_eq_stoppingInterval] using hx)
theorem canonicalLevelBadPart_eq_zero_of_notMem (A : ℕ → ℝ) {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ stoppingBadUnion f) (k : ℕ) : canonicalLevelBadPart A f k x = 0 := by
  have hz (c : stoppingCell f) :
      levelAtom A f k (stoppingCenter c) (stoppingLength c) x = 0 := by
    apply levelAtom_eq_zero_of_not_mem
    rw [centeredInterval_eq_stoppingInterval]
    exact fun hc ↦ hx (mem_iUnion.mpr ⟨c, hc⟩)
  simp only [canonicalLevelBadPart, disjointLevelAtomSum, hz, tsum_zero]
end CanonicalScaleAtoms
end QuadraticCarleson
