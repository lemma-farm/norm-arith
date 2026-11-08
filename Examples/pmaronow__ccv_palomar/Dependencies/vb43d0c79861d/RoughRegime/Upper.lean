module
public import Mathlib
@[expose] public section
/-!
Algebraic and analytic ingredients of Section 4.
The declarations explicitly document which paper claims they cover.
-/
noncomputable section
open scoped BigOperators
open Complex
namespace RoughRegime.Upper
def intervalCenter (lo hi : ℝ) : ℝ := (hi + lo) / 2
def intervalHalfWidth (lo hi : ℝ) : ℝ := (hi - lo) / 2
def intervalGeometricMean (lo hi : ℝ) : ℝ := Real.sqrt (lo * hi)
def intervalRho (lo hi : ℝ) : ℝ :=
  (Real.sqrt hi - Real.sqrt lo) / (Real.sqrt hi + Real.sqrt lo)
lemma intervalRho_pos (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    0 < intervalRho lo hi := by
  unfold intervalRho
  exact div_pos (sub_pos.mpr (Real.sqrt_lt_sqrt hlo.le hlt))
    (add_pos (Real.sqrt_pos.mpr (lt_trans hlo hlt)) (Real.sqrt_pos.mpr hlo))
open MeasureTheory ProbabilityTheory
lemma interval_argument_mem (lo hi x : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (hx : x ∈ Set.Icc lo hi) :
    (x - intervalCenter lo hi) / intervalHalfWidth lo hi ∈ Set.Icc (-1) 1 := by
  have hd : 0 < intervalHalfWidth lo hi := by unfold intervalHalfWidth; positivity
  constructor
  · apply (le_div_iff₀ hd).mpr
    unfold intervalCenter intervalHalfWidth
    linarith [hx.1]
  · apply (div_le_iff₀ hd).mpr
    unfold intervalCenter intervalHalfWidth
    linarith [hx.2]
def ExponentSlots {p : ℕ} (α : Fin p →₀ ℕ) := Σ i : Fin p, Fin (α i)
instance {p : ℕ} (α : Fin p →₀ ℕ) : Fintype (ExponentSlots α) := by
  unfold ExponentSlots
  infer_instance
lemma chebyshev_abs_le_one (y : ℝ) (hy : y ∈ Set.Icc (-1) 1) (k : ℕ) :
    |(Polynomial.Chebyshev.T ℝ (k : ℕ)).eval y| ≤ 1 := by
  have hc : Real.cos (Real.arccos y) = y := Real.cos_arccos hy.1 hy.2
  rw [← hc, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _
end RoughRegime.Upper
