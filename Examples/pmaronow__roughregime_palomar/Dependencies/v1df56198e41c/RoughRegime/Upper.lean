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
lemma intervalRho_lt_one (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) :
    intervalRho lo hi < 1 := by
  unfold intervalRho
  have hu := Real.sqrt_pos.mpr hlo
  have hv := Real.sqrt_pos.mpr (lt_trans hlo hlt)
  apply (div_lt_one (add_pos hv hu)).mpr
  linarith
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
end RoughRegime.Upper
