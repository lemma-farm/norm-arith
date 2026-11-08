import Examples.CoolRmal__FavardLength.Dependencies.vaf34edf3e2c6.FavardLength.BasicProof.Cantor
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The projection length

Finiteness, boundedness, monotonicity in the depth, measurability in the angle, and the two
reflection symmetries `θ ↦ π - θ` and `θ ↦ π/2 - θ` of the projection length
`λ(π_θ(K_n))`.

Measurability is proved without any continuity argument: for a compact `K ⊆ ℝ²`, the set
`{(θ, x) | x ∈ π_θ(K)}` is closed (it is the image of a closed set under a projection along the
compact factor `K`), so its sections have measurable measure by `measurable_measure_prodMk_left`.
-/
open MeasureTheory Set Real
namespace Favard.BasicProof
theorem volume_proj_image_fourCorner_ne_top (n : ℕ) (θ : ℝ) :
    volume (proj θ '' fourCorner n) ≠ ⊤ :=
  (isCompact_proj_image_fourCorner θ n).measure_lt_top.ne
theorem projLength_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ projLength n θ :=
  ENNReal.toReal_nonneg
/-! ### The bound `√2` -/
/-- The projection of `[0,1]²` in an arbitrary direction lies in an interval of length
`|cos θ| + |sin θ|`. -/
theorem proj_image_unitSquare_subset (θ : ℝ) :
    proj θ '' (Icc 0 1 ×ˢ Icc 0 1) ⊆
      Icc (min 0 (cos θ) + min 0 (sin θ)) (max 0 (cos θ) + max 0 (sin θ)) := by
  rintro _ ⟨⟨x, y⟩, ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩, rfl⟩
  simp only [proj]
  have key : ∀ c t : ℝ, 0 ≤ t → t ≤ 1 → min 0 c ≤ t * c ∧ t * c ≤ max 0 c := by
    intro c t h0 h1
    rcases le_total 0 c with hc | hc
    · rw [min_eq_left hc, max_eq_right hc]
      constructor <;> nlinarith
    · rw [min_eq_right hc, max_eq_left hc]
      constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := key (cos θ) x hx0 hx1
  obtain ⟨h3, h4⟩ := key (sin θ) y hy0 hy1
  exact ⟨by linarith, by linarith⟩
theorem abs_cos_add_abs_sin_le_sqrt_two (θ : ℝ) : |cos θ| + |sin θ| ≤ √2 := by
  rw [Real.le_sqrt (by positivity) (by norm_num)]
  nlinarith [sq_abs (cos θ), sq_abs (sin θ), sin_sq_add_cos_sq θ,
    sq_nonneg (|cos θ| - |sin θ|)]
end Favard.BasicProof
