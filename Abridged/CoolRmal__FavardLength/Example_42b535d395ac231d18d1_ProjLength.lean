import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- ==== Examples.CoolRmal__FavardLength.Examples.Example_42b535d395ac231d18d1_ProjLength ====
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

/-! ### The bound `√2` -/

theorem abs_cos_add_abs_sin_le_sqrt_two (θ : ℝ) : |cos θ| + |sin θ| ≤ √2 := by
  rw [Real.le_sqrt (by positivity) (by norm_num)]
  nlinarith [sq_abs (cos θ), sq_abs (sin θ), sin_sq_add_cos_sq θ,
    sq_nonneg (|cos θ| - |sin θ|)]
end Favard.BasicProof
