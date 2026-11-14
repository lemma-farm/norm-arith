module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

-- ==== Examples.vltanh__lean4_squares_in_circles.Dependencies.veb9de1d9de7b.SquaresInCircles.Six.Constants ====
public section
/-!
# Six squares: the constants

The constants of the six-square proof, each with one decimal bracket.

The model (defined with the statement, in `Geometry.lean`) is built from
`h = √2/2` and the smaller root `s*` of `s² - A s + B`; `t*`, `d*` and the
squared radius `q* = 2s*² + 4s* + 5/2` follow from it. The far corners of E and
W and the far vertices of D lie on the circle of squared radius `q*`. The
stress of the model has weight `1` on the four contacts of
C, `r* = (s* + 1/2)/(s* + 3/2)` on N–W and E–S, and `m* = (1 + r*) k*`, with
`k* = (t* + 1/2)/(3/2 - s*)`, on W–D and D–S; the force on D has length
`diagonalK = 2h m*`, the centre of D lies at distance `ρ* = √(q* - 1/4) - 1/2`
from the disk centre, and `pairBase = m* (1/2 - t*)`. The forces of the model
point at the far corners of N and W on the circle, which gives their lengths,
and `2 pairBase + diagonalK (1 - ρ*) = 0` because `ρ* = 2h d*`. The brackets
have as many decimals as their uses need: seven or eight for `h`, `s*`, `t*`,
`r*`, `k*` and `m*`, from which the others are computed, and at most five for
the rest. `s*` comes from the sign of its quadratic, the others from it by
products, quotients and square roots.

The normalization works below the ceiling `Q0 = 2.85118` on the squared radius,
less than `3·10⁻⁶` above `q*`. With `R0 = √Q0`, the number
`ρ0 = √(Q0 - 1/4) - 1/2` is the largest radial coordinate of a square in the
disk, `c0 = ρ0 - 1` bounds the centre of the central square C,
`coreRadius = 3/2 - ρ0` is the radius of a disk about the origin inside C,
`aMin = 2 - ρ0` is the least radial coordinate of a square outside that disk and
`U0` its largest transverse coordinate. The decimals `radiusBound`, `rhoBound`,
`coreLower` and `coreUpper` stand for `R0`, `ρ0` and `c0`, rounded, in the
estimates, and `A` and `B` for `1/2 ∓ coreUpper`.
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles.Six
/-! ### The model -/
def Q0 : ℝ := 2.85118
/-- The radius of the disk of squared radius `Q0`. -/
def R0 : ℝ := Real.sqrt Q0
/-- The largest radial offset of a square in the disk: its far corner
`(ρ0 + 1/2, 1/2)` lies on the circle of radius `R0`. -/
def rho0 : ℝ := Real.sqrt (Q0-1/4)-1/2

namespace Wings

end Wings
end SquaresInCircles.Six

end
end
end

-- ==== Examples.vltanh__lean4_squares_in_circles.Examples.Example_acd6944fc6fafe8d935b_Caps ====
/-!
# Six squares: squares in a deep cap

A square in the closed disk of radius `R0` that lies beyond a line whose normal
makes the angle `t`, `|t| ≤ π/4`, with an axis of the square keeps the line
within `capDepth |t|` of the origin: with `A = |a| + 1/2` and `B = |b| + 1/2` on
the disk `A² + B² ≤ Q0`, the support `A cos t + B sin t` of the far corner along
the normal is at most its value at the corner `(ρ0 + 1/2, 1/2)` of the disk
below the angle `capSwitch = arcsin (1/(2 R0))`, and at most `R0` beyond it. A
cap at least `coreRadius` deep therefore forces `|t| < 2/5`, and one at least
`1/2` deep forces `|t| < 1/4`. In a cap `x ≥ h` with `h ≥ coreRadius` the square
has `|b| < a`, `h + 1/2 ≤ a ≤ ρ0`, `|b| ≤ U0` and `|b| < 1/2`
(`deep_cap_bounds`), and it contains the point `(h + 1/2, 0)` (`cap_piercing`):
otherwise its far vertex would leave the disk, by a polynomial positive on a
rectangle. A square with `a ≥ 0` and `|b| < 1/2` faces such a cap: its phase
lies within `2/5` of the normal modulo `2π` (`deep_cap_faces`), since a quarter
or a half turn would make the cap face a short or a negative coordinate.
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles.Six.Normalization
/-! ### The cap depth -/
/-- The angle `arcsin (1/(2 R0))` at which the two branches of the cap depth
meet. -/
def capSwitch : ℝ := Real.arcsin (1 / (2 * R0))
/-- The cap branch: the far corner of the square at `(ρ0 + 1/2, 1/2)`. -/
def capFirst (t : ℝ) : ℝ :=
  (rho0 - 1 / 2) * Real.cos t - (1 / 2) * Real.sin t
/-- The vertex branch: the far vertex on the circle along the normal. -/
def capSecond (t : ℝ) : ℝ := R0 - Real.cos t - Real.sin t
/-- The depth of the deepest cap that holds a square at the angle `t`,
`0 ≤ t ≤ π/4`, to the cap normal. -/
def capDepth (t : ℝ) : ℝ :=
  if t ≤ capSwitch then capFirst t else capSecond t


set_option linter.unusedVariables false in
/-- A square with `h + (|cos t| + |sin t|)/2 ≤ a cos t - b sin t`, the support
inequality of a square in the cap `x ≥ h`, has `h ≤ capDepth |t|`, for
`|t| ≤ π/4`. -/
theorem cap_support_bound_signed {a b height t : ℝ}
    (ht : |t| ≤ Real.pi / 4)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : height + (|Real.cos t| + |Real.sin t|) / 2 ≤
      a * Real.cos t - b * Real.sin t) 
    (h_SquaresInCircles_Six_Normalization_cap_low_branch_slope : ∀ {t : ℝ},
      0 ≤ t →
        t ≤ SquaresInCircles.Six.Normalization.capSwitch →
          (SquaresInCircles.Six.rho0 + 1 / 2) * Real.sin t ≤ 1 / 2 * Real.cos t)
    (h_SquaresInCircles_Six_R0_pos : 0 < SquaresInCircles.Six.R0)
    (h_SquaresInCircles_Six_R0_sq : SquaresInCircles.Six.R0 ^ 2 = SquaresInCircles.Six.Q0)
    (h_SquaresInCircles_Six_rho0_bounds : 1.11281 < SquaresInCircles.Six.rho0 ∧ SquaresInCircles.Six.rho0 < 1.11282)
    (h_SquaresInCircles_Six_disk_corner_support : ∀ {A B a b c s : ℝ},
      0 < a →
        b ≤ B →
          0 ≤ c →
            a ^ 2 + b ^ 2 = SquaresInCircles.Six.Q0 →
              A ^ 2 + B ^ 2 ≤ SquaresInCircles.Six.Q0 → a * s ≤ b * c → A * c + B * s ≤ a * c + b * s)
    (h_SquaresInCircles_Six_rho0_identity : (SquaresInCircles.Six.rho0 + 1 / 2) ^ 2 + 1 / 4 = SquaresInCircles.Six.Q0)
    (h_SquaresInCircles_east_quadrant_trig : ∀ {t : ℝ}, 0 ≤ t → t ≤ Real.pi / 4 → 7 / 10 ≤ Real.cos t ∧ 0 ≤ Real.sin t ∧ Real.sin t ≤ Real.cos t)
    :
    height ≤ capDepth |t| := by
  have htr := h_SquaresInCircles_east_quadrant_trig (abs_nonneg t) ht
  have hcos : Real.cos |t| = |Real.cos t| := by
    rw [Real.cos_abs, abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [(abs_le.mp ht).1, Real.pi_pos], by linarith [(abs_le.mp ht).2, Real.pi_pos]⟩)]
  have hsin : Real.sin |t| = |Real.sin t| :=
    (Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_pos])).symm
  have hA : a * Real.cos t ≤ |a| * Real.cos |t| := by
    rw [hcos, ← abs_mul]; exact le_abs_self _
  have hB : -(b * Real.sin t) ≤ |b| * Real.sin |t| := by
    rw [hsin, ← abs_mul]; exact neg_le_abs _
  have hab : height ≤ (|a| + 1 / 2) * Real.cos |t| + (|b| + 1 / 2) * Real.sin |t| -
      Real.cos |t| - Real.sin |t| := by
    rw [← hcos, ← hsin] at hcap
    linarith
  unfold capDepth
  split_ifs with hbranch
  · have hcorner := h_SquaresInCircles_Six_disk_corner_support
      (A := |a| + 1 / 2) (B := |b| + 1 / 2) (a := rho0 + 1 / 2) (b := (1 : ℝ) / 2)
      (c := Real.cos |t|) (s := Real.sin |t|)
      (by linarith [h_SquaresInCircles_Six_rho0_bounds.1]) (by linarith [abs_nonneg b]) (by linarith [htr.1])
      (by nlinarith [h_SquaresInCircles_Six_rho0_identity]) hbox (h_SquaresInCircles_Six_Normalization_cap_low_branch_slope (abs_nonneg t) hbranch)
    dsimp [capFirst]
    linarith
  · have hround : (|a| + 1 / 2) * Real.cos |t| + (|b| + 1 / 2) * Real.sin |t| ≤ R0 := by
      nlinarith [sq_nonneg ((|a| + 1 / 2) * Real.sin |t| - (|b| + 1 / 2) * Real.cos |t|),
        Real.sin_sq_add_cos_sq |t|, h_SquaresInCircles_Six_R0_sq, h_SquaresInCircles_Six_R0_pos, abs_nonneg a, abs_nonneg b, htr.1, htr.2.1]
    dsimp [capSecond]
    linarith
/-! ### The angle of a square in a deep cap -/
end SquaresInCircles.Six.Normalization
