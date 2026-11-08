module
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.veb9de1d9de7b.SquaresInCircles.Common.Basic
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.veb9de1d9de7b.SquaresInCircles.Common.Trigonometry
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
lemma Q0_pos : 0 < Q0 := by norm_num [Q0]
lemma R0_sq : R0^2=Q0 := Real.sq_sqrt Q0_pos.le
lemma R0_pos : 0 < R0 := Real.sqrt_pos.mpr Q0_pos
lemma R0_bounds : 1.6885 < R0 ∧ R0 < 1.6886 := by
  constructor
  · rw [R0,Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  · rw [R0,Real.sqrt_lt' (by norm_num)]
    norm_num [Q0]
/-- The corners `(ρ0 + 1/2, ±1/2)` lie on the circle of radius `R0`. -/
lemma rho0_identity : (rho0+1/2)^2+1/4=Q0 := by
  have hs := Real.sq_sqrt (show 0 ≤ Q0-1/4 by norm_num [Q0])
  dsimp [rho0]
  nlinarith
lemma rho0_bounds : 1.11281 < rho0 ∧ rho0 < 1.11282 := by
  constructor
  · rw [rho0,lt_sub_iff_add_lt,Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  · rw [rho0,sub_lt_iff_lt_add,Real.sqrt_lt' (by norm_num)]
    norm_num [Q0]
namespace Wings
/-- `1/2 - coreUpper` and `1/2 + coreUpper`: the coefficients that the half-width
of a square and the box of the centre of C leave in the separating inequalities
of the wings. -/
def A : ℝ := 0.38718
def B : ℝ := 0.61282
end Wings
end SquaresInCircles.Six
