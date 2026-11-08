module
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v99a3c95ae15b.SquaresInCircles.Common.Basic
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
/-- The ceiling on the squared radius, just above `qStar`. -/
def Q0 : ℝ := 2.85118
/-- The largest radial offset of a square in the disk: its far corner
`(ρ0 + 1/2, 1/2)` lies on the circle of radius `R0`. -/
def rho0 : ℝ := Real.sqrt (Q0-1/4)-1/2
/-- The bound on the coordinates of the centre of C in its frame. -/
def c0 : ℝ := rho0-1
/-- The largest transverse coordinate of an exterior square that avoids the
core: its far corner at `a = aMin`. -/
def U0 : ℝ := Real.sqrt (Q0-(5/2-rho0)^2)-1/2
/-- The corners `(ρ0 + 1/2, ±1/2)` lie on the circle of radius `R0`. -/
lemma rho0_identity : (rho0+1/2)^2+1/4=Q0 := by
  have hs := Real.sq_sqrt (show 0 ≤ Q0-1/4 by norm_num [Q0])
  dsimp [rho0]
  nlinarith
lemma rho0_sq : rho0^2+rho0+1/2=Q0 := by
  nlinarith [rho0_identity]
lemma rho0_bounds : 1.11281 < rho0 ∧ rho0 < 1.11282 := by
  constructor
  · rw [rho0,lt_sub_iff_add_lt,Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  · rw [rho0,sub_lt_iff_lt_add,Real.sqrt_lt' (by norm_num)]
    norm_num [Q0]
lemma c0_bounds : 0.11281 < c0 ∧ c0 < 0.11282 := by
  dsimp [c0]
  constructor <;> linarith [rho0_bounds.1,rho0_bounds.2]
lemma U0_radicand : Q0-(5/2-rho0)^2=6*rho0-23/4 := by
  nlinarith [rho0_sq]
lemma U0_upper : U0 < 0.463 := by
  rw [U0,sub_lt_iff_lt_add,Real.sqrt_lt' (by norm_num),U0_radicand]
  linarith [rho0_bounds.2]
/-! ### Decimal ceilings -/
namespace Wings
end Wings
end SquaresInCircles.Six
