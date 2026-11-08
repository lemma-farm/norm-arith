module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitFlow
/-!
# Convergence of the Lie splitting for a cell solution

For a classical cell solution `h` of `∂ₛh + B·∇h = κΔh` (`κ = μ/4π²`) the split operator with
`n` steps applied to the quasi-periodic exponential converges uniformly to `h(1)`, with rate
`n^{-β/2}`.  The proof is a local error estimate for one step (Taylor expansion in space and the
mean value theorem in time) followed by a telescoping sum, using that each step is a
sup-norm contraction.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss
variable {L M : ℕ} {S : ℕ → ℝ}
end AnomDiss
