module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.vd757f5319ad4.CoarseDeGiorgi.Foundations.Euclid.Kernel
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.vd757f5319ad4.Homogenization.Sobolev.Fractional.Definitions
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
namespace CoarseDeGiorgi.Foundations.Euclid
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ}
/-- The unnormalized Euclidean fractional seminorm on an arbitrary set. -/
def eFracSeminorm (A : Set (Vec d)) (α r : ℝ) (u : Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ xy, euclidKernel ((d : ℝ) + α * r) r u xy
    ∂((volume.restrict A).prod (volume.restrict A))) ^ (1 / r)
end
end CoarseDeGiorgi.Foundations.Euclid
