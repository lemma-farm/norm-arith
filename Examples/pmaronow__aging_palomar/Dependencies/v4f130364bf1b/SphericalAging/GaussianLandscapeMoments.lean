module
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.GaussianLandscape
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
set_option autoImplicit false
public section
/-!
# Uniform Gaussian landscape moments

The proved actual Gaussian tail is integrated by layer cake. A single
exponential square moment bound dominates every nonnegative real power and
every exponential moment, uniformly over dimensions N≥1.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SphericalAging.GaussianLandscapeMoments
open FiniteModel GaussianLandscape
end SphericalAging.GaussianLandscapeMoments
