module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.OrthogonalProjectionDensity
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.FourierReconstructionPairing
public import Mathlib
set_option autoImplicit false
/-!
# Concrete low-pass approximants of the orthogonal densities

The inverse square-integrable Fourier approximant is identified with the actual
Schwartz kernel convolved against the source measure. Its pointwise bound is
therefore a consequence of probability mass, as required in Lemma 5.3.
-/
@[expose] public section
noncomputable section
open MeasureTheory Filter SchwartzMap FourierTransform
open scoped ENNReal ContDiff
namespace FalconerThetaGauge
end FalconerThetaGauge
