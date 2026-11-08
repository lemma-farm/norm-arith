module
public import Examples.pmaronow__aging_palomar.Dependencies.vc0770c57311b.SphericalAging.CriticalEndpoint
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
public section
/-!
# Differentiation of positive spectral Laplace transforms

No moments at time zero are assumed. At every strictly positive time,
exponential damping bounds every polynomial moment. This supplies the
justification for all derivatives used in Lemma 16.3 of the manuscript.
-/
open MeasureTheory Set
open scoped Topology
namespace SphericalAging.SpectralLaplace
noncomputable section
end
end SphericalAging.SpectralLaplace
