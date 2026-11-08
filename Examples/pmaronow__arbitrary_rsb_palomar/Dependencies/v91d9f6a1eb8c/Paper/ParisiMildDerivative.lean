module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v91d9f6a1eb8c.Paper.HeatGradient
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v91d9f6a1eb8c.Paper.ParisiLocal
set_option autoImplicit false
@[expose] public section
/-! # The local gradient fixed point is the actual gradient of its potential

Gaussian smoothing differentiates the bounded measurable nonlinear source.
Its `1/√(s-t)` derivative bound is integrable in time, so dominated
differentiation identifies the mild gradient with the spatial derivative of
the genuine potential Duhamel formula.
-/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace Paper
end Paper
