module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SphericalAging.SphereTensorObservable
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SphericalAging.OrthogonalGaussianDisclosure
set_option autoImplicit false
public section
/-! The literal ordered tensor action of a vector orthogonal map. Its
isometry, Gaussian invariance and measurable evaluation are derived from
actual pure tensors, rather than supplied as adaptive frame assumptions. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.TensorOrthogonalAction
open Set MeasureTheory ProbabilityTheory FiniteModel HardSphereDynamics
open AdaptiveGradientDisclosure SphereTensorObservable
open scoped InnerProductSpace BigOperators
end SphericalAging.TensorOrthogonalAction
