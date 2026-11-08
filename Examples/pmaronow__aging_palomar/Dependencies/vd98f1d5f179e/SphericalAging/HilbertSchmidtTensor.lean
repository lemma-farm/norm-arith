module
public import Examples.pmaronow__aging_palomar.Dependencies.vd98f1d5f179e.SphericalAging.HilbertTensorContraction
public import Mathlib
set_option autoImplicit false
public section
/-! The genuine completed rank-one Hilbert--Schmidt space and its faithful
realization as bounded operators. The Hilbert norm is the actual Hilbert tensor
norm; the operator embedding is constructed and proved injective. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace TensorProduct
open UniformSpace Set
namespace SphericalAging.HilbertSchmidtTensor
open CausalTree CausalTree.HilbertDatum HilbertTensorContraction
end SphericalAging.HilbertSchmidtTensor
