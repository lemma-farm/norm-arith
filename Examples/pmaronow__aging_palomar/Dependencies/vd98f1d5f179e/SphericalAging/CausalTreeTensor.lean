module
public import Examples.pmaronow__aging_palomar.Dependencies.vd98f1d5f179e.SphericalAging.CausalTreePrefix
public import Examples.pmaronow__aging_palomar.Dependencies.vd98f1d5f179e.SphericalAging.HilbertSumTensor
public import Mathlib
set_option autoImplicit false
public section
/-! Canonical identification of the distributed causal-tree root tensor space
with the usual ordered completed tensor power of the tree Hilbert space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct InnerProductSpace ENNReal
open UniformSpace
namespace SphericalAging.CausalTree
attribute [local instance] Classical.propDecidable
local instance (α : Type) : DecidableEq α := Classical.decEq α
namespace HilbertDatum
end HilbertDatum
namespace HilbertDatum
end HilbertDatum
end SphericalAging.CausalTree
