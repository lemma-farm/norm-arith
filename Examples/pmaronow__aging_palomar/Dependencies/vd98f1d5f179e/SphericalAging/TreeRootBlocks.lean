module
public import Examples.pmaronow__aging_palomar.Dependencies.vd98f1d5f179e.SphericalAging.TreeCoherentRoot
public import Examples.pmaronow__aging_palomar.Dependencies.vd98f1d5f179e.SphericalAging.HilbertTensorContraction
public import Mathlib
set_option autoImplicit false
public section
/-! Genuine binary height blocks of the completed-tensor coherent root. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace ENNReal NNReal TensorProduct Topology
open Set MeasureTheory Filter UniformSpace
namespace SphericalAging.TreeRootBlocks
open CausalTree CausalTree.HilbertDatum TreeCeilings TreeCoherentRoot
local instance (α : Type) : DecidableEq α := Classical.decEq α
end SphericalAging.TreeRootBlocks
