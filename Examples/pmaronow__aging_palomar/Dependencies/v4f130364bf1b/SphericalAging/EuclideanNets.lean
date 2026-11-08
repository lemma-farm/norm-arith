module
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.FiniteModel
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
set_option autoImplicit false
public section
/-! Finite unit-sphere nets with dimension-exponential cardinality, obtained
from actual maximal separated sets and the disjoint-ball Haar volume argument. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory Module
open scoped NNReal ENNReal
namespace SphericalAging.EuclideanNets
open FiniteModel
end SphericalAging.EuclideanNets
