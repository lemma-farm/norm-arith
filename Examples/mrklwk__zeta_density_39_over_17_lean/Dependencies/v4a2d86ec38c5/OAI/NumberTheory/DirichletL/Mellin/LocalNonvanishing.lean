module
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.GaussSum.ThetaLocalRows
public import Mathlib
set_option autoImplicit false
@[expose] public section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
namespace TargetLocalReduction
end TargetLocalReduction
namespace ActualEisensteinCubic
open AddChar MulChar
end ActualEisensteinCubic
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
namespace ShortDraftHeckeBridge
abbrev O := ActualEisensteinSieve.O
noncomputable def normFiberCoeff (weight : Ideal O → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset, weight I
end ShortDraftHeckeBridge
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
open scoped ComplexConjugate
end ActualEisensteinCubic
open MulChar AddChar
namespace ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end ShortDraftLocal
end
end OAI
