module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Tactic
set_option autoImplicit false
public section
/-!
# The actual ordered Gaussian tensor model

The disorder is the finite product of standard real Gaussian laws indexed by
all ordered p-tuples. No symmetrization is performed. The Hamiltonian has
exactly the normalization of Section 3. Its mean and covariance below are
proved by integration against this actual law, not postulated as model axioms.
-/
noncomputable section
namespace SphericalAging.FiniteModel
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
@[expose] abbrev TensorIndex (N p : ℕ) := Fin p → Fin N
@[expose] abbrev Disorder (N p : ℕ) := TensorIndex N p → ℝ
@[expose] def disorderLaw (N p : ℕ) : Measure (Disorder N p) :=
  Measure.pi (fun _ : TensorIndex N p => gaussianReal 0 1)
instance disorderLaw_isProbability (N p : ℕ) : IsProbabilityMeasure (disorderLaw N p) := by
  unfold disorderLaw
  infer_instance
end SphericalAging.FiniteModel
