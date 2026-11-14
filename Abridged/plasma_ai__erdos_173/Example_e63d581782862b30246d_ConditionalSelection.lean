module

public import Mathlib
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Topology.Separation.CompletelyRegular

-- ==== Examples.plasma_ai__erdos_173.Examples.Example_e63d581782862b30246d_ConditionalSelection ====
-- Copied from openai/math at adc7f124 (same path under lean/) and modified; see OAI/README.md.
set_option autoImplicit false
@[expose] public section
namespace OAI
noncomputable section
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
namespace EuclideanFiveColor.GoodFiber
variable {W ι T : Type*} [MeasurableSpace W] [Fintype ι] [Nonempty ι] [Fintype T]
end EuclideanFiveColor.GoodFiber
open MeasureTheory
namespace EuclideanFiveColor.Approximation
variable {A X : Type*} [PseudoMetricSpace A] [MeasurableSpace X]
variable [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
end EuclideanFiveColor.Approximation
open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.ConditionalFiber
variable {X W G V : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W] [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
end EuclideanFiveColor.ConditionalFiber
namespace EuclideanFiveColor.FiniteModule
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open ConditionalFiber
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
variable {X W ι T : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W] [Fintype ι] [Nonempty ι] [Fintype T]
end EuclideanFiveColor.FiniteModule
open scoped BigOperators
namespace EuclideanFiveColor.FiniteBins
variable {A : Type*} [PseudoMetricSpace A]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
lemma linear_combination_dist_bound {q : ℕ} (H : Fin q → V)
    (b c : Fin q → ℂ) :
    dist (∑ i, b i • H i) (∑ i, c i • H i) ≤
      dist b c * ∑ i, ‖H i‖ := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖b i • H i - c i • H i‖ := norm_sum_le _ _
    _ ≤ ∑ i, dist b c * ‖H i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sub_smul, norm_smul]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [dist_eq_norm] using dist_le_pi_dist b c i) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]
end EuclideanFiveColor.FiniteBins
end
end OAI
