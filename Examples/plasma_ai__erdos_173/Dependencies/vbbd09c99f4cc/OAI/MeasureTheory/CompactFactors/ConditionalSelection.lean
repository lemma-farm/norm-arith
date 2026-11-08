module
-- Copied from openai/math at adc7f124 (same path under lean/) and modified; see OAI/README.md.
public import Examples.plasma_ai__erdos_173.Dependencies.vbbd09c99f4cc.OAI.Analysis.PlaneSpectrum.PhaseCollision
public import Mathlib
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Topology.Separation.CompletelyRegular
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
omit [MeasurableSpace X] in
lemma dist_sq_four_points (a b c d : A) :
    dist a d ^ 2 ≤ 3*(dist a b ^ 2 + dist b c ^ 2 + dist d c ^ 2) := by
  have ht : dist a d ≤ dist a b + dist b c + dist d c := by
    have := dist_triangle a b d
    have := dist_triangle b c d
    rw [dist_comm c d] at this
    linarith
  have ha := dist_nonneg (x := a) (y := b)
  have hb := dist_nonneg (x := b) (y := c)
  have hc := dist_nonneg (x := d) (y := c)
  have hd := dist_nonneg (x := a) (y := d)
  nlinarith [sq_nonneg (dist a b - dist b c), sq_nonneg (dist a b - dist d c),
    sq_nonneg (dist b c - dist d c)]
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
end EuclideanFiveColor.FiniteBins
end
end OAI
