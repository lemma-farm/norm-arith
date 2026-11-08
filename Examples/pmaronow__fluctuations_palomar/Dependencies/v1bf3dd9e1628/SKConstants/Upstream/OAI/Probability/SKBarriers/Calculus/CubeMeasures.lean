module
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Calculus/CubeMeasures.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
public import Mathlib
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.ParameterCalculus
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic
instance parameterMeasurable : (n : ℕ) → MeasurableSpace (ParameterSpace n)
  | 0 => inferInstanceAs (MeasurableSpace ℝ)
  | n+1 => letI := parameterMeasurable n; inferInstanceAs (MeasurableSpace (ParameterSpace n × ℝ))
instance parameterBorel : (n : ℕ) → BorelSpace (ParameterSpace n)
  | 0 => inferInstanceAs (BorelSpace ℝ)
  | n+1 => letI := parameterBorel n; inferInstanceAs (BorelSpace (ParameterSpace n × ℝ))
instance parameterSecondCountable : (n : ℕ) → SecondCountableTopology (ParameterSpace n)
  | 0 => inferInstanceAs (SecondCountableTopology ℝ)
  | n+1 => letI := parameterSecondCountable n; inferInstanceAs (SecondCountableTopology (ParameterSpace n × ℝ))
def fiberMeasure : (n : ℕ) → ℝ → Measure (ParameterSpace n)
  | 0, x => Measure.dirac x
  | n+1, x => (fiberMeasure n x).prod volume
instance fiberSigmaFinite : (n : ℕ) → (x : ℝ) → SigmaFinite (fiberMeasure n x)
  | 0, x => inferInstanceAs (SigmaFinite (Measure.dirac x))
  | n+1, x => letI := fiberSigmaFinite n x; inferInstanceAs (SigmaFinite ((fiberMeasure n x).prod volume))
def cubeMeasure : (n : ℕ) → ℝ → ℝ → ℝ → Measure (ParameterSpace n)
  | 0, x, _, _ => Measure.dirac x
  | n+1, x, a, b => (cubeMeasure n x a b).prod (volume.restrict (Ioc a b))
instance cubeFiniteMeasure : (n : ℕ) → (x a b : ℝ) → IsFiniteMeasure (cubeMeasure n x a b)
  | 0, x, _, _ => inferInstanceAs (IsFiniteMeasure (Measure.dirac x))
  | n+1, x, a, b => letI := cubeFiniteMeasure n x a b
                    inferInstanceAs (IsFiniteMeasure ((cubeMeasure n x a b).prod (volume.restrict (Ioc a b))))
end SK.Analytic
end
end
end
end
end
end SKConstantsOAI
