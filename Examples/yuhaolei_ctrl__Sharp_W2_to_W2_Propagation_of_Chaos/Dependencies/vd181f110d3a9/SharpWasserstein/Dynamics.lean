module
public import Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Dependencies.vd181f110d3a9.SharpWasserstein.Transport
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
@[expose] public section
/-! Concrete analytic target of the manuscript. `MainTheorem` below is a
proposition to be proved, NOT a theorem or an axiom. Weak Fokker--Planck
solutions are expressed using genuine derivatives, measures and integrals.
Establishing equivalence with the manuscript's SDEs remains an obligation. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Interval
namespace SharpWasserstein
def coordinateVector {d N : ℕ} (i : Fin N) (a : Fin d) : Configuration d N :=
  fun j c => if j = i ∧ c = a then 1 else 0
def coordinateDerivative {d N : ℕ} (φ : Configuration d N → ℝ)
    (i : Fin N) (a : Fin d) (x : Configuration d N) : ℝ :=
  fderiv ℝ φ x (coordinateVector i a)
def laplacian {d N : ℕ} (φ : Configuration d N → ℝ) (x : Configuration d N) : ℝ :=
  ∑ i, ∑ a, coordinateDerivative (coordinateDerivative φ i a) i a x
def generator {d N : ℕ} (v : Configuration d N → Configuration d N)
    (φ : Configuration d N → ℝ) (x : Configuration d N) : ℝ :=
  laplacian φ x + ∑ i, ∑ a, v x i a * coordinateDerivative φ i a x
def SmoothCompactTest {d N : ℕ} (φ : Configuration d N → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ
/-- Integrated weak equation with explicit integrability, probability and
moment conditions. Diffusion coefficient is one, corresponding to sqrt(2) noise. -/
structure WeakEvolution {d N : ℕ}
    (v : ℝ → Configuration d N → Configuration d N)
    (P : ℝ → Measure (Configuration d N)) : Prop where
  probability : ∀ t, 0 ≤ t → IsProbabilityMeasure (P t)
  secondMoment : ∀ t, 0 ≤ t → HasSecondMoment (P t)
  momentBound : ∀ T, 0 < T → ∃ M : ℝ≥0∞, M < ∞ ∧
    ∀ t ∈ Icc 0 T, (∫⁻ x, ENNReal.ofReal (productCost x 0) ∂P t) ≤ M
  testContinuous : ∀ φ, SmoothCompactTest φ →
    ContinuousOn (fun t => ∫ x, φ x ∂P t) (Ici 0)
  generatorIntegrable : ∀ φ, SmoothCompactTest φ → ∀ t, 0 ≤ t →
    Integrable (generator (v t) φ) (P t)
  timeIntegrable : ∀ φ, SmoothCompactTest φ → ∀ t, 0 ≤ t →
    IntervalIntegrable (fun s => ∫ x, generator (v s) φ x ∂P s) volume 0 t
  equation : ∀ φ, SmoothCompactTest φ → ∀ t, 0 ≤ t →
    (∫ x, φ x ∂P t) - (∫ x, φ x ∂P 0) =
      ∫ s in 0..t, ∫ x, generator (v s) φ x ∂P s
end SharpWasserstein
