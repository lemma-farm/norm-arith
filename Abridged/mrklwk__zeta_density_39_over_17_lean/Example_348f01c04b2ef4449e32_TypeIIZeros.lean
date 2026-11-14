module

public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v0c197328dc8b.GuthMaynard.NativeSource.GuthMaynard.Asymptotics ====
public section
set_option autoImplicit false
@[expose] public section
open Asymptotics Filter Topology
namespace GuthMaynard.NativeMoment
/--
`EpsilonPowerBound f g` represents the Guth-Maynard asymptotic convention $f(T) \lessapprox g(T)$.
It means that for any $\varepsilon > 0$, we have $|f(T)| \ll_{\varepsilon} T^{\varepsilon} |g(T)|$ as $T \to \infty$.
The implicit constant may depend on $\varepsilon$.
-/
def EpsilonPowerBound (f g : ℝ → ℝ) : Prop :=
  ∀ (ε : ℝ), ε > 0 → (fun T => |f T|) =O[atTop] (fun T => T ^ ε * |g T|)

end GuthMaynard.NativeMoment

end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v0c197328dc8b.GuthMaynard.NativeSource.GuthMaynard.ZeroDetector ====
public section
set_option autoImplicit false
@[expose] public section
open Complex
open scoped BigOperators
open Classical
namespace GuthMaynard.NativeMoment
/-- One past the natural-number floor of the detector's divisor cutoff. -/
noncomputable def detectorCutoff (T : ℝ) : ℕ :=
  ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ + 1

/- Actual truncated Möbius divisor sum
   `∑_{d ∣ n, d ≤ 2 T^(1/100)} μ(d)`. -/

end GuthMaynard.NativeMoment

end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_348f01c04b2ef4449e32_TypeIIZeros ====
set_option autoImplicit false
@[expose] public section
open Asymptotics Filter MeasureTheory
open Complex
open scoped BigOperators Interval
open Classical
namespace GuthMaynard.NativeMoment
/-- The short Möbius polynomial `M(s)` in Maynard--Pratt Definition 22. -/
noncomputable def shortMobiusPolynomial (T : ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Ico 1 (detectorCutoff T),
    (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
/-- The real-line parameterization of the vertical contour through `1/2 - Re ρ`. -/
noncomputable def typeIIContourShift (ρ : ℂ) (u : ℝ) : ℂ :=
  ((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I
/-- The integrand in the Maynard--Pratt Type II contour detector. -/
noncomputable def typeIIContourIntegrand (ρ : ℂ) (T u : ℝ) : ℂ :=
  let s := typeIIContourShift ρ u
  (T : ℂ) ^ (s / 2) * Complex.Gamma s *
    shortMobiusPolynomial T (ρ + s) * riemannZeta (ρ + s)
/--
The vertical contour detector in Maynard--Pratt Definition 22, parameterized by
`s = 1/2 - Re ρ + iu`. The factor `1/(2π)` includes `ds = i du`.
-/
noncomputable def typeIIContourIntegral (ρ : ℂ) (T : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ u : ℝ, typeIIContourIntegrand ρ T u)
/-- The genuine contour-integral Type II condition from Maynard--Pratt Definition 22. -/
def IsContourTypeIIZero (ρ : ℂ) (T : ℝ) : Prop :=
  (1 / 3 : ℝ) ≤ ‖typeIIContourIntegral ρ T‖

/-- The fourth-moment integrand used in the proof of Maynard--Pratt Lemma 24. -/
noncomputable def twistedZetaMomentIntegrand (T t : ℝ) : ℝ :=
  ‖shortMobiusPolynomial T ((1 / 2 : ℂ) + (t : ℂ) * I) *
    riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 4
/-- The twisted fourth moment over the interval appearing in Appendix C. -/
noncomputable def twistedZetaFourthMoment (T : ℝ) : ℝ :=
  ∫ t in T / 2..3 * T, twistedZetaMomentIntegrand T t
/--
The source's twisted fourth-moment input, with logarithmic losses represented
by the project's epsilon-power convention.
-/
def TwistedZetaFourthMomentProp : Prop :=
  EpsilonPowerBound twistedZetaFourthMoment (fun T => T)

set_option linter.unusedVariables false in
axiom _root_.GuthMaynard.NativeMoment.EpsilonPowerBound.mul_left_rpow : ∀ {f g : ℝ → ℝ},
  GuthMaynard.NativeMoment.EpsilonPowerBound f g →
    ∀ (a : ℝ),
      GuthMaynard.NativeMoment.EpsilonPowerBound (fun (T : ℝ) ↦ T ^ a * f T) fun (T : ℝ) ↦
        T ^ a * g T
/-- The twisted fourth moment gives the correctly scaled `T^(2-2σ)` bound. -/
theorem scaled_twistedZetaFourthMoment_bound
    (hMoment : TwistedZetaFourthMomentProp) (σ : ℝ) :
    EpsilonPowerBound
      (fun T => T ^ (1 - 2 * σ) * twistedZetaFourthMoment T)
      (fun T => T ^ (2 - 2 * σ)) := by
  have hScaled := hMoment.mul_left_rpow (1 - 2 * σ)
  intro ε hε
  have H := hScaled ε hε
  apply H.congr'
  · exact Filter.Eventually.of_forall fun _ => rfl
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hpow : T ^ (1 - 2 * σ) * T = T ^ (2 - 2 * σ) := by
      calc
        T ^ (1 - 2 * σ) * T = T ^ (1 - 2 * σ) * T ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = T ^ ((1 - 2 * σ) + 1) := (Real.rpow_add hT _ _).symm
        _ = T ^ (2 - 2 * σ) := by ring_nf
    rw [hpow]
end GuthMaynard.NativeMoment
