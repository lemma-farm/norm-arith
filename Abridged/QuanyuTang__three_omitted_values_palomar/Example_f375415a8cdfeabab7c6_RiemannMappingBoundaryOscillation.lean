module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Complex
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Operator.Compact
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

-- ==== Examples.QuanyuTang__three_omitted_values_palomar.Examples.Example_f375415a8cdfeabab7c6_RiemannMappingBoundaryOscillation ====
-- Local port: the cap argument only uses the minimal area-energy input.
/-!
# Finite-energy circular caps of the interior Riemann map

The derivative is cut off to the **open** disk, where the actual map is
holomorphic. Translated polar integration and the nonintegrability of
`1/r` at zero give arbitrarily small circles whose portions in the disk
have arbitrarily small image length. The chosen radius is also a genuine
integrable angular slice, so no default-valued integral is used as a
substitute for finite length.

Integrating the actual derivative on any open circular arc in the disk
constructs its finite endpoint values. None of these statements assumes
or asserts a continuous extension of the Riemann map to the whole circle.
The Jordan crosscut separation argument needed to turn these cap estimates
into a full Carathéodory extension remains a separate geometric step. In
that step distinct frontier endpoints are joined by a short physical
boundary arc; coincident endpoints instead give a small closed loop.
Endpoint injectivity is not assumed before proving the boundary theorem.
-/
@[expose] public section
set_option autoImplicit false
-- Local port: allow the current Mathlib definitions to unfold during type checking.
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PolyaNeumann
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal
/-- The actual complex derivative, extended by zero outside its open
domain. Values of the original total function on the boundary are unused. -/
def riemannInteriorDerivative (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (ball (0 : ℂ) 1).indicator (deriv F) z

/-- The true angular derivative of `F ∘ circleMap c r` on its portions
inside the disk, and zero on the remaining portions. -/
def riemannCapDerivative (F : ℂ → ℂ) (c : ℂ) (r θ : ℝ) : ℂ :=
  riemannInteriorDerivative F (circleMap c r θ) * (circleMap 0 r θ * Complex.I)


set_option linter.unusedVariables false in
/-- The Courant–Lebesgue length consequence for the actual map. The
integral includes exactly the portions of the circle lying in the open
disk; the derivative was proved to vanish on its other portions. -/
theorem riemannMapping_exists_small_cap_length (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (c : ℂ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) 
    (h_PolyaNeumann_norm_riemannCapDerivative : ∀ (F : ℂ → ℂ) (c : ℂ) {r : ℝ},
      0 ≤ r →
        ∀ (θ : ℝ),
          ‖PolyaNeumann.riemannCapDerivative F c r θ‖ =
            r * ‖PolyaNeumann.riemannInteriorDerivative F (circleMap c r θ)‖)
    (h_PolyaNeumann_riemannCapDerivative_integrable : ∀ (F : ℂ → ℂ) (c : ℂ) {r : ℝ},
      0 ≤ r →
        MeasureTheory.IntegrableOn
            (fun (θ : ℝ) ↦ ‖PolyaNeumann.riemannInteriorDerivative F (circleMap c r θ)‖ ^ 2)
            (Set.Ioo (-Real.pi) Real.pi) MeasureTheory.MeasureSpace.volume →
          MeasureTheory.IntegrableOn (PolyaNeumann.riemannCapDerivative F c r)
            (Set.Ioo (-Real.pi) Real.pi) MeasureTheory.MeasureSpace.volume)
    (h_PolyaNeumann_riemannMapping_exists_small_cap_energy : ∀ (F : ℂ → ℂ),
      DifferentiableOn ℂ F (Metric.ball 0 1) →
        Set.InjOn F (Metric.ball 0 1) →
          Bornology.IsBounded (F '' Metric.ball 0 1) →
            ∀ (c : ℂ) {δ ε : ℝ},
              0 < δ →
                0 < ε →
                  ∃ r ∈ Set.Ioo 0 δ,
                    MeasureTheory.IntegrableOn
                        (fun (θ : ℝ) ↦ ‖PolyaNeumann.riemannInteriorDerivative F (circleMap c r θ)‖ ^ 2)
                        (Set.Ioo (-Real.pi) Real.pi) MeasureTheory.MeasureSpace.volume ∧
                      r ^ 2 *
                          ∫ (θ : ℝ) in Set.Ioo (-Real.pi) Real.pi,
                            ‖PolyaNeumann.riemannInteriorDerivative F (circleMap c r θ)‖ ^ 2 <
                        ε)
    :
    ∃ r ∈ Ioo (0 : ℝ) δ,
      IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi) ∧
      (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖) < ε := by
  let a : ℝ := ε / (4 * Real.pi)
  have ha : 0 < a := div_pos hε (by positivity)
  obtain ⟨r, hr, hs, hsmall⟩ := h_PolyaNeumann_riemannMapping_exists_small_cap_energy
    F hF hinj hb c hδ (show 0 < 2 * a * ε by positivity)
  have hi := h_PolyaNeumann_riemannCapDerivative_integrable F c hr.1.le hs
  have hsq : IntegrableOn (fun θ => ‖riemannCapDerivative F c r θ‖ ^ 2)
      (Ioo (-Real.pi) Real.pi) := by
    rw [IntegrableOn] at hs ⊢
    simpa only [h_PolyaNeumann_norm_riemannCapDerivative F c hr.1.le, mul_pow]
      using! hs.const_mul (r ^ 2)
  have hsqsmall : (∫ θ in Ioo (-Real.pi) Real.pi,
      ‖riemannCapDerivative F c r θ‖ ^ 2) < 2 * a * ε := by
    simpa only [h_PolyaNeumann_norm_riemannCapDerivative F c hr.1.le, mul_pow,
      integral_const_mul] using hsmall
  have hconst : IntegrableOn (fun _ : ℝ => a) (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hpoint : ∀ θ, ‖riemannCapDerivative F c r θ‖ ≤
      a + ‖riemannCapDerivative F c r θ‖ ^ 2 / (4 * a) := by
    intro θ
    have h : (‖riemannCapDerivative F c r θ‖ - a) * (4 * a) ≤
        ‖riemannCapDerivative F c r θ‖ ^ 2 := by
      nlinarith [sq_nonneg (‖riemannCapDerivative F c r θ‖ - 2 * a)]
    have := (le_div_iff₀ (show 0 < 4 * a by positivity)).2 h
    linarith
  have hle := integral_mono hi.norm (hconst.add (hsq.div_const (4 * a))) hpoint
  change (∫ θ in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r θ‖) ≤
    ∫ θ in Ioo (-Real.pi) Real.pi, a + ‖riemannCapDerivative F c r θ‖ ^ 2 / (4 * a) at hle
  have hmeasure : (∫ θ in Ioo (-Real.pi) Real.pi, a) = 2 * Real.pi * a := by
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    simp only [smul_eq_mul]
    ring
  rw [integral_add hconst (hsq.div_const (4 * a)), hmeasure, integral_div] at hle
  have hdiv : (∫ θ in Ioo (-Real.pi) Real.pi,
      ‖riemannCapDerivative F c r θ‖ ^ 2) / (4 * a) < ε / 2 := by
    apply (div_lt_iff₀ (show 0 < 4 * a by positivity)).2
    nlinarith [hsqsmall]
  refine ⟨r, hr, hi, hle.trans_lt ?_⟩
  have hhalf : 2 * Real.pi * a = ε / 2 := by
    dsimp [a]
    field_simp [Real.pi_pos.ne']; ring
  rw [hhalf]
  linarith

end PolyaNeumann
end
