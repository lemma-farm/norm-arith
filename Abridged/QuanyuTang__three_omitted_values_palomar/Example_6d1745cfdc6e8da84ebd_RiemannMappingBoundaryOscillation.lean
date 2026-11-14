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

-- ==== Examples.QuanyuTang__three_omitted_values_palomar.Examples.Example_6d1745cfdc6e8da84ebd_RiemannMappingBoundaryOscillation ====
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
/-- The displacement of the continuous cap image, including its newly
constructed endpoints, is bounded by the true length of the good slice. -/
theorem riemannMapping_cap_extension_displacement (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (c : ℂ) (r : ℝ)
    (hi : IntegrableOn (riemannCapDerivative F c r) (Ioo (-Real.pi) Real.pi))
    {a b : ℝ} (_hab : a < b) (hwidth : b ≤ a + 2 * Real.pi)
    (harc : MapsTo (circleMap c r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap c r θ)) (Ioo a b)) 
    (h_PolyaNeumann_riemannCapDerivative_periodic : ∀ (F : ℂ → ℂ) (c : ℂ) (r : ℝ),
      Function.Periodic (PolyaNeumann.riemannCapDerivative F c r) (2 * Real.pi))
    (h_PolyaNeumann_riemannMapping_cap_extension_subarc_displacement : ∀ (F : ℂ → ℂ),
      DifferentiableOn ℂ F (Metric.ball 0 1) →
        ∀ (c : ℂ) (r : ℝ),
          MeasureTheory.IntegrableOn (PolyaNeumann.riemannCapDerivative F c r)
              (Set.Ioo (-Real.pi) Real.pi) MeasureTheory.MeasureSpace.volume →
            ∀ {a b : ℝ},
              Set.MapsTo (circleMap c r) (Set.Ioo a b) (Metric.ball 0 1) →
                ∀ {G : ℝ → ℂ},
                  Continuous G →
                    Set.EqOn G (fun (θ : ℝ) ↦ F (circleMap c r θ)) (Set.Ioo a b) →
                      ∀ {θ τ : ℝ},
                        θ ∈ Set.Icc a b →
                          τ ∈ Set.Icc a b →
                            θ ≤ τ →
                              ‖G τ - G θ‖ ≤
                                ∫ (s : ℝ) in θ..τ, ‖PolyaNeumann.riemannCapDerivative F c r s‖)
    (h_PolyaNeumann_riemannCapDerivative_intervalIntegrable : ∀ (F : ℂ → ℂ) (c : ℂ) (r : ℝ),
      MeasureTheory.IntegrableOn (PolyaNeumann.riemannCapDerivative F c r) (Set.Ioo (-Real.pi) Real.pi)
          MeasureTheory.MeasureSpace.volume →
        ∀ (a b : ℝ),
          IntervalIntegrable (PolyaNeumann.riemannCapDerivative F c r) MeasureTheory.MeasureSpace.volume
            a b)
    :
    ∀ θ ∈ Icc a b, ∀ τ ∈ Icc a b,
      ‖G θ - G τ‖ ≤
        ∫ s in Ioo (-Real.pi) Real.pi, ‖riemannCapDerivative F c r s‖ := by
  let V : ℝ → ℂ := riemannCapDerivative F c r
  have hVi : ∀ s u : ℝ, IntervalIntegrable V volume s u :=
    h_PolyaNeumann_riemannCapDerivative_intervalIntegrable F c r hi
  have hperiod : Function.Periodic (fun s => ‖V s‖) (2 * Real.pi) :=
    (h_PolyaNeumann_riemannCapDerivative_periodic F c r).comp norm
  have hfull : (∫ s in a..a + 2 * Real.pi, ‖V s‖) =
      ∫ s in Ioo (-Real.pi) Real.pi, ‖V s‖ := by
    calc
      _ = ∫ s in (-Real.pi)..Real.pi, ‖V s‖ := by
        simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring]
          using hperiod.intervalIntegral_add_eq a (-Real.pi)
      _ = _ := by
        rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
          integral_Ioc_eq_integral_Ioo]
  have hordered : ∀ θ ∈ Icc a b, ∀ τ ∈ Icc a b, θ ≤ τ →
      ‖G τ - G θ‖ ≤ ∫ s in Ioo (-Real.pi) Real.pi, ‖V s‖ := by
    intro θ hθ τ hτ hθτ
    calc
      ‖G τ - G θ‖ ≤ ∫ s in θ..τ, ‖V s‖ :=
        h_PolyaNeumann_riemannMapping_cap_extension_subarc_displacement F hF c r hi harc hGc hGeq hθ hτ hθτ
      _ ≤ ∫ s in a..a + 2 * Real.pi, ‖V s‖ :=
        intervalIntegral.integral_mono_interval hθ.1 hθτ (hτ.2.trans hwidth)
          (Eventually.of_forall fun _ => norm_nonneg _) (hVi a _).norm
      _ = _ := hfull
  intro θ hθ τ hτ
  rcases le_total θ τ with h | h
  · rw [norm_sub_rev]
    exact hordered θ hθ τ hτ h
  · exact hordered τ hτ θ hθ h
end PolyaNeumann
end
