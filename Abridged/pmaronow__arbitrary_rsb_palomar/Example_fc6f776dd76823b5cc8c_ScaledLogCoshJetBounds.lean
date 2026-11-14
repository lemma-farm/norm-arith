module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Probability.Moments.CovarianceBilinDual
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.HasLaw
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Choose.Sum

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v849fa81b18f3.Paper.TanhPolynomial ====
public section
set_option autoImplicit false
@[expose] public section
/-!
# Polynomial observables of tanh

Differentiating a polynomial in `tanh` preserves that class of observables.
Every such observable is uniformly bounded because `tanh` takes values in the
compact interval `[-1,1]`.
-/
open scoped Polynomial
namespace Paper
noncomputable def tanhPolynomialDeriv (P : ℝ[X]) : ℝ[X] :=
  P.derivative * (1 - Polynomial.X ^ 2)

end Paper

end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v849fa81b18f3.DepthPaper.LogCoshTerminal ====
public section
set_option autoImplicit false
@[expose] public section
/-! The manuscript's literal log-cosh terminal condition is an actual member
of the compatible-jet Banach space, with first-derivative norm at most one. -/
noncomputable section
open Set Filter
open scoped Topology NNReal BoundedContinuousFunction Polynomial
namespace DepthPaper
set_option maxSynthPendingDepth 64

def logCoshJetPolynomial : ℕ→ℝ[X]
  | 0=>Polynomial.X
  | n+1=>Paper.tanhPolynomialDeriv (logCoshJetPolynomial n)

end DepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v849fa81b18f3.DepthPaper.BivariateJetRegularity ====
public section
set_option autoImplicit false
@[expose] public section
/-! Joint smoothness and actual mass derivatives of a bivariate polynomial.
The finite coefficient formula is used to obtain genuine compact bounds for
the endpoint quotient in the large-variance residual argument. -/
noncomputable section
open Set
open scoped Polynomial ContDiff
namespace DepthPaper
 def bivariateValue (P:Polynomial (Polynomial ℝ)) (m t:ℝ):ℝ :=
   (P.map (Polynomial.evalRingHom m)).eval t
 
 
 
 
 
 
end DepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Examples.Example_fc6f776dd76823b5cc8c_ScaledLogCoshJetBounds ====
set_option autoImplicit false
@[expose] public section
/-! Every actual mixed mass/spatial derivative of ψ_m is uniformly bounded
on compact positive mass intervals. Positive spatial orders are essential:
ψ_m itself has linear growth. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Polynomial
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def scaledLogCoshPositiveJet (j : ℕ) (m x : ℝ) : ℝ :=
  m^j*(logCoshJetPolynomial j).eval (Real.tanh (m*x))


set_option linter.unusedVariables false in
theorem scaledLogCoshJet_mixed_uniform_bound (j k : ℕ) {eps : ℝ} (heps : 0 < eps) (M : ℝ) 
    (h_DepthPaper_contDiff_logCoshJetPolynomial : ∀ (j : ℕ),
      ContDiff ℝ (↑⊤ : WithTop ℕ∞) fun (x : ℝ) ↦
        Polynomial.eval (Real.tanh x) (DepthPaper.logCoshJetPolynomial j))
    (h_DepthPaper_norm_iteratedDeriv_mul_le : ∀ (j : ℕ) {f g : ℝ → ℝ} {m A B : ℝ},
      ContDiff ℝ (↑⊤ : WithTop ℕ∞) f →
        ContDiff ℝ (↑⊤ : WithTop ℕ∞) g →
          0 ≤ A →
            0 ≤ B →
              (∀ k ≤ j, ‖iteratedDeriv k f m‖ ≤ A) →
                (∀ k ≤ j, ‖iteratedDeriv k g m‖ ≤ B) →
                  ‖iteratedDeriv j (fun (r : ℝ) ↦ f r * g r) m‖ ≤ 2 ^ j * A * B)
    (h_DepthPaper_bivariateValue_mass_uniform_bounds : ∀ (P : Polynomial (Polynomial ℝ)) (J : ℕ) (a b : ℝ),
      ∃ (K : ℝ),
        1 ≤ K ∧
          ∀ j ≤ J,
            ∀ m ∈ Set.Icc a b,
              ∀ t ∈ Set.Icc (-1) 1,
                ‖iteratedDeriv j (fun (r : ℝ) ↦ DepthPaper.bivariateValue P r t) m‖ ≤ K)
    (h_DepthPaper_logCoshJet_mass_uniform_bounds : ∀ (j N : ℕ) {eps : ℝ},
      0 < eps →
        ∃ (C : ℝ),
          0 ≤ C ∧
            ∀ k ≤ N,
              ∀ m ≥ eps,
                ∀ (x : ℝ),
                  ‖iteratedDeriv k
                        (fun (a : ℝ) ↦
                          Polynomial.eval (Real.tanh (a * x)) (DepthPaper.logCoshJetPolynomial j))
                        m‖ ≤
                    C)
    :
    ∃C:ℝ,0≤C ∧ ∀m∈Icc eps M,∀x:ℝ,
      ‖iteratedDeriv k (fun a=>scaledLogCoshPositiveJet j a x) m‖≤C := by
  obtain ⟨A,hA,ha⟩:=h_DepthPaper_bivariateValue_mass_uniform_bounds (Polynomial.C (Polynomial.X^j)) k eps M
  obtain ⟨B,hB,hb⟩:=h_DepthPaper_logCoshJet_mass_uniform_bounds j k heps
  refine ⟨(2:ℝ)^k*A*B,by positivity,?_⟩
  intro m hm x
  exact h_DepthPaper_norm_iteratedDeriv_mul_le k (contDiff_id.pow j)
    ((h_DepthPaper_contDiff_logCoshJetPolynomial j).comp (contDiff_id.mul contDiff_const))
    (zero_le_one.trans hA) hB
    (fun l hl=>by simpa [bivariateValue] using ha l hl m hm 0 (by norm_num))
    (fun l hl=>hb l hl m hm.1 x)

end DepthPaper
