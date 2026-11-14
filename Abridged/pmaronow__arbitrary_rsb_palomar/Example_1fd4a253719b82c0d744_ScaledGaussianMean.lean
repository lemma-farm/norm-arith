module

public import Mathlib
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Probability.Moments.CovarianceBilinDual
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.TerminalSpace ====
public section
set_option autoImplicit false
set_option backward.privateInPublic true
@[expose] public section
/-! The Banach terminal-data space used by Appendix A. A datum is its value
at zero and its first three bounded continuous jets. Compatibility and uniform
continuity form a closed linear subspace; reconstruction by an actual primitive
recovers the original function. The inherited max norm is equivalent to the
paper's sum norm. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
abbrev TerminalJetData := ℝ×(Fin 3→ℝ →ᵇ ℝ)
def terminalJetSubmodule : Submodule ℝ TerminalJetData where
  carrier := {z | (∀x,HasDerivAt (z.2 0) (z.2 1 x) x) ∧
    (∀x,HasDerivAt (z.2 1) (z.2 2 x) x) ∧ UniformContinuous (z.2 2)}
  zero_mem' := by
    refine ⟨fun x=>?_,fun x=>?_,?_⟩
    · exact hasDerivAt_const x 0
    · exact hasDerivAt_const x 0
    · exact uniformContinuous_const
  add_mem' := by
    intro z w hz hw
    exact ⟨fun x=>(hz.1 x).add (hw.1 x),fun x=>(hz.2.1 x).add (hw.2.1 x),
      hz.2.2.add hw.2.2⟩
  smul_mem' := by
    intro c z hz
    exact ⟨fun x=>(hz.1 x).const_smul c,fun x=>(hz.2.1 x).const_smul c,
      hz.2.2.const_smul c⟩

abbrev TerminalSpace := terminalJetSubmodule

def terminalValue (g : TerminalSpace) (x : ℝ) : ℝ :=
  g.1.1+∫y in (0:ℝ)..x,g.1.2 0 y
def terminalJet (g : TerminalSpace) (i : Fin 3) : ℝ →ᵇ ℝ := g.1.2 i

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.TerminalOperators ====
public section
set_option autoImplicit false
@[expose] public section
/-! Actual reconstructed terminal functions and their bounded centered
increment operators. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32

set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.contDiff_terminalValue : ∀ (g : ↥GeneralDepthPaper.TerminalSpace), ContDiff ℝ 3 (GeneralDepthPaper.terminalValue g)

set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.norm_terminalValue_sub_le : ∀ (g : ↥GeneralDepthPaper.TerminalSpace) (x y : ℝ),
  ‖GeneralDepthPaper.terminalValue g y - GeneralDepthPaper.terminalValue g x‖ ≤
    ‖GeneralDepthPaper.terminalJet g 0‖ * ‖y - x‖
set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.norm_terminalJet_le : ∀ (g : ↥GeneralDepthPaper.TerminalSpace) (i : Fin 3), ‖GeneralDepthPaper.terminalJet g i‖ ≤ ‖g‖
def terminalIncrement (d : ℝ) (g : TerminalSpace) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x=>terminalValue g (x+d)-terminalValue g x)
    (((contDiff_terminalValue g).continuous.comp (continuous_id.add continuous_const)).sub
      (contDiff_terminalValue g).continuous) (‖d‖*‖g‖) (fun x=>by
        have h := norm_terminalValue_sub_le g x (x+d)
        simp only [add_sub_cancel_left] at h
        exact h.trans ((mul_le_mul_of_nonneg_right (norm_terminalJet_le g 0)
          (norm_nonneg d)).trans_eq (mul_comm _ _)))

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.GaussianNormalizerRegularity ====
public section
set_option autoImplicit false
@[expose] public section
/-! The actual centered Gaussian normalizer is jointly analytic in the mass,
positive variance, and Banach terminal datum, including mass zero. The proof
uses an exact precision change to one fixed Gaussian measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
abbrev ColeHopfParameter := (ℝ×ℝ)×TerminalSpace
end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.ScaledGaussianKernel ====
public section
set_option autoImplicit false
@[expose] public section
/-! Gaussian kernels parameterized by their standard deviation. Unlike a
precision chart, this parameterization includes variance zero. The estimates
hold in the supremum norm, including for uniformly continuous highest jets. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000


def scaledGaussianKernel (p : ColeHopfParameter) (z : ℝ) : ℝ →ᵇ ℝ :=
  NormedSpace.exp (p.1.1 • terminalIncrement (p.1.2*z) p.2)

def scaledGaussianNormalizer (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  ∫ z,scaledGaussianKernel p z ∂gaussianReal 0 1

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Examples.Example_1fd4a253719b82c0d744_ScaledGaussianMean ====
set_option autoImplicit false
@[expose] public section
/-! Normalized Gaussian averages remain continuous in the terminal Banach
norm at zero variance. Uniform continuity is required only of the bounded
observable; it is part of the terminal space's highest-jet condition. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000


def scaledGaussianLower (c : ℝ) : ℝ :=
  ∫z,Real.exp (-c*‖z‖) ∂gaussianReal 0 1

set_option linter.unusedVariables false in
theorem scaledGaussianLower_le (p : ColeHopfParameter) (c : ℝ)
    (hc : ‖p.1.1‖*‖p.1.2‖*‖p.2‖ ≤ c) (x : ℝ) 
    (h_GeneralDepthPaper_integrable_scaledGaussianKernel : ∀ (p : GeneralDepthPaper.ColeHopfParameter),
      MeasureTheory.Integrable (GeneralDepthPaper.scaledGaussianKernel p)
        (ProbabilityTheory.gaussianReal 0 1))
    (h_GeneralDepthPaper_integrable_scaledGaussianLower : ∀ (c : ℝ),
      MeasureTheory.Integrable (fun (z : ℝ) ↦ Real.exp (-c * ‖z‖)) (ProbabilityTheory.gaussianReal 0 1))
    (h_GeneralDepthPaper_scaledGaussianNormalizer_apply : ∀ (p : GeneralDepthPaper.ColeHopfParameter) (x : ℝ),
      (GeneralDepthPaper.scaledGaussianNormalizer p : ℝ → ℝ) x =
        ∫ (z : ℝ),
          Real.exp
            (p.1.1 *
              (GeneralDepthPaper.terminalValue p.2 (x + p.1.2 * z) -
                GeneralDepthPaper.terminalValue p.2 x)) ∂ProbabilityTheory.gaussianReal 0 1)
    (h_GeneralDepthPaper_scaledGaussianKernel_apply : ∀ (p : GeneralDepthPaper.ColeHopfParameter) (z x : ℝ),
      (GeneralDepthPaper.scaledGaussianKernel p z : ℝ → ℝ) x =
        Real.exp
          (p.1.1 *
            (GeneralDepthPaper.terminalValue p.2 (x + p.1.2 * z) -
              GeneralDepthPaper.terminalValue p.2 x)))
    :
    scaledGaussianLower c ≤ scaledGaussianNormalizer p x := by
  rw [h_GeneralDepthPaper_scaledGaussianNormalizer_apply]
  have hi : Integrable (fun z =>
      Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)))
      (gaussianReal 0 1) := by
    simpa only [BoundedContinuousFunction.evalCLM_apply,h_GeneralDepthPaper_scaledGaussianKernel_apply] using
      ((BoundedContinuousFunction.evalCLM ℝ x).integrable_comp (h_GeneralDepthPaper_integrable_scaledGaussianKernel p))
  change (∫z,Real.exp (-c*‖z‖) ∂gaussianReal 0 1) ≤ _
  apply integral_mono (h_GeneralDepthPaper_integrable_scaledGaussianLower c) hi
  intro z
  apply Real.exp_le_exp.mpr
  have hi := norm_terminalValue_sub_le p.2 x (x+p.1.2*z)
  simp only [add_sub_cancel_left] at hi
  have hnorm : ‖p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)‖ ≤ c*‖z‖ := by
    rw [norm_mul]
    calc
      ‖p.1.1‖*‖terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x‖
        ≤ ‖p.1.1‖*(‖p.2‖*‖p.1.2*z‖) := by
          gcongr
          exact hi.trans (mul_le_mul_of_nonneg_right (norm_terminalJet_le p.2 0) (norm_nonneg _))
      _ = (‖p.1.1‖*‖p.1.2‖*‖p.2‖)*‖z‖ := by rw [norm_mul]; ring
      _ ≤ c*‖z‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  calc
    -c*‖z‖ ≤ -‖p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)‖ := by
      simpa only [neg_mul] using neg_le_neg hnorm
    _ ≤ p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x) := neg_abs_le _
end GeneralDepthPaper
