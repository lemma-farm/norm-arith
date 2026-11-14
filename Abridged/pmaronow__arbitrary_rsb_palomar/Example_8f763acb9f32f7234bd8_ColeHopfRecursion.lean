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

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.TerminalSpace ====
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

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.TerminalOperators ====
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
axiom _root_.GeneralDepthPaper.norm_terminalJet_le : ∀ (g : ↥GeneralDepthPaper.TerminalSpace) (i : Fin 3), ‖GeneralDepthPaper.terminalJet g i‖ ≤ ‖g‖

set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.norm_terminalValue_le : ∀ (g : ↥GeneralDepthPaper.TerminalSpace) (x : ℝ),
  ‖GeneralDepthPaper.terminalValue g x‖ ≤ (1 + ‖x‖) * ‖g‖

set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.terminalValue_add : ∀ (g h : ↥GeneralDepthPaper.TerminalSpace) (x : ℝ),
  GeneralDepthPaper.terminalValue (g + h) x =
    GeneralDepthPaper.terminalValue g x + GeneralDepthPaper.terminalValue h x
set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.terminalValue_smul : ∀ (c : ℝ) (g : ↥GeneralDepthPaper.TerminalSpace) (x : ℝ),
  GeneralDepthPaper.terminalValue (c • g) x = c * GeneralDepthPaper.terminalValue g x

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.AnalyticKernel ====
public section
set_option autoImplicit false
set_option backward.privateInPublic true
@[expose] public section
/-! Uniform exponential envelopes give bounded-function valued analyticity.
This formulation does not require strong operator-norm measurability of
translation operators, which fails for the highest uniformly continuous jet. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace GeneralDepthPaper
variable {S E : Type*} [TopologicalSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
def boundedExpKernel (L : S→E→L[ℝ] ℝ) (H : S→ℝ) (hL : Continuous L) (hH : Continuous H)
    (q : E) : S →ᵇ ℝ := by
  classical
  exact if h : ∃C:ℝ,∀s,‖H s*Real.exp (L s q)‖≤C then
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun s=>H s*Real.exp (L s q))
      (hH.mul (Real.continuous_exp.comp ((ContinuousLinearMap.apply ℝ ℝ q).continuous.comp hL)))
      h.choose h.choose_spec else 0

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.TerminalKernel ====
public section
set_option autoImplicit false
@[expose] public section
/-! The genuine centered exponential kernel is analytic in the mass-scaled
terminal datum and positive Gaussian precision, as a bounded function of both
spatial position and Gaussian displacement. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
abbrev TerminalParameter := ℝ×TerminalSpace
def terminalEvalCLM (x : ℝ) : TerminalSpace→L[ℝ]ℝ :=
  LinearMap.mkContinuous
    {toFun:=fun g=>terminalValue g x
     map_add':=fun g h=>terminalValue_add g h x
     map_smul':=fun c g=>by simpa only [RingHom.id_apply,smul_eq_mul] using terminalValue_smul c g x}
    (1+‖x‖) (fun g=>norm_terminalValue_le g x)

def terminalLaplaceLinear (p : ℝ×ℝ) : TerminalParameter→L[ℝ]ℝ :=
  ((terminalEvalCLM (p.2+p.1)-terminalEvalCLM p.2).comp
      (ContinuousLinearMap.snd ℝ ℝ TerminalSpace))-
    (p.1^2) • (ContinuousLinearMap.fst ℝ ℝ TerminalSpace)

set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.continuous_terminalLaplaceLinear : Continuous GeneralDepthPaper.terminalLaplaceLinear

def weightedTerminalKernel (p : TerminalParameter) : (ℝ×ℝ) →ᵇ ℝ :=
  boundedExpKernel terminalLaplaceLinear (fun _=>1) continuous_terminalLaplaceLinear continuous_const p

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.GaussianKernelOperator ====
public section
set_option autoImplicit false
@[expose] public section
/-! A genuine Gaussian averaging operator from bounded displacement/space
kernels to bounded spatial functions. Its norm is at most one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper

set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.norm_gaussianKernel_integral_le : ∀ (v : NNReal) (f : BoundedContinuousFunction (ℝ × ℝ) ℝ) (x : ℝ),
  ‖∫ (d : ℝ), (f : ℝ × ℝ → ℝ) (d, x) ∂ProbabilityTheory.gaussianReal 0 v‖ ≤ ‖f‖
set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.continuous_gaussianKernel_integral : ∀ (v : NNReal) (f : BoundedContinuousFunction (ℝ × ℝ) ℝ),
  Continuous fun (x : ℝ) ↦ ∫ (d : ℝ), (f : ℝ × ℝ → ℝ) (d, x) ∂ProbabilityTheory.gaussianReal 0 v
def gaussianKernelAverage (v : ℝ≥0) (f : (ℝ×ℝ) →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x=>∫d,f (d,x) ∂gaussianReal 0 v)
    (continuous_gaussianKernel_integral v f) ‖f‖ (norm_gaussianKernel_integral_le v f)

def centeredKernelNormalizer (v : ℝ≥0) (p : TerminalParameter) : ℝ →ᵇ ℝ :=
  gaussianKernelAverage v (weightedTerminalKernel p)

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.GaussianVarianceRatio ====
public section
set_option autoImplicit false
@[expose] public section
/-! Exact Gaussian change of precision for centered terminal kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
def gaussianPrecisionDifference (v w : ℝ) : ℝ := 1/(2*v)-1/(2*w)

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.GaussianNormalizerRegularity ====
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
def gaussianPrecisionPrefactor (w v : ℝ) : ℝ :=
  Real.sqrt (2*Real.pi*w)/Real.sqrt (2*Real.pi*v)
def referenceGaussianNormalizer (w : ℝ) (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  gaussianPrecisionPrefactor w p.1.2 • centeredKernelNormalizer w.toNNReal
    (gaussianPrecisionDifference p.1.2 w,p.1.1•p.2)
def centeredGaussianNormalizer (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  referenceGaussianNormalizer (2*p.1.2) p

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.GaussianTiltedOperator ====
public section
set_option autoImplicit false
@[expose] public section
/-! Actual Gaussian tilted averages of bounded displacement/space observables.
The map is jointly analytic in mass, variance, terminal datum and observable;
the zero-mass branch is the original Gaussian averaging operator. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
abbrev GaussianObservable := (ℝ×ℝ) →ᵇ ℝ
abbrev TiltedParameter := ColeHopfParameter×GaussianObservable
def referenceGaussianNumerator (w : ℝ) (p : TiltedParameter) : ℝ →ᵇ ℝ :=
  gaussianPrecisionPrefactor w p.1.1.2 • gaussianKernelAverage w.toNNReal
    (weightedTerminalKernel (gaussianPrecisionDifference p.1.1.2 w,p.1.1.1•p.1.2)*p.2)
def centeredGaussianNumerator (p : TiltedParameter) : ℝ →ᵇ ℝ :=
  referenceGaussianNumerator (2*p.1.1.2) p

def tiltedGaussianOperator (p : TiltedParameter) : ℝ →ᵇ ℝ :=
  Ring.inverse (centeredGaussianNormalizer p.1)*centeredGaussianNumerator p

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.ParametricGaussianAverage ====
public section
set_option autoImplicit false
@[expose] public section
/-! A genuine Gaussian averaging operator from bounded displacement/parameter
kernels to bounded spatial functions. Its norm is at most one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
variable {S : Type*} [TopologicalSpace S] [FirstCountableTopology S]

set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.norm_parametricGaussianKernel_integral_le.{w_u_1} : ∀ {S : Type w_u_1} [inst : TopologicalSpace S] [FirstCountableTopology S] (v : NNReal)
  (f : BoundedContinuousFunction (ℝ × S) ℝ) (x : S),
  ‖∫ (d : ℝ), (f : ℝ × S → ℝ) (d, x) ∂ProbabilityTheory.gaussianReal 0 v‖ ≤ ‖f‖
set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.continuous_parametricGaussianKernel_integral.{w_u_1} : ∀ {S : Type w_u_1} [inst : TopologicalSpace S] [FirstCountableTopology S] (v : NNReal)
  (f : BoundedContinuousFunction (ℝ × S) ℝ),
  Continuous fun (x : S) ↦ ∫ (d : ℝ), (f : ℝ × S → ℝ) (d, x) ∂ProbabilityTheory.gaussianReal 0 v
def parametricGaussianKernelAverage (v : ℝ≥0) (f : (ℝ×S) →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x=>∫d,f (d,x) ∂gaussianReal 0 v)
    (continuous_parametricGaussianKernel_integral v f) ‖f‖ (norm_parametricGaussianKernel_integral_le v f)

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.CompactTiltKernel ====
public section
set_option autoImplicit false
@[expose] public section
/-! An analytic kernel uniform in a compact auxiliary tilt. An independent
second terminal direction allows differentiation of its normalizer without
introducing a division by the auxiliary tilt at zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
abbrev UnitTilt := Icc (0:ℝ) 1
abbrev CompactTiltParameter := ℝ×(TerminalSpace×TerminalSpace)
abbrev CompactTiltLocation := UnitTilt×ℝ
def compactTiltLaplaceLinear (s : ℝ×CompactTiltLocation) : CompactTiltParameter→L[ℝ]ℝ :=
  let inc := terminalEvalCLM (s.2.2+s.1)-terminalEvalCLM s.2.2
  (s.2.1:ℝ) • (inc.comp ((ContinuousLinearMap.fst ℝ TerminalSpace TerminalSpace).comp
    (ContinuousLinearMap.snd ℝ ℝ (TerminalSpace×TerminalSpace))))+
  inc.comp ((ContinuousLinearMap.snd ℝ TerminalSpace TerminalSpace).comp
    (ContinuousLinearMap.snd ℝ ℝ (TerminalSpace×TerminalSpace)))-
  s.1^2 • (ContinuousLinearMap.fst ℝ ℝ (TerminalSpace×TerminalSpace))

set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.continuous_compactTiltLaplaceLinear : Continuous GeneralDepthPaper.compactTiltLaplaceLinear

def compactTiltKernel (p : CompactTiltParameter) : (ℝ×CompactTiltLocation) →ᵇ ℝ :=
  boundedExpKernel compactTiltLaplaceLinear (fun _=>1) continuous_compactTiltLaplaceLinear continuous_const p

def compactTiltNormalizer (w : ℝ≥0) (p : CompactTiltParameter) : CompactTiltLocation →ᵇ ℝ :=
  parametricGaussianKernelAverage w (compactTiltKernel p)

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.TerminalReconstruction ====
public section
set_option autoImplicit false
@[expose] public section
/-! Reconstruction identifies the compatible Banach jets with the actual C³
terminal functions, and the inherited norm is equivalent to the sum norm in
Appendix A. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32

def terminalSpaceOfJets (f : ℝ→ℝ) (J : Fin 3→ℝ →ᵇ ℝ)
    (h01 : ∀x,HasDerivAt (J 0) (J 1 x) x)
    (h12 : ∀x,HasDerivAt (J 1) (J 2 x) x) (hU : UniformContinuous (J 2)) : TerminalSpace :=
  ⟨(f 0,J),h01,h12,hU⟩

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.CompactTiltResponse ====
public section
set_option autoImplicit false
@[expose] public section
/-! Normalized compact-tilt responses are actual Gaussian increment averages,
with joint smoothness in all Banach parameters. The proof differentiates the
analytic bounded kernel and uses its genuinely positive uniform normalizer. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

def compactTiltLower (w : ℝ≥0) (p : CompactTiltParameter) : ℝ :=
  ∫d,Real.exp (-(‖p.2.1‖+‖p.2.2‖)*‖d‖-p.1*d^2) ∂gaussianReal 0 w

def compactTiltResponse (w : ℝ≥0) (q : CompactTiltParameter×TerminalSpace) : CompactTiltLocation →ᵇ ℝ :=
  Ring.inverse (compactTiltNormalizer w q.1)*
    (fderiv ℝ (compactTiltNormalizer w) q.1 (0,(0,q.2)))

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.ProbabilityKernelAverage ====
public section
set_option autoImplicit false
@[expose] public section
/-! A genuine probability averaging operator from bounded displacement/parameter
kernels to bounded spatial functions. Its norm is at most one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
variable {S : Type*} [TopologicalSpace S] [FirstCountableTopology S]
set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.integrable_probabilityKernel_section.{w_u_1} : ∀ {S : Type w_u_1} [inst : TopologicalSpace S] [FirstCountableTopology S]
  (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
  (f : BoundedContinuousFunction (ℝ × S) ℝ) (x : S),
  MeasureTheory.Integrable (fun (d : ℝ) ↦ (f : ℝ × S → ℝ) (d, x)) μ
set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.norm_probabilityKernel_integral_le.{w_u_1} : ∀ {S : Type w_u_1} [inst : TopologicalSpace S] [FirstCountableTopology S]
  (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
  (f : BoundedContinuousFunction (ℝ × S) ℝ) (x : S), ‖∫ (d : ℝ), (f : ℝ × S → ℝ) (d, x) ∂μ‖ ≤ ‖f‖
set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.continuous_probabilityKernel_integral.{w_u_1} : ∀ {S : Type w_u_1} [inst : TopologicalSpace S] [FirstCountableTopology S]
  (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
  (f : BoundedContinuousFunction (ℝ × S) ℝ),
  Continuous fun (x : S) ↦ ∫ (d : ℝ), (f : ℝ × S → ℝ) (d, x) ∂μ
def probabilityKernelAverage (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (ℝ×S) →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x=>∫d,f (d,x) ∂μ)
    (continuous_probabilityKernel_integral μ f) ‖f‖ (norm_probabilityKernel_integral_le μ f)

set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.norm_probabilityKernelAverage_le.{w_u_1} : ∀ {S : Type w_u_1} [inst : TopologicalSpace S] [inst_1 : FirstCountableTopology S]
  (μ : MeasureTheory.Measure ℝ) [inst_2 : MeasureTheory.IsProbabilityMeasure μ]
  (f : BoundedContinuousFunction (ℝ × S) ℝ), ‖GeneralDepthPaper.probabilityKernelAverage μ f‖ ≤ ‖f‖
def probabilityKernelAverageCLM (μ : Measure ℝ) [IsProbabilityMeasure μ] : ((ℝ×S) →ᵇ ℝ)→L[ℝ](S →ᵇ ℝ) :=
  LinearMap.mkContinuous
    {toFun:=probabilityKernelAverage μ
     map_add':=fun f g=>by
       ext x
       exact integral_add (integrable_probabilityKernel_section μ f x)
         (integrable_probabilityKernel_section μ g x)
     map_smul':=fun c f=>by
       ext x
       exact integral_const_mul c (fun d=>f (d,x))}
    1 (fun f=>by
      convert! norm_probabilityKernelAverage_le μ f using 1
      simp only [one_mul])

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.UnitTiltAverage ====
public section
set_option autoImplicit false
@[expose] public section
/-! The literal integral over the auxiliary tilt interval is a norm-one
bounded-function linear operator. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper
def unitTiltMeasure : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.instIsProbabilityMeasureRealUnitTiltMeasure : MeasureTheory.IsProbabilityMeasure GeneralDepthPaper.unitTiltMeasure
attribute [instance] _root_.GeneralDepthPaper.instIsProbabilityMeasureRealUnitTiltMeasure
def unitTiltExtensionCLM : (CompactTiltLocation →ᵇ ℝ)→L[ℝ]((ℝ×ℝ) →ᵇ ℝ) :=
  BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun s:ℝ×ℝ=>(projIcc 0 1 zero_le_one s.1,s.2),by fun_prop⟩
def unitTiltAverageCLM : (CompactTiltLocation →ᵇ ℝ)→L[ℝ](ℝ →ᵇ ℝ) :=
  (probabilityKernelAverageCLM unitTiltMeasure).comp unitTiltExtensionCLM

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.CenteredColeHopfValue ====
public section
set_option autoImplicit false
@[expose] public section
/-! The actual centered Cole–Hopf value is jointly C∞ as a bounded spatial
function, including at mass zero. The auxiliary-tilt response supplies its
removable extension and the exact Gaussian precision identity handles variance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000


def referenceCenteredColeHopfValue (w : ℝ) (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  unitTiltAverageCLM (compactTiltResponse w.toNNReal
    ((gaussianPrecisionDifference p.1.2 w,(p.1.1•p.2,0)),p.2))
def centeredColeHopfValue (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  referenceCenteredColeHopfValue (2*p.1.2) p

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.TerminalGaussianJets ====
public section
set_option autoImplicit false
@[expose] public section
/-! Banach-valued Gaussian moment polynomials for the first three spatial
Cole–Hopf jets. Their joint analytic regularity uses actual tilted averages;
spatial derivative identification is kept separate from this parameter proof. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
def terminalJetCLM (i : Fin 3) : TerminalSpace→L[ℝ](ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    {toFun:=fun g=>terminalJet g i
     map_add':=fun g h=>rfl
     map_smul':=fun c g=>rfl}
    1 (fun g=>by
      convert! norm_terminalJet_le g i using 1
      simp only [one_mul])

def shiftedTerminalJetCLM (i : Fin 3) : TerminalSpace→L[ℝ]GaussianObservable :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun s:ℝ×ℝ=>s.2+s.1,by fun_prop⟩).comp (terminalJetCLM i)

def terminalGaussianMoment (H : ColeHopfParameter→GaussianObservable) (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  tiltedGaussianOperator (p,H p)

def terminalGaussianJetOne (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  terminalGaussianMoment (fun q=>shiftedTerminalJetCLM 0 q.2) p
def terminalGaussianJetTwo (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  terminalGaussianMoment (fun q=>shiftedTerminalJetCLM 1 q.2) p+
    p.1.1 • (terminalGaussianMoment (fun q=>(shiftedTerminalJetCLM 0 q.2)^2) p-
      terminalGaussianJetOne p^2)
def terminalGaussianJetThree (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  terminalGaussianMoment (fun q=>shiftedTerminalJetCLM 2 q.2) p+
  (3*p.1.1) • (terminalGaussianMoment
      (fun q=>shiftedTerminalJetCLM 0 q.2*shiftedTerminalJetCLM 1 q.2) p-
    terminalGaussianJetOne p*terminalGaussianMoment (fun q=>shiftedTerminalJetCLM 1 q.2) p)+
  p.1.1^2 • (terminalGaussianMoment (fun q=>(shiftedTerminalJetCLM 0 q.2)^3) p-
    (3:ℝ) • (terminalGaussianJetOne p*terminalGaussianMoment (fun q=>(shiftedTerminalJetCLM 0 q.2)^2) p)+
    (2:ℝ) • terminalGaussianJetOne p^3)

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v10a9208a7533.GeneralDepthPaper.ColeHopfTerminal ====
public section
set_option autoImplicit false
@[expose] public section
/-! The centered Cole–Hopf map is an actual jointly smooth map into the
manuscript's complete terminal-data Banach space, at every real mass (including
zero) and every positive variance. Its reconstructed function is precisely
`T(a,V,g) - g`. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

def centeredColeHopfJets (p : ColeHopfParameter) : Fin 3→ℝ →ᵇ ℝ :=
  ![terminalGaussianJetOne p-terminalJet p.2 0,
    terminalGaussianJetTwo p-terminalJet p.2 1,
    terminalGaussianJetThree p-terminalJet p.2 2]
set_option linter.unusedVariables false in
axiom _root_.GeneralDepthPaper.centeredColeHopfJets_compatible : ∀ (p : GeneralDepthPaper.ColeHopfParameter),
  0 < p.1.2 →
    (∀ (x : ℝ),
        HasDerivAt (⇑(GeneralDepthPaper.centeredColeHopfJets p 0) : ℝ → ℝ)
          ((GeneralDepthPaper.centeredColeHopfJets p 1 : ℝ → ℝ) x) x) ∧
      (∀ (x : ℝ),
          HasDerivAt (⇑(GeneralDepthPaper.centeredColeHopfJets p 1) : ℝ → ℝ)
            ((GeneralDepthPaper.centeredColeHopfJets p 2 : ℝ → ℝ) x) x) ∧
        UniformContinuous (⇑(GeneralDepthPaper.centeredColeHopfJets p 2) : ℝ → ℝ)
def centeredColeHopfTerminal (p : ColeHopfParameter) : TerminalSpace :=
  if hv:0<p.1.2 then
    terminalSpaceOfJets (centeredColeHopfValue p) (centeredColeHopfJets p)
      (centeredColeHopfJets_compatible p hv).1
      (centeredColeHopfJets_compatible p hv).2.1
      (centeredColeHopfJets_compatible p hv).2.2
  else 0

end GeneralDepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Examples.Example_8f763acb9f32f7234bd8_ColeHopfRecursion ====
set_option autoImplicit false
@[expose] public section
/-! Actual finite Gaussian Cole–Hopf recursion in the complete terminal-data
space. Every finite depth is covered, with arbitrary real masses and positive
step variances, and the first-derivative norm is preserved. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

def coleHopfTerminal (p : ColeHopfParameter) : TerminalSpace := p.2+centeredColeHopfTerminal p

abbrev ColeHopfRecursionParameter (L:ℕ) := (Fin L→ℝ×ℝ)×TerminalSpace
def coleHopfRecursion : (L:ℕ)→ColeHopfRecursionParameter L→TerminalSpace
  | 0,p=>p.2
  | L+1,p=>coleHopfTerminal (p.1 0,coleHopfRecursion L (fun i=>p.1 i.succ,p.2))

set_option linter.unusedVariables false in
theorem norm_terminalJet_coleHopfRecursion_le (L:ℕ) (p:ColeHopfRecursionParameter L)
    (hv:∀i,0<(p.1 i).2) 
    (h_GeneralDepthPaper_norm_terminalJet_coleHopfTerminal_le : ∀ (p : GeneralDepthPaper.ColeHopfParameter),
      0 < p.1.2 →
        ‖GeneralDepthPaper.terminalJet (GeneralDepthPaper.coleHopfTerminal p) 0‖ ≤
          ‖GeneralDepthPaper.terminalJet p.2 0‖)
    : ‖terminalJet (coleHopfRecursion L p) 0‖≤‖terminalJet p.2 0‖ := by
  induction L with
  | zero => exact le_rfl
  | succ L ih =>
    exact (h_GeneralDepthPaper_norm_terminalJet_coleHopfTerminal_le
      (p.1 0,coleHopfRecursion L (fun i=>p.1 i.succ,p.2)) (hv 0)).trans
      (ih (fun i=>p.1 i.succ,p.2) (fun i=>hv i.succ))
end GeneralDepthPaper
