module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v3cca349de115.DepthPaper.TerminalSpace ====
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
namespace DepthPaper
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

end DepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Examples.Example_2ec6739724b3dcb5a705_TerminalOperators ====
set_option autoImplicit false
@[expose] public section
/-! Actual reconstructed terminal functions and their bounded centered
increment operators. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace DepthPaper
set_option maxSynthPendingDepth 32

set_option linter.unusedVariables false in
axiom _root_.DepthPaper.contDiff_terminalValue : ∀ (g : ↥DepthPaper.TerminalSpace), ContDiff ℝ 3 (DepthPaper.terminalValue g)

set_option linter.unusedVariables false in
axiom _root_.DepthPaper.norm_terminalValue_sub_le : ∀ (g : ↥DepthPaper.TerminalSpace) (x y : ℝ),
  ‖DepthPaper.terminalValue g y - DepthPaper.terminalValue g x‖ ≤
    ‖DepthPaper.terminalJet g 0‖ * ‖y - x‖
set_option linter.unusedVariables false in
axiom _root_.DepthPaper.norm_terminalJet_le : ∀ (g : ↥DepthPaper.TerminalSpace) (i : Fin 3), ‖DepthPaper.terminalJet g i‖ ≤ ‖g‖
def terminalIncrement (d : ℝ) (g : TerminalSpace) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x=>terminalValue g (x+d)-terminalValue g x)
    (((contDiff_terminalValue g).continuous.comp (continuous_id.add continuous_const)).sub
      (contDiff_terminalValue g).continuous) (‖d‖*‖g‖) (fun x=>by
        have h := norm_terminalValue_sub_le g x (x+d)
        simp only [add_sub_cancel_left] at h
        exact h.trans ((mul_le_mul_of_nonneg_right (norm_terminalJet_le g 0)
          (norm_nonneg d)).trans_eq (mul_comm _ _)))

set_option linter.unusedVariables false in
theorem norm_terminalIncrement_le (d : ℝ) (g : TerminalSpace) 
    (h_DepthPaper_terminalIncrement_apply : ∀ (d : ℝ) (g : ↥DepthPaper.TerminalSpace) (x : ℝ),
      (DepthPaper.terminalIncrement d g : ℝ → ℝ) x =
        DepthPaper.terminalValue g (x + d) - DepthPaper.terminalValue g x)
    :
    ‖terminalIncrement d g‖≤‖d‖*‖g‖ := by
  apply (BoundedContinuousFunction.norm_le (f:=terminalIncrement d g)
    (C:=‖d‖*‖g‖) (mul_nonneg (norm_nonneg d) (norm_nonneg g))).mpr
  intro x
  rw [h_DepthPaper_terminalIncrement_apply]
  have h := norm_terminalValue_sub_le g x (x+d)
  simp only [add_sub_cancel_left] at h
  exact h.trans ((mul_le_mul_of_nonneg_right (norm_terminalJet_le g 0)
    (norm_nonneg d)).trans_eq (mul_comm _ _))

end DepthPaper
