module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v330695745e07.DepthPaper.TerminalSpace
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v330695745e07.Common.Mathlib.Probability.Distributions.Gaussian.ExpGrowth
set_option autoImplicit false
@[expose] public section
/-! Actual reconstructed terminal functions and their bounded centered
increment operators. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace DepthPaper
set_option maxSynthPendingDepth 32
open ColeHopfFoundation.ProbabilityTheory
theorem lipschitzWith_terminalValue (g : TerminalSpace) :
    LipschitzWith ‖terminalJet g 0‖₊ (terminalValue g) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x=>(hasDerivAt_terminalValue g x).differentiableAt)
  intro x
  rw [(hasDerivAt_terminalValue g x).deriv]
  exact BoundedContinuousFunction.nnnorm_coe_le_nnnorm _ _
theorem norm_terminalValue_sub_le (g : TerminalSpace) (x y : ℝ) :
    ‖terminalValue g y-terminalValue g x‖≤‖terminalJet g 0‖*‖y-x‖ := by
  simpa only [dist_eq_norm,coe_nnnorm] using (lipschitzWith_terminalValue g).dist_le_mul y x
theorem norm_terminalJet_le (g : TerminalSpace) (i : Fin 3) : ‖terminalJet g i‖≤‖g‖ :=
  (norm_le_pi_norm g.1.2 i).trans (norm_snd_le g.1)
theorem norm_terminalValue_le (g : TerminalSpace) (x : ℝ) :
    ‖terminalValue g x‖≤(1+‖x‖)*‖g‖ := by
  have h0 : ‖terminalValue g 0‖≤‖g‖ := by
    rw [terminalValue_zero]; exact norm_fst_le g.1
  have hd := norm_terminalValue_sub_le g 0 x
  rw [sub_zero] at hd
  calc
    ‖terminalValue g x‖≤‖terminalValue g x-terminalValue g 0‖+‖terminalValue g 0‖ :=
      by simpa only [sub_add_cancel] using
        norm_add_le (terminalValue g x-terminalValue g 0) (terminalValue g 0)
    _≤‖terminalJet g 0‖*‖x‖+‖g‖ := add_le_add hd h0
    _≤‖g‖*‖x‖+‖g‖ := by gcongr; exact norm_terminalJet_le g 0
    _=(1+‖x‖)*‖g‖ := by ring
end DepthPaper
