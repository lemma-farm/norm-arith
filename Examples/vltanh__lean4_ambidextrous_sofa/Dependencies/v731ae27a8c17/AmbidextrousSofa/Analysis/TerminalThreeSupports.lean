module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.TerminalWallBound
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.PartialTopInsertion
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Three actual supports at a proper terminal angle

The two diagonal supports and the first terminal support give simultaneous
upper bounds for the actual cap roof and lower bounds for its actual
partial barrier. The latter retains the whole outgoing first wall.

The terminal position is obtained from the support maximum of the cap.
Its compatibility with the diagonal position is proved at actual support
points. The top-endpoint alternatives likewise come from actual points of
a height-one affine-middle joint maximum.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
def terminalSlope (α : ℝ) : ℝ := Real.cos α / Real.sin α
theorem terminalSlope_pos {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    0 < terminalSlope α :=
  div_pos (sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩).2 (sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩).1
end AmbidextrousSofa
