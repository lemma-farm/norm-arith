module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.CapOrder
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Vertical extrusion and height saturation of actual caps

An extrusion raises the whole roof and fills down to the baseline. Its
upward supports gain exactly the vertical translation pairing. Every
interior wall and the actual terminal wall therefore gain the same amount;
the nonnegative barrier gains at most that amount. The exterior and middle
windows have equal length, so the actual scalar score cannot decrease.

The final construction saturates any cap to height one. It applies to the
broad cap domain, including caps initially contained in the baseline.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
end AmbidextrousSofa
