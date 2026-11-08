-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientOriginCellInstanceSlice
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.WeakGradientGluingTMeasurable
set_option autoImplicit false
set_option warningAsError true
/-!
# A measurable weak pressure gradient on an interior origin ball

The slice derivatives of `eq:pressure-gradient-morrey` have one measurable
representative on the whole time interval. Its derivatives on all open
subdomains share one exceptional set of times, as needed in `prop:bootstrap`.
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
open OriginInstance
end CKN.Core.Step4
