-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceGradientSelection
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedSupport
set_option autoImplicit false
set_option warningAsError true
/-!
# A measurable weak gradient on a countable union of time windows

The pressure gradient in `paper/ckn.tex`, Section `sec:pressure`, is first
constructed on spatial slices. Selection on integrable time windows and
countable pasting give a jointly measurable representative on their union.
The representative remains locally integrable and a weak derivative on almost
every spatial slice, so uniqueness identifies it with every derivative on
an open subdomain of the carrier.
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
namespace CKN
end CKN
