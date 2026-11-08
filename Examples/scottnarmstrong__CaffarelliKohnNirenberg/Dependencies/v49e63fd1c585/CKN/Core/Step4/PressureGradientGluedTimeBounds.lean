-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientOriginClauseField
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Integration.Slice
set_option autoImplicit false
set_option warningAsError true
/-!
# Time integrability on fixed pressure carriers

The `3/2` power of a spatial norm, integrated in time over a fixed local box,
is the space-time power integral on that box: Tonelli exchanges the two. The
finiteness that identity delivers is stable under a finite fixed coefficient
and under extending the time window by zero. The coefficients below are fixed
before the time integral; no shrinking-cell growth is asserted.
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
namespace CKN.Core.Step4
end CKN.Core.Step4
