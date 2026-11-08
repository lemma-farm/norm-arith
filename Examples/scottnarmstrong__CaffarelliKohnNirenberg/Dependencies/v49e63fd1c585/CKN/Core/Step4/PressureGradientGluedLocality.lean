-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedPartition
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedSupport
set_option autoImplicit false
set_option warningAsError true
/-!
# Weak partial derivatives are a local property

Being the `i`th weak partial derivative is checked against test functions with
compact support, so it is local: if a single locally integrable function is the
`i`th weak partial derivative of `u` on every member of an open cover of `U`,
then it is the `i`th weak partial derivative of `u` on `U` itself.

The proof decomposes a test function with the finite smooth partition of unity
of `exists_smooth_partition_of_unity_of_isCompact`, applies the hypothesis to
each piece, and reassembles the integrals.  The corresponding statement was not
available anywhere: the previously existing interface for weak derivatives
consisted only of restriction, transport and almost-everywhere uniqueness.
-/
open MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
