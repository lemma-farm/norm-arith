-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedLocality
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.PressureGradientGluedSelectionCore
set_option autoImplicit false
set_option warningAsError true
/-!
# Gluing weak partial derivatives over an open cover

Weak partial derivatives produced separately on the members of an open cover
agree almost everywhere on the overlaps, because a locally integrable weak
partial derivative is unique almost everywhere on an open set.  They therefore
glue: over a countable open cover the pieces are represented by one function,
and by locality that function is the weak partial derivative on the union.

The second statement is the form used in practice.  It says that the existence
of a weak partial derivative is a purely local matter: if every point of an
open set has a neighbourhood on which `u` has a locally integrable `i`th weak
partial derivative, then `u` has one on the whole set.  Second countability of
`Fin d → ℝ` reduces the given family to a countable subfamily.
-/
open MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
