-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Statements.Theta
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Statements.Gamma
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Statements.Lambda
set_option autoImplicit false
set_option warningAsError true
/-!
# Scale invariance of the dimensionless quantities

This module formalizes the rescaled fields of Definition `def:rescaling` of
`paper/ckn.tex` and the transformation law of Lemma `lem:scaling-quantities`:
at the rescaled base point each of `α`, `β`, `γ`, `δ`, `λ`, `θ` is unchanged
from its value at the original point with the radius scaled by the dilation.

The analytic input is the parabolic change of variables for cylinder integrals
and time-slice essential suprema, together with the elementary algebra of the
exponents.  The essential supremum of the velocity `L²` energy is handled with
the boundedness assumption that makes the transform of an essential supremum
legitimate; every other quantity is unconditional.
-/
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN
/-! ### The rescaled fields -/
end CKN
end
