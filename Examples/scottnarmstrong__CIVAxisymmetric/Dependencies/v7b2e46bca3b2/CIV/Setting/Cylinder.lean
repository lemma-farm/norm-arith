-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.Meridional
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.UnitCylinder
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
/-!
# The unit parabolic cylinder and the meridional plane

This module collects the definitions `CIV.unitCylinder` and `CIV.meridional`, each stated in its
own file among the main-result statement files.
-/
@[expose] public section
