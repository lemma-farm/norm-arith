-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Setting.Cylinder
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.AngularMean
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.AngularMeanScalar
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.IsAxisymmetricOn
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.RotField
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.RotZ
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
/-!
# Rotations about the axis and the angular mean

This module collects the definitions `CIV.rotZ`, `CIV.rotField`, `CIV.angularMean`,
`CIV.angularMeanScalar` and `CIV.IsAxisymmetricOn` of `eq:interior:average` and
`sec:aniso:notation`, each stated in its own file among the main-result statement files.
-/
@[expose] public section
