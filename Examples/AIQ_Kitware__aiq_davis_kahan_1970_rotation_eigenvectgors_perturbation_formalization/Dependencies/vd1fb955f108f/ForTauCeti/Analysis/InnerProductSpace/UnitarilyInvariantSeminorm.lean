/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Majorization
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Gauge
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Instances
set_option autoImplicit false
set_option linter.deprecated false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Unitarily invariant seminorms

`UnitarilyInvariantSeminorm 𝕜 E F` extends `Seminorm` on rectangular linear maps.
Ky Fan dominance applies on every such map space. Symmetric gauges, adjoints of
endomorphisms, and operator absolute value use the specialization `E = F`.
-/
public section
