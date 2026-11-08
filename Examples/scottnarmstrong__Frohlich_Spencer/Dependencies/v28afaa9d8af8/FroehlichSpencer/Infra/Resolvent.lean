/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v28afaa9d8af8.FroehlichSpencer.Infra.Resolvent.Basic
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v28afaa9d8af8.FroehlichSpencer.Infra.Resolvent.Complex
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v28afaa9d8af8.FroehlichSpencer.Infra.Resolvent.Decoupling
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finite-dimensional resolvent infrastructure

Generic matrix resolvent identities, spectral bounds, and block decoupling
motivated by Fröhlich–Spencer (1983), equations (2.10)–(2.13), pp. 159–160.
-/
public section
