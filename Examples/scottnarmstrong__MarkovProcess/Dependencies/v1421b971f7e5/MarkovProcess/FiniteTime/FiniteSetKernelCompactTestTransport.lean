/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.FiniteProductCoordinateNormalForm
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.ProjectiveFamily
import Mathlib.MeasureTheory.Integral.CompactlySupported
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Compact-test transport for finite-set kernels

This file identifies the increasing-coordinate representation of a finite set with its ordinary
function space by a homeomorphism. It transports compactly supported tests across that
homeomorphism and rewrites their finite-set-kernel integrals as finite-time-kernel integrals.

Strong measurability of a compactly supported test is obtained privately from uniform coordinate-
polynomial approximations. This avoids adding an `OpensMeasurableSpace` assumption on the finite
product. These declarations are finite-dimensional infrastructure; no statement about path space
is proved here.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported
namespace MarkovProcess.SubMarkovKernelSemigroup
end MarkovProcess.SubMarkovKernelSemigroup
