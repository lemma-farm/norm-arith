/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.DenseTime.PhysicalReindex
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.FiniteProductCoordinateNormalForm
import Mathlib.MeasureTheory.Integral.CompactlySupported
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Compact-test transport from physical to dense-time coordinates

This file identifies finite paths labelled by physical rational times with paths labelled by the
corresponding dense times. It pulls compactly supported tests back across this homeomorphism and
rewrites integrals against mapped finite-set kernels.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported
namespace MarkovProcess.DenseTimePath
open SubMarkovKernelSemigroup
end MarkovProcess.DenseTimePath
