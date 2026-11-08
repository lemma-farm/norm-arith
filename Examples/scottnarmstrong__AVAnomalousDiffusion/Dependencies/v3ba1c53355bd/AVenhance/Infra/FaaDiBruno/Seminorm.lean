-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.Homogenization.Ambient.Basic
public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Normed.Lp.PiLp
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Appendix B derivative seminorms

The coordinate derivatives of order `n` are represented by evaluating the
iterated Fréchet derivative on coordinate basis vectors. An ordered list of
coordinate directions presents a multi-index, and the API groups these lists
by their multiplicities. For smooth functions, identifying all orderings of
the same multi-index uses the symmetry of iterated derivatives.
-/
@[expose] public section
noncomputable section
open MeasureTheory
namespace AVenhance.FaaDiBruno
open Homogenization
end AVenhance.FaaDiBruno
end
