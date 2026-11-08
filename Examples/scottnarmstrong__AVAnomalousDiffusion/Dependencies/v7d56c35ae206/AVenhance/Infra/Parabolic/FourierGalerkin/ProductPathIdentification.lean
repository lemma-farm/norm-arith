-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.ProductWeakLimitPassage
public import Mathlib
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Identifying product and weak-path scalar limits

The pointwise weakly continuous Galerkin limit and the product-space limit have the same pairings
against separated time/spatial tests. The proof uses dominated convergence and the uniform scalar
energy bound.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
end AVenhance.Infra.Parabolic.FourierGalerkin
end
