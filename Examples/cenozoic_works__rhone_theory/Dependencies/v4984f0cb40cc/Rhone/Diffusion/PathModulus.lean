/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.Diffusion.InterpolatedPath
public import Examples.cenozoic_works__rhone_theory.Dependencies.v4984f0cb40cc.Rhone.Analysis.PathCompactness
public import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Modulus of continuity of interpolated paths -/
@[expose] public section
namespace Rhone.Diffusion
open Set Analysis
open scoped NNReal
end Rhone.Diffusion
