/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module
public import Examples.jvanwinden__PlanarFrontStability.Dependencies.vef976335a54d.Planarwave.Analysis.BUCBilinear
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
@[expose] public section
/-!
# Nonlinear composition and Taylor remainders on BUC

Continuous nonlinear maps preserve BUC when the values lie in a proper space.
On bounded sets, a twice continuously differentiable reaction has a uniform
quadratic Taylor remainder. This is the reaction estimate in Lemma 4.1 of the paper.
-/
open Bornology Function Set
noncomputable section
namespace BUC
section PointwiseBounds
variable {A F G : Type*} [PseudoMetricSpace A]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
end PointwiseBounds
variable {A E F : Type*} [PseudoMetricSpace A]
  [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F]
end BUC
namespace Planarwave
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
end Planarwave
namespace BUC
variable {A E F : Type*} [PseudoMetricSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
end BUC
