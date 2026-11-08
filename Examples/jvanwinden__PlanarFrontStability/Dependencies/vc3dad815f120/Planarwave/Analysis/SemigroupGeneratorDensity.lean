/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module
public import Examples.jvanwinden__PlanarFrontStability.Dependencies.vc3dad815f120.Planarwave.Analysis.SemigroupGenerator
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul
@[expose] public section
/-!
# Density of the generator domain

Integrating an orbit produces a generator-domain vector. Its short-time averages converge to
the initial datum. This supplies the density needed for uniqueness of a semigroup with a
given generator, and hence for reassociating bounded perturbations in the paper's compact-
family uniformization argument.
-/
open Filter MeasureTheory Set Topology
namespace C0Semigroup
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
end
end C0Semigroup
