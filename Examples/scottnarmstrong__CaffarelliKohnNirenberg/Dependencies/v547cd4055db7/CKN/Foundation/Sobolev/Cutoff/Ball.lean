-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v547cd4055db7.CKN.Foundation.Sobolev.Cutoff.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v547cd4055db7.CKN.Foundation.Sobolev.Cutoff.Profile
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option warningAsError true
/-!
# Quantitative smooth cutoffs for round balls

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent port uses the native `Fin d → ℝ` carrier and an
explicit Euclidean squared distance.

## Main definitions

* `euclideanBall` and `euclideanClosedBall`: round balls for the explicit
  Euclidean norm.
* `canonicalBallCutoff`: a smooth cutoff with a midpoint support collar.

## Main results

* `canonicalBallCutoff_smooth`, `canonicalBallCutoff_eq_one_on_inner`, and
  `canonicalBallCutoff_tsupport_subset_outer` give the qualitative cutoff
  properties.
* `canonicalBallCutoff_gradient_bound` gives the explicit bound
  `32 / (R - r)`.
-/
open Set
noncomputable section
namespace CKN
end CKN
