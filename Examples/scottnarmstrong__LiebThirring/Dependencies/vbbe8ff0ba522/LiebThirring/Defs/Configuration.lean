/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Data.Fin.Basic
public import Mathlib.Analysis.Fourier.LpSpace
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Particle configurations and spin states

Spatial and spin spaces for many-particle L² states, with coordinate insertion and permutation.
-/
public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring
@[expose] def Position  : Type :=
  EuclideanSpace ℝ (Fin 3)
attribute [reducible] Position
@[expose] def Configuration (N : ℕ) : Type :=
  EuclideanSpace ℝ (Fin N × Fin 3)
attribute [reducible] Configuration
@[expose] def SpinLabels (N q : ℕ) : Type :=
  Fin N → Fin q
attribute [reducible] SpinLabels
@[expose] def SpinAmplitudes (N q : ℕ) : Type :=
  EuclideanSpace ℂ (SpinLabels N q)
attribute [reducible] SpinAmplitudes
@[expose] def State (N q : ℕ) : Type :=
  Lp (SpinAmplitudes N q) 2 (volume : Measure (Configuration N))
attribute [reducible] State
@[expose] def particlePosition {N : ℕ} (x : Configuration N) (i : Fin N) : Position :=
  toLp 2 (fun a => x (i, a))
@[expose] def OtherConfiguration {N : ℕ} (i : Fin N) : Type :=
  EuclideanSpace ℝ ({j : Fin N // j ≠ i} × Fin 3)
attribute [reducible] OtherConfiguration
end LiebThirring
end
