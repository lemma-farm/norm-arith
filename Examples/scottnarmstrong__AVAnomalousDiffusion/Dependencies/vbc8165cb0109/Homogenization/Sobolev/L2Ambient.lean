-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.Homogenization.Ambient.Basic
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.Homogenization.Ambient.HilbertFinite
public import Mathlib
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
/-!
This file introduces the actual `L²` ambient types used later to package the
potential and solenoidal spaces as subspaces of a Hilbert space.

The current Sobolev layer still uses predicate-level `MemLp` witnesses in many
places. This file provides the first typed `Lp` layer on bounded domains so the
closed-subspace and minimization arguments can be formulated cleanly.
-/
/-- The restricted Lebesgue measure on a domain `U ⊆ \R^d`. -/
noncomputable abbrev volumeMeasureOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U
noncomputable abbrev HilbertVectorL2 {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.Lp (HilbertVec d) 2 (volumeMeasureOn U)
noncomputable instance instMeasurableSpaceHilbertVectorL2 {d : ℕ} {U : Set (Vec d)} :
    MeasurableSpace (HilbertVectorL2 U) :=
  borel _
noncomputable instance instBorelSpaceHilbertVectorL2 {d : ℕ} {U : Set (Vec d)} :
    BorelSpace (HilbertVectorL2 U) :=
  ⟨rfl⟩
section CarrierTransport
variable {d : ℕ} {U : Set (Vec d)}
end CarrierTransport
section ConstantFields
variable {d : ℕ} {U : Set (Vec d)}
variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
end ConstantFields
section Operators
variable {d : ℕ} {U : Set (Vec d)}
variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
end Operators
end Homogenization
