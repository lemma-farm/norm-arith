module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.HypoellipticAleksandrov.Parabolic.Dirichlet.GelfandTriple
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Reverse-time Bochner spaces

This module defines the quotient-valued Bochner `L²` carriers over the literal
reverse-time interval and lifts the spatial Gelfand-triple maps to them.
It makes only almost-everywhere representative statements, never fixed-time
evaluation or temporal regularity claims.
-/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
/-- The open reverse-time interval, including the empty case `T ≤ 0`. -/
def reverseTimeOpenInterval (T : ℝ) : Set ℝ :=
  Set.Ioo 0 T
/-- Lebesgue measure restricted to the literal open reverse-time interval. -/
noncomputable def reverseTimeVolume (T : ℝ) : Measure ℝ :=
  volume.restrict (reverseTimeOpenInterval T)
/-- Bochner `L²` curves with values in the zero-boundary spatial Hilbert graph. -/
abbrev ReverseTimeL2V
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) : Type _ :=
  MeasureTheory.Lp (H10HilbertGraph hΩ) (2 : ℝ≥0∞) (reverseTimeVolume T)
/-- Bochner `L²` curves with values in spatial restricted-volume `L²`. -/
abbrev ReverseTimeL2H
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) : Type _ :=
  MeasureTheory.Lp (PDE.ScalarLp Ω (2 : ℝ≥0∞)) (2 : ℝ≥0∞)
    (reverseTimeVolume T)
/-- Bochner `L²` curves with values in the spatial Gelfand dual. -/
abbrev ReverseTimeL2VStar
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) : Type _ :=
  MeasureTheory.Lp (H10HilbertGraphDual hΩ) (2 : ℝ≥0∞)
    (reverseTimeVolume T)
/-- Pointwise application of the spatial value map, lifted to Bochner `L²`. -/
noncomputable def reverseTimeValueCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    ReverseTimeL2V hΩ T →L[ℝ] ReverseTimeL2H hΩ T :=
  (valueCLM hΩ).compLpL (2 : ℝ≥0∞) (reverseTimeVolume T)
end HypoellipticAleksandrov.Parabolic.Dirichlet
