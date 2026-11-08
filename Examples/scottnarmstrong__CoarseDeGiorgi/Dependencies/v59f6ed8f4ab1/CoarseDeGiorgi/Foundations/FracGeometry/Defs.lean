module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.Homogenization.Multiscale.CubeAverage
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Prod
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Foundations.Euclid.Gagliardo
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Statements.EuclidDist
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Statements.FracSeminorm
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Statements.FracNorm
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Statements.CubeSurface
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Statements.CubeFaceMeasure
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Statements.SurfaceMeasure
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Statements.SurfaceFracSeminorm
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Statements.SurfaceFracNorm
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
namespace CoarseDeGiorgi.Foundations.FracGeometry
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
/- Compatibility names retain the existing implementation API while all mathematical
bodies are supplied by the `Statements/` definitions. -/
abbrev surfaceMeasure {d : ℕ} (τ : ℝ) : Measure (Vec d) :=
  CoarseDeGiorgi.surfaceMeasure τ
variable {d : ℕ}
/-- Compatibility access to the coordinate-face measure for Fubini arguments. -/
abbrev faceMeasure (τ : ℝ) (i : Fin d) (positive : Bool) : Measure (Vec d) :=
  CoarseDeGiorgi.cubeFaceMeasure τ i positive
theorem faceMeasure_eq_pi (τ : ℝ) (i : Fin d) (positive : Bool) :
    faceMeasure τ i positive = Measure.pi (fun j : Fin d =>
      if j = i then Measure.dirac (if positive then τ / 2 else -τ / 2)
      else volume.restrict (Set.Ioo (-τ / 2) (τ / 2))) := rfl
private instance faceCoordinateMeasures_finite (τ : ℝ) (i : Fin d) (positive : Bool)
    (j : Fin d) : IsFiniteMeasure (CoarseDeGiorgi.faceCoordinateMeasures τ i positive j) := by
  unfold CoarseDeGiorgi.faceCoordinateMeasures
  split_ifs <;> infer_instance
private instance cubeFaceMeasure_finite (τ : ℝ) (i : Fin d) (positive : Bool) :
    IsFiniteMeasure (CoarseDeGiorgi.cubeFaceMeasure τ i positive) := by
  unfold CoarseDeGiorgi.cubeFaceMeasure
  infer_instance
instance faceMeasure_finite (τ : ℝ) (i : Fin d) (positive : Bool) :
    IsFiniteMeasure (faceMeasure τ i positive) := by
  unfold faceMeasure
  infer_instance
/-- The surface measure (sum of face measures) is finite, even at an inadmissible radius. -/
instance surfaceMeasure_finite (τ : ℝ) : IsFiniteMeasure (surfaceMeasure (d := d) τ) := by
  unfold surfaceMeasure CoarseDeGiorgi.surfaceMeasure
  infer_instance
end
end CoarseDeGiorgi.Foundations.FracGeometry
