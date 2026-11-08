module
public import Examples.na0b__gaussianriesz_lean.Dependencies.v888864f55c85.GaussianRiesz.Preamble
set_option autoImplicit false
@[expose] public section
open MeasureTheory
noncomputable def GaussMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  volume.withDensity
    (fun x => ENNReal.ofReal (Real.pi ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2)))
