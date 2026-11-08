module
/-
Modified for this project: compatibility adaptations and source-comment cleanup.
Apache-2.0: vendor/LICENSE. Provenance: vendor/PROVENANCE.json.
-/
/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.FilteredQuadraticVariation
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.StochasticCalculus.ItoFormulaPartition
set_option autoImplicit false
public section
/-!
# Quadratic covariation of the actual independent coordinate drivers

All independence below comes from the whole coordinate path laws in
`BrownianDriver`. In particular, coefficient processes may observe the full
filtration and the initial background.

The deterministic stopped-partition estimates are adapted from Ezzeri Esa's
`StochasticCalculus.QuadraticVariation` (Apache 2.0).
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.VectorQuadraticVariation
open HardSphereDynamics VectorIto
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
end SphericalAging.VectorQuadraticVariation
