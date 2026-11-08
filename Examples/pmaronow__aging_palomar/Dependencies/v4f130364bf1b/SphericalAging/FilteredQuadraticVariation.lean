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
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.VectorIto
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.StochasticCalculus.QuadraticVariationDensity
set_option autoImplicit false
public section
/-!
# Quadratic variation in an enlarged Brownian filtration

Adapted from Ezzeri Esa's `QuadraticVariation`, `QuadraticVariationElementary`
`QuadraticVariationDensity` and `QuadraticVariationGrid` (Apache 2.0). The natural-filtration equality
is replaced by the actual increment independence `IsFilteredPreBrownian`.
All bracket convergence statements concern the constructed stochastic integral.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped BigOperators ENNReal NNReal InnerProductSpace
namespace SphericalAging.FilteredQuadraticVariation
variable {W : Type*} [MeasurableSpace W] {P : Measure W} [IsProbabilityMeasure P]
  {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
end SphericalAging.FilteredQuadraticVariation
