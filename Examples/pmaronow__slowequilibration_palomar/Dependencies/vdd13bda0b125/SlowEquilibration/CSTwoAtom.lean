-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.CrisantiSommers
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.CSVariation
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.NonconvexCertificate
set_option autoImplicit false
@[expose] public section
namespace SlowEquilibration.CrisantiSommers
open MeasureTheory Set
/-- The manuscript's admissible measures, with their ordinary probability law.
The cutoff is a witness of compact support below one, not a parameter of the value. -/
structure Admissible where
  law : Measure ℝ
  probability : IsProbabilityMeasure law
  cutoff_exists : ∃ q, HasCutoff law q
instance (ζ : Admissible) : IsProbabilityMeasure ζ.law := ζ.probability
end SlowEquilibration.CrisantiSommers
namespace SlowEquilibration.NonconvexCertificate
open MeasureTheory Set CrisantiSommers
end SlowEquilibration.NonconvexCertificate
