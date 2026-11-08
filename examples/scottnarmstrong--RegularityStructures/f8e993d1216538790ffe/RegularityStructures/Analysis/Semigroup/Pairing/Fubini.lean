/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Swap

/-!
# Fubini in the time variable

Integrability of `(v, z) ↦ Λ_s(z) (Q_v φ)(z)` on `(0, h] × E`, which allows to exchange the
integral `dv` of the integrated generator identity with the pairing against `Λ_s`.

* `measurable_apply_uncurry`: `(v, z) ↦ (Q_v g)(z)` is measurable if the kernel is jointly
  measurable;
* `LocalData.exists_integral_norm_mul_apply_le`: `∫ |Λ_s Q_v φ| ≤ W ∫ |φ|` uniformly in `v ≤ h₀`;
* `LocalData.integrable_uncurry_apply`.
-/

public section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

                                                                                   
                                                                               
                                                                                  
                                                         
                                                                                                 
                                               
                                                                                         

end RegularityStructures.RegularisingSemigroup

end
