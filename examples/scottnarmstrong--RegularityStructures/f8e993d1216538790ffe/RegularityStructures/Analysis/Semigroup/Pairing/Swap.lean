/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Moment
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Self-adjointness of `Q_h` against a distribution of local order `γ`

* `integral_mul_apply_eq`: `∫ (Q_h g) φ = ∫ g (Q_h φ)` (Fubini and symmetry of the kernel) when
  `Q_h(y, z) g(z) φ(y)` is integrable on `E × E`;
* `LocalData.integrable_prod`: that integrability holds for `g = Λ_s`, `Λ` of local order `γ` at
  `x₀` and `φ` measurable, integrable and supported in `{d(·, x₀) ≤ λ}`;
* `LocalData.integral_apply_mul`: `∫ Λ_{s+h} φ = ∫ Λ_s (Q_h φ)`.
-/

public section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- `φ` is a test function adapted to `x₀` at scale `λ`: measurable, integrable and vanishing
where `d(y, x₀) > λ`. -/
structure IsSupported (φ : E → ℝ) (x₀ : E) (lam : ℝ) : Prop where
  meas : Measurable φ
  integrable : Integrable φ μ
  supp : ∀ y, lam < K.scaleDist y x₀ → φ y = 0

                                                                                    
                                                                                          
                                                                   
                                                                                     
                                                                          
                         
                                 
                                                     
                                                                                
                                         
                                                                          
                         
                                 
                                                                          
                   
                           

                                                                                   
                                                                                          
                                                     
                                         
                                                           
                                                     
                           
                                                                    
             
                     

end RegularityStructures.RegularisingSemigroup

end
