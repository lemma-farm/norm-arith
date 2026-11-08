/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Tendsto
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# The test-function bound `|⟨Λ, φ^λ_{x₀}⟩| ≲ λ^γ`

* `tendsto_integral_pairing`: `∫ Λ_s φ → ⟨Λ, φ⟩` as `s ↓ 0`;
* `abs_pairing_le`: `|⟨Λ, φ⟩| ≤ C · pairingConst A · (B₀ + B₁) · λ^γ`.

This is the bridge from the `Q`-distribution `Rf - Π_{x₀} f(x₀)` of local order `γ` to the
reconstruction bound [Hai14, Theorem 3.10, (3.3)]. Here `φ` is a test function adapted to the
scale `λ` (`∫ |φ| ≤ B₀`) with `ψ = Lφ` (`∫ |ψ| ≤ B₁ λ^{-ℓ}`). The proof evaluates the increment
bounds of `LocalData.abs_integral_sub_le` at `T = λ^ℓ`: `|G(T)| ≤ C B₀ |A| λ^γ` and
`|G(T) - G(s)| ≤ C B₁ (∑_a ℓ/(a+ℓ)) λ^γ`.

Source: [Hai14] = arXiv:1303.5113v4.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

                                                                                   
                                 
                                                                       
                                                               
                        
                  
                                        
                                                                                   
                                               
              
                                                        
                                                                             
                                                       
                                                                   
                
                                                                                    
                                                                    
                                                                       
                                                     
                             
                                     
                                               
                                  

end RegularityStructures.RegularisingSemigroup

end
