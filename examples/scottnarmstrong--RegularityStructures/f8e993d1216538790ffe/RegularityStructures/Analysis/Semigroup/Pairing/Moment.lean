/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Kernel moments against a distribution of local order `γ`

If `Λ` is of order `γ` at `x₀` (`IsLocalOrder`), the kernel moment bounds control
`∫ |Q_v(y, z)| |Λ_s(z)| dz` uniformly in `v ≤ h₀` and in the points `y` with `d(y, x₀) ≤ λ`
(`exists_integral_abs_kernel_mul_le`); this is the integrability input for the Fubini arguments in
`RegularityStructures.Analysis.Semigroup.Pairing.Swap`.

* `LocalData`: bundle of the standing hypotheses on `Λ`;
* `abs_le_of_isLocalOrder`: `|Λ_u(y)| ≤ C ∑ u^{a/ℓ} λ^{γ-a}` where `d(y, x₀) ≤ λ`;
* `rpow_add_le_mul`: `(x + y)^r ≤ 2^r (x^r + y^r)`.
-/

public section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

                                                                            
                                               
                                     
                                  
                                   
                                  
                                               
                                                                                 
                                                               
                                     
                                                                            
                                       
                                       
                                    
                                     
                                    

end RegularityStructures.RegularisingSemigroup

end
