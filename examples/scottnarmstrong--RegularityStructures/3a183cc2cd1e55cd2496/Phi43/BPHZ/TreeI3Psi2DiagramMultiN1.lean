/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramLevel
public import Phi43.BPHZ.TreeI3Psi2DiagramPointwise
public import Phi43.BPHZ.TreeI3Psi2DiagramDefs
public import Phi43.BPHZ.TreeI3PsiDiagramMultiPointwise

/-!
# The weighted diagram `N₁` of `I(Ψ³)Ψ²` with general exponents

The diagram `N₁` (chaos `5`) is the double integral of
`δK(z, w) δK(z', v) · s(w - z')^(-2) s(w - v)^(-1) s(z - v)^(-2)` against a covariance-independent
weight.  In the difference of the fields at two scales (or two mollifiers) one of the five
covariance factors gains a factor `μ s^(-θ)`, so the exponents become `2 + x₁`, `1 + x₂`, `2 + x₃`
with small `xᵢ ≥ 0`.  We prove, for every measurable `F` dominated by this weight, that
`F` is integrable on the product and `|∫∫ F| ≤ C S_{1 + δ + x₁ + x₂ + x₃}(z, z')`, where
`S_p(z, z') = s(z - z')^(-p) + s(z)^(-p) + s(z')^(-p)` (`i3Psi2S`).
The loss `δ > 0` of the exponent of the first factor on the time slab is the one of
[Hai14, p. 170--171].
-/

@[expose] public noncomputable section

namespace RegularityStructures

                                                                                               
            
                                                                
                                                                        
                                                                                        

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

                                                                      
                                               
                         
                            
                                                                                   
                                                                                              

                                                                         
theorem singularPow_loss_le {p δ : ℝ} (hδ : 0 ≤ δ) {c w : SpaceTime}
    (h : 0 < torusParabolicSize (c - w)) (h3 : torusParabolicSize (c - w) ≤ 3) :
    singularPow p c w ≤ 3 ^ δ * singularPow (p + δ) c w := by
  have hpow : singularPow p c w = torusParabolicSize (c - w) ^ δ * singularPow (p + δ) c w := by
    unfold singularPow
    rw [← Real.rpow_add h]; congr 1; ring
  rw [hpow]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow h.le h3 hδ) (singularPow_nonneg _ _ _)

                                                      
                                                                                        
                  
                                                                                        
                                                                       
                                                                       
                                                                               
                                            
                                                                                    
                                          
                                                                                               
                                                     
                                        
                                                                  
                                                               
                                                                      
                                                                          
                                                     
                                                             
                                                                 
                         
                           
                                                     
                                   
                                     
                                                           
                                                                        
                                                                            
                                                           
                                                                                    
                                                     
                   
                                                                                      
                                                                  
                                                                                        
                                                                   
                                                                                        
                                                                 
                                                        
                                                                
                                                        
                                                                
                                                        
                                                               
                                                                                                 
                                                       
                                                          
                                                             
                                                                       
                                                                                                   
                                                       
                                                                             
                                                    
                                                                                        
                                                                  
                                    
                                         
          
                                                                                   
                     
                         
                       
                                                                               
                   
                       
                     

end RegularityStructures

end

