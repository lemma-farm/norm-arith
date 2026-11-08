/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramLeaves
public import Phi43.BPHZ.TreeI3PsiChainBasic

/-!
# Pointwise majorants for the diagrams of `I(Ψ³)Ψ²`

Bounds of the covariance entries by centred powers, `|Q(c - w)| ≤ B s(c - w)^(-1)`, its square
(with and without a loss `δ` of the exponent, the latter on the slab `|t| ≤ 4`), and the time
slab on which the recentred kernel `δK(z, ·)` lives.
-/

public section

open MeasureTheory

namespace RegularityStructures

                                      
                                                                                       
                   
                            
                                       
                                   
            
                               
                   

                                      
                                                        
                                                                                        
                                                            
                                          
        

                                        
                                                           
                                                                                        
                                                            
                                                     
                                      
                                                             
                                        
                                
                    
                                                                               
                                                  
          

                                                                      
                                                                               
                                                                                        
                                                                                   
                                                                
                                       

                                                                                      
                                                                                 
                         
                                     
           
                                         

                                                 
                                                                                    
                               
                             

                                                                                   
theorem singularPow_mul_self_eq {a b e : ℝ} (hab : a + b = e) (c w : SpaceTime)
    (h : 0 < torusParabolicSize (c - w)) :
    singularPow a c w * singularPow b c w = singularPow e c w := by
  rw [singularPow_mul_self a b c w h, hab]

/-- Almost-everywhere merging of two powers with the same centre. -/
theorem ae_singularPow_mul_self {a b e : ℝ} (hab : a + b = e) (c : SpaceTime) :
    ∀ᵐ w : SpaceTime ∂volume, singularPow a c w * singularPow b c w = singularPow e c w := by
  filter_upwards [ae_torusParabolicSize_sub_pos c] with w hw
  exact singularPow_mul_self_eq hab c w hw

/-- Flipping the centre: `s(w - c)^(-p) ≤ 2^p s(c - w)^(-p)`. -/
theorem rpow_neg_flip_singularPow {p : ℝ} (hp : 0 ≤ p) {c w : SpaceTime}
    (h : 0 < torusParabolicSize (c - w)) :
    torusParabolicSize (w - c) ^ (-p) ≤ 2 ^ p * singularPow p c w :=
  torusParabolicSize_rpow_neg_flip_le' hp h

end RegularityStructures

end
