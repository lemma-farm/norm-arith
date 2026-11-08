/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramMultiN1
public import Phi43.BPHZ.TreeI3PsiChainBasic

/-!
# The weighted diagram `N₂` of `I(Ψ³)Ψ²` with general exponents

The diagram `N₂` (chaos `3`) is the double integral of `δK(z, w) δK(z', v)` against the weight
`s(w - z)^(-1) s(w - z')^(-1) s(w - v)^(-1) s(v - z')^(-1) s(z - v)^(-1)`.  Each of the five
exponents may be raised by a small `yᵢ ≥ 0` (the factor `μ s^(-θ)` of one covariance in the
difference of the fields), and the exponent of `s(w - z)` also carries the slab loss `δ`.  This file
contains the pointwise domination by the majorant `i3Psi2N2Majorant`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The majorant of the diagram `N₂`: exponents `1 + ν₁` at `(z, w)`, `1 + y₂` at `(z', w)`,
`1 + y₃` at `(w, v)`, `4 + y₄` at `(z', v)`, `(0, v)` and `1 + y₅` at `(z, v)`. -/
def i3Psi2N2Majorant (ν₁ y₂ y₃ y₄ y₅ : ℝ) (z z' w v : SpaceTime) : ℝ :=
  ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + ν₁) z w *
      singularPow (1 + y₂) z' w) *
    ((3 * singularPow (4 + y₄) z' v + singularPow (4 + y₄) 0 v) * singularPow (1 + y₅) z v *
      singularPow (1 + y₃) w v)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

                                                                             
                                                      
                         
                            
                                                                                               
                                                                                             
                                             

                                                      
                                                                                              
                                                
                                                                                        
                                                                       
                                                                       
                                                                               
                                            
                                                                                    
                                          
                                                                                               
                                                                                                
                                                     
                                                                      
                                                            
                                                               
                                                                       
                                                                       
                                                                       
                                                                    
                                                                               
                                                                                  
                                  
                         
                           
                                                    
                                   
                                     
                                                          
                                                                       
                                                                          
                                                         
                                                                                    
                                                     
                   
                                                       
                                                           
                                                     
                                                                  
                                                           
                                                     
                                                                 
                                                                                              
                                                                                              
                                                     
                     
                                                              
                                                                        
                                                  
                                                          
                                                                                   
                                                                                               
                                                                                        
                                                                          
                                  
                         
                                                                              
                                                              
                                                             
                                                                                 
                                   
                                                                             
                                                      
                                                                                  
                                                                  
                                                                                        
                                                                
                                                        
                                                                 
                                                        
                                                                
                                                        
                                                                 
                                                        
                                                                
                                                        
                                                       
                                                  
                                                                        
                                       
                                                                           
                                                                  
                                                         
                                                                                  
                                                        
                                                         
                                                                        
                                                            
                                                                                                 
                 
                                                                                    
                                                         
                                                                                
                                                                                                    
                                                          
                                                                        
                                                            
                                                                                              
                                                                                                     
                                                                    
                                                                           
                                                                         
                                  
                                                             
                             
                                           
            
                                                                                   
                     
                         
                       
                                                                               
                   
                       
                     

end RegularityStructures

end
