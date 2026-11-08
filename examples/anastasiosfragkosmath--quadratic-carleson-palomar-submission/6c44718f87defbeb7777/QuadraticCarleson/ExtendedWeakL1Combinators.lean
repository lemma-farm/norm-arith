/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import QuadraticCarleson.KaltonPaperApplication
import QuadraticCarleson.HardyLittlewoodMaximal

/-!
# Elementary weak-L¹ combinators for extended nonnegative outputs

These lemmas transfer distribution estimates through the concrete pointwise
comparison `F ≤ 2 H + 16 M` used for the finite low-modulation block.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace ExtendedWeakL1Combinators

open KaltonPaperApplication

set_option autoImplicit false

                                          
                                                    
                               
                                                                
                                       
                  
            
                                                                                
              

                                            
                                                    
                               
                                                       
                                       
                            
            
                                                       

theorem HasExtendedWeakL1Bound.restrict
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {A : ℝ} {F : X → ENNReal} (h : HasExtendedWeakL1Bound mu A F)
    (s : Set X) : HasExtendedWeakL1Bound (mu.restrict s) A F := by
  refine ⟨h.1, ?_⟩
  intro a ha
  exact (mul_le_mul' le_rfl (Measure.restrict_le_self _)).trans (h.2 a ha)

                                                                          
                                                                         
                                                                            
                                                          
                                               
                                                                
                                                  
                                                                
                                                      
                                                          
           
                                                         
            
                                                             
                                       
             
                                    
                                                                             
                                                                       
         
                                                        
                                                        
                                        

                                                                          
                                                            
                                                            
                                                    
                                     
                                        
                                         
                                           
                                                        
                           
                           
                            
            
                                               
                                                      
                                                       
                                       
                                         
                                                                              
                                                                                 
           
        
                                                              
                            
                                                                                  
           
        
                                                      
                                  
                                                                                 
           
        
                                                            
                                  
                                                    
                                   
           
        
                                                                
                            
                                          
                                                       
           
        
                               
              
                     
                                                 
                                                       
                                                  
                                                       
                                                             
          
                            
                                        
                                                        
                                                                 
                                                             
                                                 
      
                                                                   
                                                                             
                                                                 
                  
                                              
                                                    
                                              
                                                    
                               
                                              
                                                      
                                    
                                           
                                                            
            
                              
                                
                                               
                                                            
                                                       
                                                        
                                                   
                

                                                                            
                                                                     
                                                                   
                                                          
                                 
                                 
                                                           
                                                             
                                                             
            
                                                     
                                       
                  
                                                     
                                                      


end ExtendedWeakL1Combinators
end QuadraticCarleson
