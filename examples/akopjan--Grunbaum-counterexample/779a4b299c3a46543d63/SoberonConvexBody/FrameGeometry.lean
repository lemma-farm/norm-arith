import SoberonConvexBody.FrameBasics
import SoberonConvexBody.SphereParity
import SoberonConvexBody.Cells
import Mathlib
/-!
# Orthonormal-frame coordinates

Convert the unbundled frame used by the original project into a bundled
linear isometric equivalence. This avoids postulating any rotation lemma.
-/

noncomputable section
namespace SoberonConvexBody
open Set MeasureTheory
open scoped BigOperators


namespace Cells

/-- Product formula with the project's original boundary convention. -/
theorem signCharacter_eq_prod (c : HyperplaneCfg) (I : Walsh4.Index) (x : E4) :
    signCharacter c I x =
      ∏ i ∈ I, if c.offset i <= inner Real x (c.normal i)
        then (1 : Real) else -1 := by
  unfold signCharacter Walsh4.char Walsh4.charZ
  rw [Int.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : c.offset i <= inner Real x (c.normal i)
  · simp [pattern, not_lt.mpr h, h]
  · have hh : inner Real x (c.normal i) < c.offset i := lt_of_not_ge h
    simp [pattern, hh, h]

                                                                         
                                        
                                         
                                                         
                                                                     
          
                              
           
                      
                                                         
                          
                          

                                                                     
                                                         
                                                         
                                               
                                               
                                                         
                             
           
                                                             
                                                  
                                                

                                                                           
                                                        
                                     
                                                                               
                                                                       
     

end Cells

namespace SphereGeometry

                                                                     
                                                                               
                                          
                                                                      
                               
                                              
                                                       
                                                 

                                                     
                                                    
                                                      
                                     
                                                       
                                                                
                                      
                                                                          
           
                                                                     
                                                                  
                                           
            

                                                            
                                            
                                                              
                      
                                                             
                                                              
                                                                          
                                              
                                                       
                                       
                                                        

                                                            
                                            
                                                              
                      
                                                             
                                                              
                                                                          
                                              
                                                       
                                       
                                                        

                                                            
                                            
                                                              
                      
                                                             
                                                              
                                                                          
                                              
                                                       
                                       
                                                        

                                                            
                                            
                                                              
                      
                                                             
                                                              
                                                                          
                                              
                                                       
                                       
                                                        

                                                             
                                             
                                                              
                      
                                                               
                                                              
                                                                               
                                              
                                                       
                                       
                                                         

end SphereGeometry
end SoberonConvexBody
