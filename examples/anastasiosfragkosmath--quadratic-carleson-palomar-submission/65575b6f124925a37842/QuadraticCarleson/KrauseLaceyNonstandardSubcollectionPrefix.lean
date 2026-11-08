import QuadraticCarleson.KrauseLaceyNonstandardMaximalPrefix
import Mathlib
/-!
# Prefix bounds for arbitrary genuine nonstandard subcollections

This is the form needed after overlap pruning: the finite family is any
literal subset of the actual nonstandard collection, and the prefix length
is arbitrary. No estimate for the pruning operation is assumed or claimed.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers KrauseLaceyRademacherMenshov

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

                                              
                                                                                 
                                                                             
                                  
                                                         

                                          
                                                                                 
                                                                             
                                                                    
                                                        
                                                                 
                                                                                     
                                                 
                                           
                                               
                                                          
                                                                                         
                                 
                                                           
                               

                                                                   
                                                                          
                                                           
                                                             
                                                              
                              
                                                          
                                                                                   
                                                                              
                                                                                         
                                                                                   
                                                  
            
                                                           
                                              
                                    
                                                                                             
              
                                                   
         
              
                     
                                                           
              

noncomputable def badSubcollectionPrefixMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (M : ℕ) (x : ℝ) : ℝ :=
  ⨆ n : Fin (M + 1), ‖∑ i ∈ Finset.range n.val,
    krauseLaceyCollectionAction (generation N i) scale
      (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖

                                           
                                                                                 
                                                                             
                                                                  
                                                                                       
                                    
                                                               
                                                          
                                                                  
                                                                                      
                                 
                                                          
                  
         
         
                                                   

                                           
                                                                                 
                                                                             
                                                                    
                                                                                     
                                   

                                                                       
                                                                          
                                              
                                                
                                                             
                                                              
                              
                                                          
                                                                                   
                                                                              
                                                                                         
                                                                            
                                            
                                                               
                                                                                      
                                                                    
                                                                 
                                                                                   
                            


end KrauseLaceyBadScale
end QuadraticCarleson
