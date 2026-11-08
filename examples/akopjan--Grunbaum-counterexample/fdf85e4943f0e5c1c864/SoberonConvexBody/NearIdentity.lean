import SoberonConvexBody.FrameBasics
import Mathlib
/-!
# Elementary inverse estimates near the identity

The inverse is constructed by finite-dimensional injectivity. The second-order
estimate follows from the exact resolvent identity, not a matrix power series.
-/
noncomputable section
namespace SoberonConvexBody
open scoped BigOperators
open Tensors

namespace NearIdentity

                                                     
                                                          
                                                 
           
                              
                            
                                                  
        
                                                   
                                           
                          
                                      
                                       
                           
                           

def normalMap {q : Fin 4 -> E4} (hq : IsONFrame q) (n : Fin 4 -> E4) :
    E4 →ₗ[Real] E4 where
  toFun x := WithLp.toLp 2 (fun i => inner Real (hq.toIsometry x) (n i))
  map_add' x y := by
    ext i
    simp [inner_add_left]
  map_smul' a x := by
    ext i
    simp [real_inner_smul_left]

@[simp] theorem normalMap_apply {q : Fin 4 -> E4} (hq : IsONFrame q)
    (n : Fin 4 -> E4) (x : E4) (i : Fin 4) :
    normalMap hq n x i = inner Real (hq.toIsometry x) (n i) := rfl

                                                            
                                             
                                                 
                                                
                                                                           
           
                                                                                    
                                                        
            
        
                                                                                         
                                  
                                                                         
                        
                                                                  
                 
                                                                                
                     

                                                              
                                                                         
               
                                                 
                     
                                   
                                                              
                                           

                                                            
                                                                
                                                     

                                                                              
                                                       
                                        

                                                   
                                                       
                                   
                                         
        
                                    
                  

                                                                      
                                                       
                                    
                         
                                            
                                                                
                                                   
                   
                         
                                    

                                                                   
                                                                      
                                        
                         
                                            
                                        
                                             
           

                                                                          
                                                                      
                                                  
                                                                   
                                    
        
          
                           
                                          
                         
                                             
           

                                                                             

                                                                
                                                                       

                                                                           
                                      
                           
                                
                                                               
                                                  
                                               
                                                          
                                                                                         
                               
                                                       
                        
            
                                                         
                                                                           
                                             
                          
                                                                           
                                                                                                          
                       
           
                                                                                   
                                                                                   
                                                                                      
                                             
             
                                                       
                                                           
                                                       
                                                           

                                                                  
                                              
                                                           
                                               
                                                 
         
            

end NearIdentity
end SoberonConvexBody
