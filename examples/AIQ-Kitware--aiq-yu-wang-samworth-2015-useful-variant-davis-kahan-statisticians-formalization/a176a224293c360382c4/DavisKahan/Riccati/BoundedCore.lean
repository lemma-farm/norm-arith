/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import DavisKahan.Riccati.BoundedBasic
import Mathlib
/-!
# Bounded graph invariance and the operator Riccati equation

This leaf module proves the algebraic foundation for the bounded Riccati
program.  For the self-adjoint block data used by Davis--Kahan, invariance of
the graph of an angular operator is equivalent to vanishing of its Riccati
defect.  The later reduction, existence, uniqueness, and block-diagonalization
steps can build on this result without repeating direct-sum coordinate algebra.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

                                                                             
                                                
                                                                      
                         
                        

                                             
                                                               
       
                                     
                                
                                                           
     

                                             
                                                       
       
                                
                                                          
                       
                                            
                                                              
     

                                             
                                                                               
                                                           
                               
                                         
                                                       
             
              
                                                 
                                                              
                                  
                                                          
                                             
                                               
        
                          
                                
            
                                          
                                                        
           

                                                                
                              
                                                          
                               
                                                      

                                             
                                                      
                                   
                                                          
                       
                       
               
                                                             
             
              
                                           
             
         
          
                                                                   
                
        
                            
                                                                 
                                                
                  
                                                          
                                                    
                
                                 
           
          
                                                             
                       
                      
        
                                                           
                                  
                                                
                  
                                 

                                             
                                                                               
                                 
                                              
                                                          
                       
                                                            
                                  
             
                
                                                                  
                                                 
         
                                                          
          
                   
                                                      
                              
                                    
                                                           
                     
                                               
           
          
                                                             
                                 
                                    
                                                      
                  

end DavisKahanExt
end TauCeti