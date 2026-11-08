/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import DavisKahan.Riccati.BoundedCore
import Mathlib
/-!
# Bounded Riccati graph reduction

This leaf module completes the geometric upgrade from bounded graph invariance
to graph reduction.  The block operator determined by self-adjoint diagonal
blocks and mutually adjoint off-diagonal blocks is symmetric.  Consequently,
invariance of an angular graph already implies invariance of its orthogonal
complement.  Combining this observation with the algebraic result in
`BoundedCore` identifies reducing graph subspaces exactly with bounded
solutions of the operator Riccati equation.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

                                             
                                                                              
          
       
                           
                                                          
                              
                       
                   
                                                    
                                                        
     

                                             
                                                                           
                                                         
                                   
                                                            
                                                 
           
                             
                             
                             
                             
                                  
                                                 
                                  
                                                 
                                                   
                              
                                                      
        
                        
                                             
                                            
                                                
                                                                        
                             
                                     
        
                              
                              
                                                          
                                    
        
                                          
                                              
                                            
                                            
      
                                          
                                                
                                              
                                                    
                                            
                                                  
                                                  
       
                                              
                                                    
          

                                             
                                                                           
                                                                 
                                            
                                                          
                       
                                                                      
             
              
                                                               
            
                                                                      
                                                           

end DavisKahanExt
end TauCeti