/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.GraphSubspace
import Mathlib
/-!
# Basic bounded block-operator and Riccati definitions

This module contains the dependency-minimal definitions shared by the bounded
Riccati leaf proofs.  The public facade is
`DavisKahan.InfiniteDimensional.Riccati.Bounded`.
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