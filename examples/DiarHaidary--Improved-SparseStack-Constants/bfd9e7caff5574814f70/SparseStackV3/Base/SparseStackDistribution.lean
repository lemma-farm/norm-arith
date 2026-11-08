/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

VENDORED BASE MODULE.  This file is copied verbatim (apart from its import
paths and this header) from the author's Version 2.0 formalization at
https://github.com/DiarHaidary/Nelson-Nguyen-conjecture-upper-bound-palomar
(`SparseFockFormal/SparseStackDistribution.lean`).  The sketch distribution, the Parseval-frame
encoding of `U`, the finite-probability API and the operator-norm/trace
bridge are unchanged between Version 2.0 and Version 3.0 of the manuscript,
so they are reused rather than reproved.
-/
import SparseStackV3.Base.SparseStackModel
import SparseStackV3.Base.FiniteProbability
import Mathlib

namespace SparseFock

namespace SparseStackDistribution

open SparseStackModel

noncomputable section

instance : Fintype Sign where
  elems := {.plus, .minus}
  complete x := by cases x <;> simp

                                                              

                                                             
                                         

                                                                               
                                                                     
                                                  
                     
           
                                
                                                          
                  
                            
                                                                 
              

                                                        
                                                              

                                                                             
                                               
                                                                          
                                                                          

                                                                            
                                                    
                                                                   
                       
                          

                                                               
                             
                                               

                                                               
                             
                                              

                                                               
                                                                    
                                                         
                               
     

                                                                              
                                                               
                                            
                                                                        
                                         
                                         
                                                      

                                                                          
                    
                                                   
                                                     
                                                              
                                                   
                                                  
                                                      

                                    
                                                                
                                                             
                                                               
                                                                                
                     
                            
      
            

                                       
                                                               
                                                       
                                                               
             
                                                                                  
                           
                                  
            
              

end

end SparseStackDistribution

end SparseFock
