module

public import Mathlib
import all Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

/-!
# Riesz synthesis on coefficient space

This file fixes the coefficient-space interface used by the atomic Hermite
model.  A Riesz basis is represented by a continuous linear equivalence from
`ℓ²`; this records both the synthesis map and its bounded inverse without
hiding either bound in an unbundled predicate.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped lp

/-- Square-summable complex coefficients indexed by `ι`. -/
abbrev CoefficientSpace (iota : Type*) := ℓ²(iota, ℂ)

                                                        
                                            
                                                  
                                                    

                                                    
                                               
                            
                                

                                                                           
                                                                      
                                                                                                        
             
                                                             
                                                   
                                                 

       
                                                                           
                                 
                                                      

                                                                        
                                            
                                                    
                                            
                            
                                      
                                    

                                                                         
         
                                                
                                       
                                            
                                         
                                                    
                   

                                                                 
                              
                                                             
                                                                     
                                              
                                     

                                                 
                                          
                                                             
                                                                     
                                                      
                                                          

end

end MeyerGeneralProblem
