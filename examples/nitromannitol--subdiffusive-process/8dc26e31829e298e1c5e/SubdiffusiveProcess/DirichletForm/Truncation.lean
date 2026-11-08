/-
# The zero-trace truncation `T_ε(s) = sgn(s)(|s| - ε)₊`
-/
module

public import SubdiffusiveProcess.DirichletForm.EnergyMeasure
public import Mathlib
@[expose] public section

/-!
# The zero-trace truncation

`T_ε(s) = sgn(s)(|s| - ε)₊`, written here as the soft threshold
`max (s - ε) 0 - max (-s - ε) 0`, is the normal contraction used to show that a
continuous function of the domain vanishing on the boundary of an open set lies
in the killed space of that set.  This file records its elementary properties:
it is a normal contraction, it vanishes on `[-ε, ε]`, it differs from the
identity by at most `ε`, and it has derivative `1` off `[-ε, ε]` and `0` inside.
-/

open Real

noncomputable section

namespace SubdiffusiveProcess.DirichletForm

                                                                                  
                                                              

                                                                  
                   

                                                           
                                                                                           
                                                            
                                            
      

                                                          
                                                                   
                                
                                                         
                                               
      

                                   
                                                                                
                                     
                                      
                                                         
                                            
      

                                     
                                                               
                                            
                               
                   
                                  
                                 
               
                   
                                       
                              

                                                      
                                                                 
                                  
             
                 
                                     
                            

                                                    
                                                                         
                                       
                                                           
                                                                                 
                                                                                
                                    

                                                             
                                                                              
                                       
                                                           
                                                                                     
                                                                                
                                    

                                                              
                                                                  
                                       
                                                             
                                                                                     
                                                                                         
                                                                               
                                    

section Level

variable {X : Type*} [TopologicalSpace X]

                                                        
                                                          
                                             
                                                              

                                                                          
                                                                         
                                                                         
                                           
                                                      
                                                 
                                        
                              

                                                                
                                                                 
                                              
                     
                                      
                           
           
                           
            
                                                           
                             
                  
                         
                              

end Level

end SubdiffusiveProcess.DirichletForm
