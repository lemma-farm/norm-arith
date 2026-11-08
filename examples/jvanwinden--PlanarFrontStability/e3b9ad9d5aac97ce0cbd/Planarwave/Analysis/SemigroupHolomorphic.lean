/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupGenerator
public import Planarwave.Analysis.HolomorphicTimeExtension
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

/-!
# Real shifts of holomorphic semigroup extensions

The identity principle transfers the real semigroup law to complex time followed by
a nonnegative real time. Together with a bound near zero this gives strong continuity
at the vertex, without asserting operator-norm continuity there.
-/

open Filter Set Topology

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

                                                                              
                              
                                                           
                                                            
                                                                    
                                                 
                                                            
                                                                            
                                                             
                                                   
              
                                                                                    
                                                                         
                                                                  
                                                   
              
                                                                                                     
                                                                              
            
                                                                                 
                                          

                                                                                
                                                                              
                                          
                                                            
                                                            
                                                                    
                                                 
                                             
                                                       
                                                                
                                    
                                    
                                                         
                                                                                  
                                                                                             
              
                                                                               
                                                       
                                                            
                                
                                                                    
                                          
                                                      
                                                         
              
                        
                                             
                                                             
        
                                              
                                                                          
                                                                                    
                                      
                                                                                             
              
                                                                                           
                                                         
                                               
              
                                                                                            
                                                           
                                
                                                                                             
            
                          
                                        
                                                                       
                                                                                  

                                                                            
                                                                
                                                               
                                                     
                         
                                                                    
                                                 
                                                                               
                                                                                    
                               
            
                                                    
                                                       
                                                                    
                    
                                             
                                                            
                                      
                                                
               
              
                                                                                           
                                                                
                                                                                           
                                                                                                   
                                                                   
                                                                                    
                                                          
                                            
                                   
                                                        
                                                                             
                                     
                                                                            
                                                                                              
                   
                                                       
                                                                       
                                                                  
                                                     
        
                                                                          
        
                                                           
                                        
                         
                                                                       
                                                            
                                                                        
             
              
                                      
                                                            
                                          
             

end

end C0Semigroup
