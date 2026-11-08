/-
# Crouzeix--Palencia assembly along compact exhaustions

This file joins compact-set sup-norm convergence to the sequence-limit
auxiliary assembly.  It reduces the exact Crouzeix--Palencia conclusion to
constructing the sharp auxiliary bounds at every stage of a decreasing
compact exhaustion of the closed numerical range.

## Main declaration

* `crouzeix_palencia_of_antitone_compact_auxiliary_bounds` -- exact L4.2
  from stagewise auxiliary bounds along a decreasing compact exhaustion.
* `crouzeix_palencia_of_compactThickening_auxiliary_bounds` -- the canonical
  specialization to closed thickenings of the closed numerical range.
-/
import Operator.Crouzeix.ApproximationSupNorm
import Operator.Crouzeix.CompactThickeningApprox
import Operator.Crouzeix.PalenciaApproximation
import Mathlib
open Filter Set
open scoped InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

                                                                       
                                                                          
                                                                              
                                                              
                                   
                                                          
                                     
                                                      
                                                          
                                                                       
                                                                   
                                                
                                        
                                                       
         
                                                        
                                                                    
                                
                     
            

                                                                         
                                                                         
                                                                           
                                                                        
                
                                                                           
                                   
                                                          
                                     
                                                      
                                                        
                                                             
                                               
                                               
                                             
                                      
                                                                   
                                         
                                          
                                                
                                        
                    
                                                              
           
         
                                                                                      
                            
                                                                
                     
                                
                     
             
                          
             
                                                  
           
                                                                      
                                  
                       
                                                      
                                                            

                                                                           
                                                               
                                 
                                                                            
                   
                                                        
                                                      
                                                                 
                                               
                                               
                                     
                                                                      
                             
                                                                       
                                                                   
                                                                 
                                                                     
                                                
                                        
                                                  
               
               
                                                    
             
                                                                    
                           
                                                                    
                                                                 
               
                                                                
                                                               
                                                         
                                                     
                                                   
                                      
                                                                
                                                            
                                                   
                                 
                                                     
                
                                              
                                                                   
                                  
                                                            
                                                                                  
         
                                                                         
                                                                        

                                                                             
                                                                        
                                                                          
                                                                        
                                                               
                   
                                                          
                                       
                                 
                                                                      
                                  
                             
                                                                           
                                                
                                        
                                                  
               
               
                                                    
             
                                                                    
                           
                                                                    
                                                                 
               
                                                                
                                                               
                                                         
                                                     
                                                   
                                      
                                                                
                                                            
                                                   
                                 
                                                     
                
                                              
                                                                   
                                  
                                                            
                                                                                  
                                                                    
                                                    
