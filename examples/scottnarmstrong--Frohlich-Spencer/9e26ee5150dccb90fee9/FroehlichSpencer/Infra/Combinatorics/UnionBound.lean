/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.ProductMeasure
public import FroehlichSpencer.Infra.Combinatorics.Animals
public import Mathlib
/-!
# Independence over disjoint blocks

Product formula for events depending on pairwise disjoint sets of sites, and the bound
`P(⋂ A_k) ≤ q ^ |⋃ S_k|` when `P(A_k) ≤ q ^ |S_k|`, as used in Fröhlich–Spencer (1983),
Sects. 5–6 (Fröhlich–Spencer (1983)).
-/

@[expose] public section

namespace FroehlichSpencer.Infra

section Independent

open MeasureTheory
open scoped ENNReal

variable {ι κ : Type*}

                                                                                              
                                                                               
                                           
                                                                           
           
                                                                            
                                                           
                                               
                                                          
                                                                              

                                                                                              
                                                                           
                                                                                  
                                                             
                                                                  
                                                                                          
                                        
                                                                           
                                                         
                              

end Independent

section Animals

open MeasureTheory
open scoped ENNReal

variable {V : Type*} (G : SimpleGraph V)

                                                                                             
                                                                                  
                                                                         
                                  
                                                                   
                     
            
                                  
                                                            
                                                
                                           
               
                              
                                                                       
                                       
                                                                 
                                                                                
                                                        
                
                                                 
                                                  
                                                             
                                                                         
              

                                                                                              
                                                                                     
                                                              
                                                      
                                                                           
                                            
                                                              
                                                                
                                                                         
                        
                                                                                         
                       
            
                                                                
                         
                 
                                                                             
                                                                                  
                           
                   
                               
                                                                                          
                                              
                                                     
                                                           
                                           
                  
                                           
                                                                      
                                     
                                                 
                                  
                                                            
                                                                                 
                         
                         
                
                                                    

                                                                                              
                                                                    
                                                                   
                                                             
                                                                         

                                                                                  
                                                                                   
                                                                             
                                                                     
                                                    
                                               
                                                                                             

end Animals

end FroehlichSpencer.Infra
