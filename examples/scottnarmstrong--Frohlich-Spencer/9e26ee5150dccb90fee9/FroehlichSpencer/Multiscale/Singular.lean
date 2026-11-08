/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Multiscale.Basic
public import FroehlichSpencer.Multiscale.Clusters
public import FroehlichSpencer.Surface.HamiltonianHermitian
public import Mathlib

/-!
# The singular-set recursion

FS83 (2.3)-(2.7) : `S_{i+1} = S_i ∖ S_i^g`, where `S_i^g` is the union of all
gentle `2 r_i`-chain clusters of `S_i`.
-/

@[expose] public section

namespace FroehlichSpencer.Multiscale


                                                                                   
                                                 
                                                          
                                                
                                                                                                  
              

   
                                                                                        
                              
  
                                                                                     
                                                         
                                                                                      

                                                                                                
                                                                                  
                                                           
           
                                                                                               

                                                                        
                                                                            
                                        

                                                                                            
                                                                                
                       
                                                          

variable {ν : ℕ} (P : Params) (blk : Finset (Site ν) → Finset (Site ν)) (S₀ : Set (Site ν))
  (v : Site ν → ℝ)

                                      
                                        
                                                                                               

                                                                                       
                           
                          
                                

                                                                           
                                     
                             
                          

                                                                                  
                                                     

                                                           
                                                                               
                          
                                                                                              
                           
                                       
                                                 
                                                                                  
               
                                        
                                                                            
                                                       
                     
                                                             
                         
       

                                                                                
                                                                                           
                                                                         
                          
                                                   

                                                                                               
                                                                 
                        
                                

                                                             
                                             
                                              

end FroehlichSpencer.Multiscale
