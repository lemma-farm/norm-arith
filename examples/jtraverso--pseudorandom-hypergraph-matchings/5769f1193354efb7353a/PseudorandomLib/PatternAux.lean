/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PatternCount
public import Mathlib
/-! # Auxiliary weight functions for the proof of Theorem 3.1

For an `ℓ`-set weight function `w`:
* `nrm ℓ w T = ∑_{|e| = ℓ, e ⊇ T} w e` is the quantity `ω(T)` of (1.1);
* `wt ℓ w t T = ∑ w e` over the `ℓ`-sets `e ∋ t` whose elements below `t` are exactly `T`
  (the function `ω^{t,k}` of the paper, on `k`-sets `T`);
* `wle ℓ w t = ∑_{s < t} wt ℓ w s` (the function `ω^{≤t-1,k}`).
-/

@[expose] public section

namespace Pseudorandom

namespace Patt

open Finset

variable {n q : ℕ}

                                             
                                                                                  
                                                          

                                     
                                                                                             
                                                                                 

                                                              
                                                                                          
                                                              

                                                                                  
                                                             
                                                         
                                               

variable {ℓ : ℕ} {w : Finset (Fin n) → ℝ}

                                                                                          
                            

                                                                                        
                                        

                                                                              
                            

                                                                                   
                                    
            
                                      
                                                              
                                       

                                        
                                                            
                                                   
                  
                 
                          
               
                                                         
                    
             
                      
                              
                                           
                                                                          
                                      
                                 
                                 

                                                                                    
                                                                                   
                              
                                         
                                                                                       
                                                                                            
               
                                                                   
                                                           
                                                                           
                                       
                                      
         
                                                                           
               
                           
               
                                        
                                   
                          
              
                                                                           
                              

                                                                                 
                                                     
           
               
                                        
                                      
           
                          
                            
                                                                  
                           

                                                                              
                                           
           
                
               
                                                                                           
                                                           
                                                                                 
           
             
                                          
                                                                                        
                                                            
                                                                           
                                                                  
                                                                                  
                                                                   
                     
                      
                                      
           
                            
                 
                                                                                     
                                                          
                                        
                 
                              
                                                                   
                                                    
                                                                                        
                                       
                 
                      
                                                                                     
                                                               
                                                                                           
                                            
                                                        
                                                                                     
                       
                     
                                          
                 
                                   
                 
                                                           
                     
                                   
                              
              
                                                                    
                                       
                 
                                                                                            
                       
                                               
                                                                                          
                                                        
                                                                                            
                                       
                                                  
                      

                                                                            
                                 
                
                                                     
                                 
           
                
                             

                                                                                  
                                                          
            
                                 
           
                   
        

                                                                               
                           
            
            

                                               
                                                    
            
                                                     

end Patt

end Pseudorandom
