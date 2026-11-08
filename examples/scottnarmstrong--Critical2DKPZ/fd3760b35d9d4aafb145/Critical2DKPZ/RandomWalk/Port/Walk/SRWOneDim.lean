/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.SRW
public import Critical2DKPZ.RandomWalk.Port.Walk.OneDim

/-! # One-dimensional simple and lazy walk kernels

Two simple walk steps give a lazy step after dividing space by two; consequently
the simple walk kernel is bounded by `√2 / √(n+1)` at every site. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

/-- The `ℓ¹` norm of a one-dimensional site is the absolute value. -/
theorem graphNorm_one (a : ℤ) : graphNorm (![a] : Site 1) = a.natAbs := by
  simp [graphNorm]

                                                                         
                                             
                                             
                                 
           
                       
                              
                         
                
                
                
                     
                                                        
                
                
                                                                   
                    
             
                
                                                           
                                                                      
                                                      
                                                
                                                
                                                      
                                     
                  
          

                                                                            
                                             
                                                              
                                                 
                                   
            
                                                                       
                                 
                                                              
                                                 
                                         
                        
                                                     
                                 
                 
               
                                              
            
                                                     
                 
                                              
            
                      
            
              
              

                                                          
                                        
                                                                  
                                                 
                                   
            
                                                
                                                        
                                                                                             
                                        
                                 
               
             
              
            
                                       
            
                         
                                             
                                             
                                                                   
                                           
                                                                                     
                                          
                                                         
          
             
            


                                                          

                                                                                
                                                                                 
                                           
                                                      
                                                                         
         
                  
           
                   
                                 
                                 
                        
                                                                          
                                         
                                            
              
                
                   
                         
                                       
                
                                                                                       
                           
                                                             
                                                                                     
                                                                                           
                                                        
                                                                   
                 
            
                           
                                     
                  
                                                                                      
                             
                                                                                      
                                                       
                                                                                          
                                                          
                                                         
                   
              
                               
                                                            
                                                                       
                                                          
                                                                       
                                                                                          
                   
                       
              

end LatticeProb

end
