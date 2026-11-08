/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorIBP
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Bridges between `iteratedFDeriv`, `dirDeriv` and reflection

* `iteratedFDeriv_const_eq_iterate`: `iteratedFDeriv ℝ n f w (fun _ => d) = (D_d^n f) w`;
* `iterate_dirDeriv_comp_sub`: `D_d^n (y ↦ c f(z - y)) = (-1)^n c (D_d^n f)(z - ·)`.
-/

public section

open scoped ContDiff

namespace RegularityStructures

                                                                                      
                                  
                                                                             
                  
                                                      
                
                                           
            
                                                            
                                                                                             
                                                                    
                                     
       

                                                                                                 
                                                                          
          
                                                         
                                                                                      
                                                                          
                                                            
                   
                 

                                                                                              
                                                                               
          
                                                                   
                 

                                                                  
                                                        
                                                 
                                                                  
                  
                                       
                
                
                                                                                              
                                                                                              
                                                         
              
          
                                                                          
                                  
            
        

end RegularityStructures

end
