/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import QuadraticCarleson.Definitions

/-!
# Elementary phase and Bohr-set lemmas

These are the first checked ingredients for Section 3 of the paper.
-/

open MeasureTheory Set

namespace QuadraticCarleson

@[simp]
theorem norm_phase (s : ℝ) : ‖phase s‖ = 1 := by
  simpa [phase] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * s)

                                                                     
                                             
         
           
      

                                                        
                
                                                                            

                                                             
                
                                                      
                                   
                                                

       
                                                                                 
                                         

                                                         
                                                                      
                                                                    

                                            
                                                   
            
            

                                                                                 
              
                                  
                                                                                     
                      

end QuadraticCarleson
