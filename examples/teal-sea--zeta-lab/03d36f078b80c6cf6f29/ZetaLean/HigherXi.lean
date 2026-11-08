/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib

/-!
# Kernel-checked algebra for the `URMS2-051` witness

This file formalizes the closed algebraic obligations in
`hunts/higher_xi/URMS2-051.md`:

* the rational parameter witness at bandwidth `51/100` and all of its strict
  margins;
* the logarithmic nearest-neighbour spacing bound used for frequencies
  `log n`;
* the integer multiplicity inequality behind the simple-zero lower bound;
* positivity of the exact rational downstream output.

It deliberately does **not** state `URMS2-051`.  The analytic Montgomery--
Vaughan mean-value estimate, RAMS2 cluster asymptotic, height-freezing estimate,
and contour transfer are not yet formalized in this project.  Keeping those
inputs out of the statement prevents the kernel-checked arithmetic below from
being mistaken for the analytic theorem.
-/

namespace ZetaLean.HigherXi

/-! ## The exact bandwidth witness -/

                         
                      
                        
                          

                                                            
                  

                                                      
                         

                                                     
                         

                                                                              
                                  

                                                                           
                                  

                                                       
                  

                                                       
                  

                                                                                 
                           

                                                                          
                           

                                                                    
                         

                                                                   
                         

                                             

                                                                    

                                                             
                                                                            
  
                                                               
                                                           
                                                                                   
                                                  
                                                               
                                                 
                                               
                   
            
      

                                                                  
                                                           
                                                   
                                                    
                                                         
                                                               
                                                   
                                                                  
                              
                                                                     
                  

                                                                             
                                                              
                                                   
      
                                                
                                       
                                                                

                                                           

open Complex Finset

/-- A unit Fourier atom with real frequency `lambda`. -/
noncomputable def fourierAtom (lambda t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (t * lambda))

                                                                          
                                    
      

                                         
                                                                        
                                                   
         
                            

                                           
                                                                               
                                                               
         
           
      

                                                                         
                                                                          
                         
                                                                
                                               
                                         

                                                                              
                                                               
                                          
                                                      
                                          
                       
                                                                             
                                                                     
                     
                            
            
                     
                            
            
      
                                                     
                                          
                                 
                                                                         
                                   
                                                 
                          
             
          

                                                                
noncomputable def sharpBlockKernel (U theta : ℝ) : ℂ :=
  ∫ t in U..2 * U, fourierAtom theta t

theorem sharpBlockKernel_zero (U : ℝ) : sharpBlockKernel U 0 = U := by
  simp [sharpBlockKernel, fourierAtom]
  ring

theorem sharpBlockKernel_of_ne_zero (U theta : ℝ) (htheta : theta ≠ 0) :
    sharpBlockKernel U theta =
      (Complex.exp ((-Complex.I * theta) * (2 * U)) -
        Complex.exp ((-Complex.I * theta) * U)) / (-Complex.I * theta) := by
  have hc : (-Complex.I * (theta : ℂ)) ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (ofReal_ne_zero.mpr htheta)
  unfold sharpBlockKernel fourierAtom
  rw [show (fun t : ℝ ↦ Complex.exp (-Complex.I * (t * theta))) =
      fun t : ℝ ↦ Complex.exp ((-Complex.I * theta) * t) by
    funext t
    congr 1
    ring]
  convert integral_exp_mul_complex (a := U) (b := 2 * U) hc using 1 <;>
    push_cast <;> ring

                                                                           
                                                                             
                                                                         
                                          
                     
                                                          
                                             
                       
                                   
                                                        
                                        
                                           
                                          
                                                                                 
                                       
                      
            
                                          
                                                   
                                                                                 
                                       
                      
            
                                                                
                              
              
                                                                   
                                
                
                                              
         

                                    

                                                                      
                     
                                                      
                                                              
                    
            
            
                                
                                                              
                                                    
                                                     

                                                                           
                                                                          
                             
                                                     
                                                   
                                               
                                                                            

                                          

                                         
                              
                                                                                                                                                                                                                                                                                                                

                                         
                                
                                                                                                                                                                                                                                                                                                                  

                                                                           

                                                                   
                                  

                                                                 
                                                                             

                                                                                  
                                                                             

                                                                                  
                                                                             

end ZetaLean.HigherXi
