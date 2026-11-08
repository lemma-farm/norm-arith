module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsTaylor
import Mathlib.Tactic

/-!
# Gamma moments of the positive-axis expansion

This module evaluates the integral Taylor polynomial with the exact rising-factorial
coefficients of the source expansion.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

                                                                          
                                               
                                  
                                                  
                                 

                                                                      
                                               
                                                                          
                                                                             
                                            
                                                 
                                                          
                                                 
                  
                                             
                      
      

                                                                               
                                                 
                                                            
                  
                                                                   
                
                                     
                                                                                         
                      
          

                                                
theorem integral_gammaKernel (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a - 1)) =
      z ^ (-a) * Real.Gamma a := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hz
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow] at h
  simpa only [mul_comm] using h

                                                                                  
                                                                            
                                                                       
                                                              
                                                                                
                                                                             
                                                 
              
              
                                                             
                                          
        
                                   
                                                                                 
                                
                                                          
      

                                                                   
                                                                                
                                                                           
                          
                              
                                         
                                                                                
            
            
                                                           
                                        
      

                                                                                       
                                                                                       
                                                                                       
                          
                                                 
                                                                                       
                                                    
           
                                         
                            
           
      

                                                                                      
                                                                       
                                                              
                                                                                  
                                                                        
                                      
                                                         
                                                                               
                                           
                                                  
                                                                                      
                                                                     
                                                              
              
                                
               
          
                                
                                    
               
                                                                  
           
                                        
                            
           
                                                                  
                                              
      

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
