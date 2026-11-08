-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Integral-form linear ODEs

This file records the integral formulation used for linear equations with measurable
coefficients, together with the continuity and almost-everywhere derivative consequences of the
Lebesgue differentiation theorem.  The coefficient and forcing are deliberately abstract: the
file is reusable for finite-dimensional spaces and for other complete real normed spaces.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace AVenhance.Infra.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

                                                               
                                                              
                 

                                                                            
                                                                     
                                   
                                                          

                                                                                         
theorem continuousOn_intervalPrimitive {g : ℝ → E} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) :
    ContinuousOn (fun t => ∫ s in a..t, g s) (uIcc a b) := by
  exact intervalIntegral.continuousOn_primitive_interval' hg (by simp)

                                                                                             
                                                             
                     
                                            
                                
                                                          
                                                      
            
                           

                                                                                              
                                                                                 
                           
                                                                
                                                                        
                                       
                                                    
                  
                                                                              
                                                           
                                                                        
                                   
                                                                     
                                                                                                         
           
                                          
                                                                  
                                       
                         
                                                    
                                                                          
                                                        
                                                          
                                          
                                   
                                         
                                    
                                        
                                                       
                                                               
                                             
                                                                                   
                              
                     
                                                 
                                                                      
                                                                       
                                                  
                                     
                          
                                                                   
              
                                                                                   
                              
                       
                                                    
                                                                 

                                                                                              
                                                               
                                                        
                 
                                                
                                                               
                                              
               
                                                                                                 
                         
                                                                          
                                           
              
                      
                   
                  
                                
            
                                                        

                                                                                              
                                                                                
                      
                     
                 
                                                
                                                               
                               
                                              
                                               
                  
                                                                    
                                                                                   
                    
                                                                                   
             
                                                                  
                                
                                 
                                                                
                       
                           
                                                    
                                 
                                                      
        
                                   
                                                          
                                                           
                                       
                                         

end AVenhance.Infra.ODE
