/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernelRegularity
public import RegularityStructures.Probability.SpaceTimeMeasure
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrability of the massive heat kernel

The nonnegative space-time kernel has mass one: the spatial mass is the Gaussian normalization and
the remaining time integral is the exponential integral on `(0, ∞)`.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures

theorem integrable_heatKernel_fixed {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernel t) := by
  rcases bounded_heatKernel ht with ⟨C, hC⟩
  refine Integrable.of_bound (continuous_heatKernel_fixed ht).aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hC x

                                                         
                                                            
      
                                                      
                                                        
                                                                           
                                                                  
                                                               

                                                                  

                                                                         
                                                                               
               
                                               
                                           

                                                                       
                                                                                     
            
                                            
                                                                      

                                     
                                                        
      
                                                  
                                                    
                                                                       
                                                
                                  
                                         
                                                                   

                                     
                                                                    
              
                                                                
                                                                                
                              
                                                                                   
                                     
                                                                    
            
      
                                                                          
                                                            
                              
                              
                         
                                                                      
            
                                                                       
                            
                                                                                 
                                 
                   
                                                  
                                             
                                    
                                                  
                                                                              
                                                       
                                        

                                                                         
                                                                
                                 
              
                                                                
                                                                    
                            
                            
                                                         
                                         
                          

                                                                                   
                                        
                                                          
                                                      
                                  
     

end RegularityStructures

end
