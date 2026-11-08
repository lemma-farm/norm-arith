module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measures and norms on time--velocity space

This module records the product Lebesgue normalization on time--velocity
space, identifies cylinders differing only by their terminal time slice, and
defines the exact `L^(d + 1)` norms used by the parabolic ABP estimate.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- Product Lebesgue volume is an additive Haar measure on time--velocity space. -/
instance timeVelocityVolumeIsAddHaar (d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (TimeVelocity d)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

                                                                                   
                                             
                                         
                                                                 
                                      

                                                                            
                                                                    
                                                                           
                             
      

                                                                              
                                                                            
                                                                   
                                                                              
                                     
                             
                                                               

                                                                                       
                                                                                  
                                                                           
                                                  
                                                                     

                                                                                    
                                                           
                                                          
                                                   
                                                        
                                                                   
                                                  

                                                                                    
                                                          
                                                       
                                                  
                                                       
                                                                  
                                                  

                                                                 
                                             

                                                                      
                                                               
                                        

                                                                              
                                                                                    
                                                                                          
                                                           
                               

                                                                             
                                                       
                                        
                                                     

                                                                                       
                                                                                  
                                                   
                                                       
                                                      
                                     
                                   

                                                                                      
                                                                 
                                                       
                                                     
                                                            
                           
                                              

                                                                             
                                                                
                                                       
                                                    
                                                           
                          
                                                        

end

end HypoellipticAleksandrov.Parabolic
