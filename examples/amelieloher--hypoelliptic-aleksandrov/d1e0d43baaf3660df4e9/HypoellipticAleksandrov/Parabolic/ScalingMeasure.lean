module

public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measure scaling for parabolic affine maps

This module proves the determinant, Haar-measure, and restricted `L^(d + 1)`
change-of-variables formulas for the affine map which multiplies time by
`r^2` and every velocity coordinate by `r`.  The results are stated for the
literal product Lebesgue measure on `TimeVelocity d`; no density-to-point or
higher-level parabolic estimate is imported here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

                                                            
                                                                        
                                                                         
                     
                         
     

                                                                      
                                             
                                                                    
                                         
                                                        
                                                               
                                                                            
                              
                     
                
         
       

                                                          
                                                                                
                                                                     
               
                
                                       
                                                       
                                             
            
         
                                                        
                                                           
                             
            

                                                                       
                                                                         
                                   
                                                    
                                                                         
                                             

                                                                        
                                                                               
                  
                                                    
                                                       

                                                                          
                                                                    
                               
                          
                          

                                                              
                                       
                                                                          
          
     

                                                                             
                                                 
                                                                            
                  
                                                                               
                                                     
                                                                 
                                                                           
                                                                                      
                                                   
                                                  
                
                                                                                    
                        
                      
                                                                             
                                                              
                                                            
                                       
                                                                
      
                                                                               
                                                           
                                                        
                                                                
                                                 
         
                                                                              
                  
                                                                            
                                                                  
                        
                                                             
                                                        

                                                                             
                             
                                                                         
                                                     
                                                                        
                                                   
                                    
      
                                                                        
                                                                                   
                                                                  
                                             
                                                   
                                                     
                                                                         
                                  

                                                                              
                                                     
                                                                                            
                                                             
                                            
                                                                                    
                                                      
      
                                                               
                                             
                                                                                              
                    
                                                               
                                         
                                                                   
                                            

                                                                           
                                                                        
                                                                         
                                                                              
                        
                                                           
                
                                           
                                             
                                                                   
                                                                    
                                     
                                                  
                       
                                                                     
                                                                                   
                                                          
                                     
                                            
                                                           
                                                                                 
                                                              
                                       

private theorem parabolicExponent_toReal (d : ℕ) :
    (parabolicExponent d).toReal = (d : ℝ) + 1 := by
  unfold parabolicExponent
  have hcast : (d : ℝ≥0∞) + 1 = ((d + 1 : ℕ) : ℝ≥0∞) := by
    norm_num
  rw [hcast, ENNReal.toReal_natCast]
  norm_num

                                                                            
                                                     
                                         
                                            
                                               
                            
                                                
         
           
                 
      

                                                                               
                                                                             
                                        
                                                                            
                                                                      
                       
                                                           
                                     
                                                                  
                                                           
                                            
                          
      
                         
                                                                   
                         
                                                     
                                              
                                                                              
                                                                               
                                       
                                                                              
                                                                                  
                                                                 
                                               
                                                                     

end HypoellipticAleksandrov.Parabolic
