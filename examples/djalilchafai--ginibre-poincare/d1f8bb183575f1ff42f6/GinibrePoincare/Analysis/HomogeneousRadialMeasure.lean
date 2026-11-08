module

public import GinibrePoincare.Analysis.MeasureTransport
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

/-! # Radial laws of homogeneous measures

A homogeneous measure of degree `2*k` and a nonnegative quadratic homogeneous
radius have a radial pushforward proportional to `r^(k-1) dr` on `(0,∞)`.
This formulation uses sublevel-set scaling and does not require spherical
coordinates or a particular choice of norm.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise

namespace GinibrePoincare
noncomputable section

                                                                            
                     
                                    
                                                        
                                                              
                                                
                                              
                                                                           
                                      
                               
                                                                               
                   
                               
                              
                                                      
                                                       
                                                 
                                                    
                                       
                                                                           
                                                                    
                                                         
                         
                                                              
                                                                            
                                         
                                                                            
                                           
                                        
                                                            
              
                       
                                              
                                                           
                                   
         
               
              
                                                      
                         
                              
                                        
                                                     
                                                                 
          

                                                                               
                                       
                                                         
                                                   
                                        
                                                                 
          
                                                                                   
                                        

                                                                    
def radialPowerMeasure (k : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun r => ENNReal.ofReal (r ^ (k - 1)))

instance (k : ℕ) : SigmaFinite (radialPowerMeasure k) := by
  unfold radialPowerMeasure
  infer_instance

                                                
                                                             
                                  
                                                                 
                           
                                            
                                                
                     
                  
                                                                      
             
                                                                                                                
                                                             
                                                   
                                              
                                                                          
                                                                  
                                
                  
                                             
           
                                                                                          
              
                                                     
                                                             

                                                                              
                                          
                                         
                                                                 
                                                   
                                                   
                                                             
                                            
                                                     
                               
                                     
                                                                         
                          
                                          
                                                           
           
                                               
                       
                                                       
                                                          
                                                                 
             
                   
                  
                                              
                                              
                                                         
                                    
                                                               
                                    
                             
                                        
                                
                                               
                                           
             
                                                  
                          
               
                                                       
               
                                                              
                                                                     
                        
                     
                                                                  
                                         
               
                                                                           
                                                           
                                                           
                                                   
           
             
             
                                                            
                               
                                                  
                                                           
           
                                                              
                       
                                            
                                                    
                                                                
                                                           
                         
          
                                                                                   
                                                                                       
               
                               
                 
                                                                     
                 
                                                                                                       
                                                                                    
                       
                  
                        
                        

                                                                            
                                  
                                                               
                                                                                  
                                                                                          
                                                
                                                                
                                                          
                                                      
                                              
                                                                          
                            
                                                                
                     
                                                                                       
                                                   
                                                                               
           
                                                      
                                               
                                                           
              
                                                              
                                                      

                                                                    
                                                                          
                                      
                                   
                                 
                                                                                           
                                                                                      
                                                    
                                                                           
                                                                                            
                                                                  
                                   
                                                                       
                       

end
end GinibrePoincare
