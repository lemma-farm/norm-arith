module

                                     
public import SharpWasserstein.SynchronousStability
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

/-! Actual existence of continuous-forcing integral solutions on every finite
horizon for globally bounded, globally Lipschitz drifts. Picard--Lindelöf is
applied to the translated ODE, so no derivative of the forcing is assumed. -/

noncomputable section
open Set MeasureTheory Metric
open scoped Interval NNReal

namespace SharpWasserstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure FiniteAdditiveTrajectory (v : ℝ → E → E) (w : ℝ → E) (x₀ : E)
    (T : ℝ) (X : ℝ → E) : Prop where
  continuous : ContinuousOn X (Icc 0 T)
  driftContinuous : ContinuousOn (fun t => v t (X t)) (Icc 0 T)
  equation : ∀ t ∈ Icc 0 T, X t = x₀ + (∫ s in (0 : ℝ)..t, v s (X s)) + w t

                                                                                   
                                       
                     
                                           
                                                              
                                 
                                                                       
                                                  
                                               
                                                      
                                                                         
                                                                 
                                              
                           
               
                                         
                                        
               
                                                                              
               
                                                                          
                   
                              
                                                            
                           
                                                                        
                                                                         
                                                           
                                                     
                                                                         
              
                                                            
                                                                          
                                 
                                                   
                                                     
                                                    
                    
             
        
                                                               
            
               

                                                                       
                                                                        
                                               
                                          
                                         
                                                                              

                                                                              
                                                                      
                                                              
                                                
                                            

                                                                                 
                                                                         
                                                    
                                                                  
                                                                       
                                                                 
                                             
                                                                          
                                                                
                                                         
                                                                         
              
                                              
           
                                         
              
                                                       
                                                
                                          
                                                                        
                                                                     
                                                                       
                                                                                                                   
                  
                                

                                                                               
                                                                               
                                                    
                                                                  
                                                                     
                                                                         
                                       
                      
                        
                                                                            
                                                    

                                                                          
                                                            
                                                                   
                                               
                                              
                                                                   
                                                          
                                     
                                                
                                              
        
                                                          
                                                                      
                                                                
                                             
              
                                                        
                                                     
                                                   
         
                                                
        
                          
                                                               
              
                                             
                                                               
                                                               
                                                                 
                                                  

end SharpWasserstein
