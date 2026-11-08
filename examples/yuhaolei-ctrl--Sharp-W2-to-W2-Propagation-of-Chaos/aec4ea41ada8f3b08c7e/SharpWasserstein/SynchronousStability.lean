module

                                     
public import SharpWasserstein.DriftBounds
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Pathwise stability for genuine integral equations with a common additive
forcing. The forcing cancels; it is never differentiated. This applies to
continuous Brownian sample paths once the integral solution is constructed. -/

noncomputable section
open Set MeasureTheory
open scoped Interval NNReal

namespace SharpWasserstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure AdditiveTrajectory (v : ℝ → E → E) (w : ℝ → E) (x₀ : E)
    (X : ℝ → E) : Prop where
  continuous : ContinuousOn X (Ici 0)
  driftContinuous : ContinuousOn (fun t => v t (X t)) (Ici 0)
  equation : ∀ t, 0 ≤ t → X t = x₀ + (∫ s in (0 : ℝ)..t, v s (X s)) + w t

                                                                
                                              
                                               
                                                                         
                          
                                                                          
                                                                  
                                                                              
                                                                  
                                                                              
                                                                                
      

variable [CompleteSpace E]

                                                                                                   
                                                
                                               
                                                                         
                          
                                                                                 
                                                                                 
                                                                                       
                                                                   
                                                                            
              
                                                        
           
                                         
              
                                                                                   
                                   
                                                                          
                                                                     
                                                                                                                          
                                                                             
                  
                                                                              

                                                                         
                                    
                                                         
                                             
                                                                         
                          
                                                          
                                     
                                                                            
                                                          
                                                              
                                                                
                                          
                                                                   
                          
                                                               
              
                                                                                 
                                                              
                                                               
                                                 

                                                                  
                                 
                                                      
                                             
                                                                           
                                
            
                                                    
                                                                                   

end SharpWasserstein
