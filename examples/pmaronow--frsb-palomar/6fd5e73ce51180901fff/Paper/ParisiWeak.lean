module

public import Paper.ParisiMildDerivative
public import Paper.ParisiTestRegularity
public import Paper.HeatAdjoint
public import Mathlib
@[expose] public section

/-!
# Distributional spatial derivatives of the constructed Parisi potential

The weak gradient is verified against actual smooth compactly supported
tests.  Spatial integration by parts and absolute integrability on the
time-space product discharge the distributional identity.
-/

open Set MeasureTheory ProbabilityTheory
open scoped Topology ContDiff

namespace Paper

instance : IsLocallyFiniteMeasure parisiSpaceTime := by
  unfold parisiSpaceTime
  infer_instance

theorem hasCompactSupport_spatial_section (φ : ℝ × ℝ → ℝ)
    (hc : HasCompactSupport φ) (t : ℝ) : HasCompactSupport (fun x : ℝ => φ (t, x)) := by
  have hk : IsCompact (Prod.snd '' tsupport φ) := hc.image continuous_snd
  apply hk.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hk.isClosed
  intro x hx
  exact ⟨(t, x), subset_closure hx, rfl⟩

                                                                      
                                                                  
                                                            
                                           
                                       
                                                                                   
                 
                                                                     
                                                                                       
                                                                          
                                                            
                                                              
                                                                      
                        
                                   
                                                                                     
                              
                                                              
                                                                        
                                                                        
                                                                                   
                                                                                    
                                                      
                                                                      
                                                                         
                                                               
                                                             
                                                              
                                                             
                                                              
                                                            
                                                      
                                                                  
                                                                       
               
                                 
      

end Paper
