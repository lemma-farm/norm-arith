module

public import Mathlib
public import MarkovProcess.Lifetime.ExitTimeStopping

@[expose] public section




set_option autoImplicit false

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal BigOperators Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Input

/-- The finite-coordinate state space, with its usual product norm and volume. -/
abbrev State (d : ℕ) := Fin d → ℝ

                                                                                      
                                                                          
                                                    

                                                                        
                                                                   
                                                      

                                                                             
                                                                                 
                                                                      
                                               
                                                              
                                            

                                                                                           
                                                                               
                         
                                                                      
                                              
                                                             
                                                
                                                           
                                                            
                                                              
                                                     



structure BoundaryApproximation {d : ℕ} (U : Set (State d))
    (u : State d → ℝ) (Du : State d → State d) where
  memLp : MemLp u 2 (volume.restrict U)
  grad_memLp : ∀ i, MemLp (fun x => Du x i) 2 (volume.restrict U)
  approx : ℕ → State d → ℝ
  smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  compactSupport : ∀ n, HasCompactSupport (approx n)
  support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_fun : Tendsto
    (fun n => eLpNorm (fun x => approx n x - u x) 2 (volume.restrict U)) atTop (𝓝 0)
  tendsto_grad : ∀ i, Tendsto
    (fun n => eLpNorm (fun x => (fderiv ℝ (approx n) x) (Pi.single i 1) - Du x i)
      2 (volume.restrict U)) atTop (𝓝 0)

                                                                                      
                                                                      
                                                                         
                                                 
                                                               
                                                         
                                       
                                                 
                                                  
                                                 
                                                                             
                                                                        
                          
                                                                            
                                                         

                                                                                             
                                                                                              
                                                         
                                                               
                                                         
                                    
                                                      
                                                
                                                               
                                                                 
                                                                              
                                                                      
                                                                       
                         

                                                                          
                                                  
                                     
                                   
                                                                           

                                                                                   
                                                                                         
                                                                                      
                                       
                                                    
                                                       
                                                        
                                                                                   

end SubdiffusiveProcess.Probability.Diffusion.Input
