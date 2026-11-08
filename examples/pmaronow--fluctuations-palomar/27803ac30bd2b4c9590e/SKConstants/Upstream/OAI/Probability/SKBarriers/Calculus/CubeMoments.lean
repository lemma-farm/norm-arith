module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Calculus/CubeMoments.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.CubeVariance
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.CubeMeasures

@[expose] public section

namespace SKConstantsOAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic
instance fiberNeZero : (n : ℕ) → (x : ℝ) → NeZero (fiberMeasure n x)
  | 0, x => inferInstanceAs (NeZero (Measure.dirac x))
  | n+1, x => by
    let := fiberNeZero n x
    refine ⟨Measure.measure_univ_ne_zero.mp ?_⟩
    change ((fiberMeasure n x).prod volume) univ ≠ 0
    rw [← univ_prod_univ, Measure.prod_prod]
    exact mul_ne_zero (NeZero.ne _) (NeZero.ne _)

                                                                          
                                         
                  
                            
                
              
                                                          

                                                                                      
                              
                  
                   
                
                                                     
                                          
                               
                                                 

                                                                               
                         
         
                                     
                                                         

                                                                                   
                                                    
                                                                
                                            
                                                                   
                 
                                                                                 
                                                                                            
                                                                                                 
                                                 
                    
          
                                                                                                                 

                                                             
                                                                    
                                                                  
                                       
                                                
                                                          
                                                                    
                                                                        
                                                                              
                                                   
                                                        
                                                                    
                                                          
                                                 
                                                                 
                                                                             
                                               
                                                                 
                                                                     
                                                                  
                                                      
                                        
                                                  
                                                       
                                                                          

end SK.Analytic

end
end
end
end
end

end SKConstantsOAI
