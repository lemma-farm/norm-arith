module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Hierarchy/CascadeRecursion.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.GaussianAverage

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
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

@[reducible] def CascadeSpace (E : Type) : ℕ → Type
  | 0 => E
  | n+1 => CascadeSpace E n × ℝ

instance cascadeNormedGroup (E : Type) [NormedAddCommGroup E] :
    (n : ℕ) → NormedAddCommGroup (CascadeSpace E n)
  | 0 => inferInstanceAs (NormedAddCommGroup E)
  | n+1 => letI := cascadeNormedGroup E n
    inferInstanceAs (NormedAddCommGroup (CascadeSpace E n × ℝ))

instance cascadeNormedSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (n : ℕ) → NormedSpace ℝ (CascadeSpace E n)
  | 0 => inferInstanceAs (NormedSpace ℝ E)
  | n+1 => letI := cascadeNormedSpace E n
    inferInstanceAs (NormedSpace ℝ (CascadeSpace E n × ℝ))

section Cascade
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

                                                
            
                                

                                                                            
              
                                                                                          

                                                                    
                                  
                
                                                                                          
                                            

                                                             
                                                                                                   
                  
                    
                                                                       

                                                                
                                                                                
                                                                    
                                                                                 
                  
                         
                
                                                            
                                                                                             

                                                        
                                                                 
                                          
                                                                           
                  
               
                
                                                                         
                                          
       

                                                            
                                                                                
                                                                              
                                                                           
                                
                                                          
                                                               
                                                                            
                                                                          
                                                                              
                                                             
                                     
           
                    
                                                               
                
                           
                              
                                   
                                                                                     
                                                                                     
                                     
                                                      
                                                                            
                                                                            
             
                                                                                       
                                                              
                                                                                             
                                                                                 
                                                                           

end Cascade
end SK.Analytic

end
end
end
end
end
end
end

end SKConstantsOAI
