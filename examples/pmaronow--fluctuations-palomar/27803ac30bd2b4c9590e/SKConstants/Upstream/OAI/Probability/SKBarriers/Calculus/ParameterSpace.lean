module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Calculus/ParameterSpace.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
                                                                                        

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

@[reducible] def ParameterSpace : ℕ → Type
  | 0 => ℝ
  | n+1 => ParameterSpace n × ℝ

instance parameterNormedGroup : (n : ℕ) → NormedAddCommGroup (ParameterSpace n)
  | 0 => inferInstanceAs (NormedAddCommGroup ℝ)
  | n+1 => letI := parameterNormedGroup n; inferInstanceAs (NormedAddCommGroup (ParameterSpace n × ℝ))

instance parameterNormedSpace : (n : ℕ) → NormedSpace ℝ (ParameterSpace n)
  | 0 => inferInstanceAs (NormedSpace ℝ ℝ)
  | n+1 => letI := parameterNormedSpace n; inferInstanceAs (NormedSpace ℝ (ParameterSpace n × ℝ))

instance parameterFiniteDimensional : (n : ℕ) → FiniteDimensional ℝ (ParameterSpace n)
  | 0 => inferInstanceAs (FiniteDimensional ℝ ℝ)
  | n+1 => letI := parameterFiniteDimensional n; inferInstanceAs (FiniteDimensional ℝ (ParameterSpace n × ℝ))

                                                     
             
                                            

                                                                              
                  
               
                
                                                                    
           
            

                                                                
                                  
                  
                           
                                                          

                                                                    
                   
                                                                 

                                                                      
                                              
                                                            
                             
                                          
                                                            
                  
           
                   
             
                              
                                                        
                
                                                                              
             
                                                                                       
                                   

end SK.Analytic

end
end
end
end
end

end SKConstantsOAI
