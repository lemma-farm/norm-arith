module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/FiberGaussian.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Hierarchy.HierarchyPenalty
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.GaussianStepCalculus

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
namespace SK.Analytic

def fiberGaussian : (n : ℕ) → ℝ → Measure (ParameterSpace n)
  | 0, x => Measure.dirac x
  | n+1, x => (fiberGaussian n x).prod (gaussianReal 0 1)

instance fiberGaussian_probability : (n : ℕ) → (x : ℝ) → IsProbabilityMeasure (fiberGaussian n x)
  | 0, x => inferInstanceAs (IsProbabilityMeasure (Measure.dirac x))
  | n+1, x => by
      let := fiberGaussian_probability n x
      exact inferInstanceAs (IsProbabilityMeasure ((fiberGaussian n x).prod (gaussianReal 0 1)))

                                                       
                                                       
                                         
                                     
                      

                                                              
                                                       
                                                
                  
                                  
                
                                               
                                                         
                                                                       
                                                             

                                                              
                                                               
                                                                
                                                                     
                  
           
               
                                                                
                              
                                              
                
                                                                               
                                                                                 
                                       
                                               
                                                                               
                                                           
                                                           
                                             
                                                                            
                                    
                                                                                
                                                                                            
                                
                                                                        
                                       
                                                                                  
                                                                               
                
                                                                                         
                                                                                                  
                                
                                    
                     
                                            
                  
               

                                                              
                                                                  

                                                                 
                                      
                             
            

                                                                                           
                                                      
                                                      

                                                                      
                                                                                           
                                             
                                                              
                   
                                                                                            
                 
      

                                                      
                                                      
                                                                
                  
                                                                                   
                
                                                                                        
                                                                                    
                                     
                                                       
            
                                                                                         
       

end SK.Analytic

end
end
end
end
end
end

end SKConstantsOAI
