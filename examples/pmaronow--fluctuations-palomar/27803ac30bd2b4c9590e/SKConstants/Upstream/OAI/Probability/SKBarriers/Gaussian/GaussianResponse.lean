module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/GaussianResponse.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Scalar.GrowthOperations

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

theorem HasExpGrowth.integrable_tilted_fiberGaussian {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) (V : ParameterSpace n → ℝ) (hV : BoundedDerivs V)
    {g : ParameterSpace n → F} (hg : HasExpGrowth g) (hc : Continuous g) (x : ℝ) :
    Integrable g ((fiberGaussian n x).tilted V) := by
  have he : HasExpGrowth (fun z => Real.exp (V z)) := by
    simpa only [one_mul] using (hV.exp_growths 1).1
  have hce := Real.continuous_exp.comp hV.1.continuous
  rw [integrable_tilted_iff (he.integrable_fiberGaussian n hce x)]
  exact (he.smul hg).integrable_fiberGaussian n (hce.smul hc) x

                                                           
                                                                                
                                                       
                                                  
                                                          
                                                                                             

                                                                           
                                                                                              
                                   
                                                        
                                                   
                                                                                  

section Directional
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

                                                                         

                                                                                
                                             
                                                                   

                                                                                
                                                                                 
                                                                                                            
                                   
                                                 
                                                             

                                                                                             
                                                                                                    
                                    
             
                                                           
                                                                 
           
                                        
                                                                               
           
        
                                            
                                                                                    
                                                   
                                                        
                                                                                 
                      
end Directional

                                                                                               
                                                                                    
                                                   
                                                                                                
                                                  

                                                                          
                                                  
                                                                                    
                                                         
                                                          
                                                      
                                                                                  
                           
                              

                                                                           
                                                    
                                                                            
                                                                                       
                                                      
                                                                
                                                                     
                                                                        
                                                                                 
                                                                                           
                                                          
                                                               
                                                                               
                                             
                                                                  
                                                                                
                                             
                                                                           
                                                               
                                                          
                                                        
                                                                                                   
                                      
                         
                                      
                          
                                                                                          
                                                               
                                                 
                                                          
                                                             
                             
           
            
                              
        
              
                                                                                                
                                                                                           
                           
                
      

@[simp]
theorem coordinateProjection_coordinateAxis (n : ℕ) (i j : Fin n) :
    coordinateProjection n i (coordinateAxis n j) = if i=j then 1 else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [coordinateProjection,coordinateAxis]
      · simp [coordinateProjection,coordinateAxis,(Fin.castSucc_ne_last j).symm]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [coordinateProjection,coordinateAxis]
      · simpa [coordinateProjection,coordinateAxis] using ih i j

                                                                       
                                                                                  
         
                                                                      
                      
         
                         
                          
                                                              

                                                                           
                                                    
                                                          
                                                    
                                                                 
                                                      
                                                                
                                                                                 
                                                                                           
                                                          
                                                               
                                                                               
                                             
                                                                                
                                                                                                      
                                                       
           
                                                                   
                                                                  
                                                                                   
                                   
                                             
                                                                           
                                                                    
                                                                          
                                         
                                                                                   
                                                        
                                                                                        
                                                                                             
                             
                                                       
              
                                                            
                                                                                             
                                            
                                                                             
                                                                  
                                                    
                                                                
               
                                      
                                  
                                                                             
                                                                         
                           
           
                                                         
                                                       
              
      

end SK.Analytic

end
end
end
end
end
end
end

end SKConstantsOAI
