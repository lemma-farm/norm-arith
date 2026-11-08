module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/GaussianSecondStep.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.LogDerivatives
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
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section SecondStep
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

                                                                                   
                                                                              
                                                                       
            
                                                                              
         
                                                                                                                   

theorem BoundedDerivs.exp_growths {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) :
    HasExpGrowth (fun x => Real.exp (m*f x)) ∧
    HasExpGrowth (fderiv ℝ (fun x => Real.exp (m*f x))) ∧
    HasExpGrowth (fderiv ℝ (fderiv ℝ (fun x => Real.exp (m*f x)))) := by
  obtain ⟨hfd,C,D,hC,hD,hb,hbb⟩ := hf.const_mul m
  have hg : HasExpGrowth (fun x => Real.exp (m*f x)) := by
    simpa only [one_mul] using exp_mul_growth_of_fderiv_bound (fun x => m*f x)
      (hfd.differentiable (by norm_num)) C hC hb 1
  exact ⟨hg,fderiv_exp_growth _ (hfd.differentiable (by norm_num)) hg hC hb,
    fderiv_fderiv_exp_growth _ hfd hg hC hD hb hbb⟩

                                                                                 
                                  
                                              
                                                                
                                                                                        
                              
                                                             
                                                                                                     
                                                                                                 
                                                                       
                                                 
                                                                             
                                                                
            
                                                                                              
                                                               
                                         
                                                                
                                                                                            
                                                                                 

                                                                                        
                                              
                                                                                   
                                                                            
            
                                     
         
                                     
                                             
                                                                       
                                                                      

                                                                                          
                                                          
                                                                   
                                                                             
                                                   
                                                    
                                                                                                    
                          
                                                                
                                                             
                                                                                      

end SecondStep
end SK.Analytic

end
end
end
end
end
end
end

end SKConstantsOAI
