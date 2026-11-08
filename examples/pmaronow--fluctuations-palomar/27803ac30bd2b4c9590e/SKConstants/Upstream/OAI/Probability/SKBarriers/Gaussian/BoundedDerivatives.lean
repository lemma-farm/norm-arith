module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/BoundedDerivatives.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Scalar.RawDerivatives
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.GaussianLogStep
                                                                                           
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.ExponentialDerivatives

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
section SmoothRecursion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def BoundedDerivs (f : E → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
    (∀ x, ‖fderiv ℝ f x‖ ≤ C) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ D)

theorem BoundedDerivs.const_mul {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) :
    BoundedDerivs (fun x => m*f x) := by
  obtain ⟨hf,C,D,hC,hD,hb,hbb⟩ := hf
  have hd := hf.differentiable (by norm_num)
  have he : fderiv ℝ (fun x => m*f x) = fun x => m • fderiv ℝ f x := by
    funext x
    exact ((hd x).hasFDerivAt.const_mul m).fderiv
  refine ⟨contDiff_const.mul hf, |m| * C, |m| * D,
    mul_nonneg (abs_nonneg _) hC, mul_nonneg (abs_nonneg _) hD, ?_, ?_⟩
  · intro x
    rw [he, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
  · intro x
    rw [he]
    change ‖fderiv ℝ (m • fderiv ℝ f) x‖ ≤ |m| * D
    rw [((hf.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) x).hasFDerivAt.const_smul m |>.fderiv]
    exact (ContinuousLinearMap.opNorm_smul_le _ _).trans (by
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbb x) (abs_nonneg _))

                                                                                  
                                                                           
                                    
                                                        
                              
                                                                                  
                                                         
                                                                    
                                                   

                                                                                                     
                                                    
                                     
                                                                                   
                            
         
                                                                                                    

                                                                               
                                                   
                                                         
                                                       
                                                                                 
                                                                                
                                                                     
                                                            
           
                            
                               
                                                               
                                                         
                                                                                  
                    
                                  
                 
                                   
                                                  
                                                                                       
                                           
                                           
                                                      
                                                             

end SmoothRecursion
end SK.Analytic

end
end
end
end
end
end

end SKConstantsOAI
