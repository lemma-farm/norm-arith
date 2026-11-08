module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Calculus/MarginalDerivatives.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.SpinGlass.Basic
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.GaussianDomination
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Scalar.RawDerivatives

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
section MarginalDerivatives
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def leftRestrict : ((E × ℝ) →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip (ContinuousLinearMap.inl ℝ E ℝ)

theorem leftRestrict_apply_bound (A : (E × ℝ) →L[ℝ] F) : ‖leftRestrict A‖ ≤ ‖A‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ E ℝ) (norm_nonneg A)).trans_eq (mul_one _))

                                                                      
                                                         
                                                                     

theorem leftRestrict_hasFDerivAt (f : E × ℝ → F) (hd : Differentiable ℝ f) (x : E) (y : ℝ) :
    HasFDerivAt (fun z => f (z,y)) (leftRestrict (fderiv ℝ f (x,y))) x := by
  exact (hd (x,y)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))

                                                                      
                                                                     
                                                          
                                                                  
                                                        
                                                                                        
                             
                                                                            

                                                                              
                                                                     
                                                            
                                                     
                                             
                                                
                     
                                                             
                                                                                                  
                                                                                                        
                                             

end MarginalDerivatives
end SK.Analytic

end
end
end
end
end
end

end SKConstantsOAI
