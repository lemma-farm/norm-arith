module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Scalar/RegularAlgebra.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.GaussianZeroMass

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
section RegularAlgebra
variable {E D : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem BoundedDerivs.add {f g : E → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g) :
    BoundedDerivs (fun x => f x+g x) := by
  obtain ⟨hf,C,D,hC,hD,hf₁,hf₂⟩ := hf
  obtain ⟨hg,A,B,hA,hB,hg₁,hg₂⟩ := hg
  have hd := hf.differentiable (by norm_num)
  have he := hg.differentiable (by norm_num)
  have heq : fderiv ℝ (fun x => f x+g x) = fun x => fderiv ℝ f x+fderiv ℝ g x := by
    funext x
    exact ((hd x).hasFDerivAt.add (he x).hasFDerivAt).fderiv
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hee := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  refine ⟨hf.add hg,C+A,D+B,add_nonneg hC hA,add_nonneg hD hB,?_,?_⟩
  · intro x
    rw [heq]
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add (hf₁ x) (hg₁ x))
  · intro x
    rw [heq, ((hdd x).hasFDerivAt.fun_add (hee x).hasFDerivAt).fderiv]
    exact (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add (hf₂ x) (hg₂ x))

                                                                                  
                                          
                                     
                                                                                   
                                                 
                            
                                                               
           
           
                                                                          
                                            
                                                                                   
                                                                              
            
                                                              
                                             
                                                                                                   
           
            
                                         
           
                                                        
                                                          
           
                                                           
                                                               
                                          
                                                                           
                         
        
                                                                                              
                           
              
                                                            
                                                              
                      

theorem RegularConvex.add {f g : E → ℝ} (hf : RegularConvex f) (hg : RegularConvex g) :
    RegularConvex (fun x => f x+g x) := ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem RegularConvex.const_mul {f : E → ℝ} (hf : RegularConvex f) {m : ℝ} (hm : 0 ≤ m) :
    RegularConvex (fun x => m*f x) := by
  refine ⟨hf.1.const_mul m, ?_⟩
  simpa only [smul_eq_mul] using hf.2.smul hm

                                                                                  
                                          
                             
                                         

end RegularAlgebra
end SK.Analytic

end
end
end
end
end
end

end SKConstantsOAI
