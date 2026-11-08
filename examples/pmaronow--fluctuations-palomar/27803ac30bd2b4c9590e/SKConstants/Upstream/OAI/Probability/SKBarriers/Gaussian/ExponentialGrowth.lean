module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/ExponentialGrowth.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.GaussianDomination

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
section TwiceDifferentiable
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

                         
                                                      
                                                             
                                                                   
                                                                         
                                                             
                                                                 
                                                                
                                                                          
                                                      
                                                             
                                                                    
                                                                   
                                                    
                                                                     

end TwiceDifferentiable

section GrowthAlgebra
variable {E F G : Type} [Norm E] [Norm F] [Norm G]

theorem HasExpGrowth.congr_bound {f : E → F} (hf : HasExpGrowth f)
    {g : E → G} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ z, ‖g z‖ ≤ K*‖f z‖) : HasExpGrowth g := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  refine ⟨K*C,M,mul_nonneg hK hC,hM,?_⟩
  intro z
  exact (hg z).trans ((mul_le_mul_of_nonneg_left (hf z) hK).trans_eq (mul_assoc _ _ _).symm)

theorem HasExpGrowth.of_bounded {f : E → F} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z, ‖f z‖ ≤ C) : HasExpGrowth f := by
  refine ⟨C,0,hC,le_rfl,?_⟩
  simpa only [zero_mul, Real.exp_zero, mul_one] using hf

                                                                                   
                                       
                             
                       
         
                                                                

end GrowthAlgebra
end SK.Analytic

end
end
end
end
end
end

end SKConstantsOAI
