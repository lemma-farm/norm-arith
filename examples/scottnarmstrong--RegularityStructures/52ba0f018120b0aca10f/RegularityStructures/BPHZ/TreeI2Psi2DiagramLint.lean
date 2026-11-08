/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# Lower-integral bounds: a small calculus

`i2Psi2LintBound μ f M` says `∫⁻ ofReal (f a) ∂μ ≤ ofReal M`.  It is the form in which the
singular-integral estimates of the tree `I(Ψ²) Ψ²` ([Hai14, (10.39)-(10.42)]) are chained: it needs
no integrability bookkeeping, is monotone, additive, scales by constants, and passes through
Tonelli (`i2Psi2LintBound.of_prod_symm`) and products of independent factors.  The final
`abs_integral_le_of_i2Psi2LintBound` turns such a bound on `|f|` into integrability of `f` and a
bound on `|∫ f|`.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures

/-- `f` has lower integral at most `M`: `∫⁻ ofReal (f a) ∂μ ≤ ofReal M`. -/
def i2Psi2LintBound {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (M : ℝ) :
    Prop :=
  ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ENNReal.ofReal M

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem i2Psi2LintBound.mono_ae {f g : α → ℝ} {M M' : ℝ}
    (h : i2Psi2LintBound μ g M) (hfg : ∀ᵐ a ∂μ, f a ≤ g a) (hM : M ≤ M') :
    i2Psi2LintBound μ f M' := by
  unfold i2Psi2LintBound at *
  refine (lintegral_mono_ae ?_).trans (h.trans (ENNReal.ofReal_le_ofReal hM))
  filter_upwards [hfg] with a ha using ENNReal.ofReal_le_ofReal ha

                                                     
                                                                      
                             
                                                

theorem i2Psi2LintBound.add {f g : α → ℝ} {M N : ℝ} (hf : AEMeasurable f μ)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hfM : i2Psi2LintBound μ f M) (hgN : i2Psi2LintBound μ g N) :
    i2Psi2LintBound μ (fun a => f a + g a) (M + N) := by
  unfold i2Psi2LintBound at *
  have h1 : ∫⁻ a, ENNReal.ofReal (f a + g a) ∂μ =
      ∫⁻ a, ENNReal.ofReal (f a) ∂μ + ∫⁻ a, ENNReal.ofReal (g a) ∂μ := by
    rw [← lintegral_add_left' hf.ennreal_ofReal]
    exact lintegral_congr fun a => ENNReal.ofReal_add (hf0 a) (hg0 a)
  rw [h1, ENNReal.ofReal_add hM hN]
  exact add_le_add hfM hgN

                                                                                 
                                                                                      
                                                                        
                                                                 
                                                                  
                                                      
                                                                 
                                                                       

theorem i2Psi2LintBound.const_mul {f : α → ℝ} {M c : ℝ} (hc : 0 ≤ c)
    (h : i2Psi2LintBound μ f M) : i2Psi2LintBound μ (fun a => c * f a) (c * M) := by
  unfold i2Psi2LintBound at *
  have h1 : ∫⁻ a, ENNReal.ofReal (c * f a) ∂μ = ENNReal.ofReal c * ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun a => ENNReal.ofReal_mul hc
  rw [h1, ENNReal.ofReal_mul hc]
  exact mul_le_mul_right h _

variable {β : Type*} [MeasurableSpace β] {ν : Measure β}

                                                          
                                                                            
                                           
                                                               
                                                                       
                             
                                                             
                                           
                                        

                                                   
                                                                                          
                                                                                     
                                                                 
                                                                     
                             
                                                            
                                                                           
                                                                 
                                                               
                                
                           

                                                                                         
                                                              
                                                                                             
                                            
                             
                                       
                                                               
                                                               
             
                                                
                         
                                                                                        
                                                                       
                                                                                           
                                                                 
                                                         
                                                        
                                                      
                                                                                
                                     

end RegularityStructures

end
