import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian

/-!
# Elementary probability tools for Erdős Problem 625

This module gives formally proved versions of the elementary probability
inequalities invoked in Section 1 of the manuscript.  It uses `Measure.real`
for real-valued probabilities, Bochner integrals for real expectations, and
Lebesgue integrals for the extended-nonnegative Paley--Zygmund statement.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Erdos625

section Markov

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

                                                                          
                                             
                                                       
                          
                                                    
                     
                        
                                                          

end Markov

section PaleyZygmund

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The Cauchy--Schwarz estimate underlying the zero-threshold
Paley--Zygmund inequality. -/
theorem lintegral_sq_le_measure_support_mul_lintegral_sq
    {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) :
    (∫⁻ ω, Z ω ∂mu) ^ 2 ≤
      mu (Function.support Z) * (∫⁻ ω, (Z ω) ^ 2 ∂mu) := by
  let I : Omega → ℝ≥0∞ := (Function.support Z).indicator (fun _ ↦ 1)
  have hI : Measurable I :=
    measurable_const.indicator (measurableSet_support hZ)
  have hHolder :
      (∫⁻ ω, (I * Z) ω ∂mu) ≤
        (∫⁻ ω, I ω ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, Z ω ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
    apply ENNReal.lintegral_mul_le_Lp_mul_Lq mu
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      hI.aemeasurable hZ.aemeasurable
  have hIZ : I * Z = Z := by
    funext ω
    by_cases hω : Z ω = 0 <;> simp [I, Function.support, hω]
  have hI_sq : (fun ω ↦ I ω ^ (2 : ℝ)) = I := by
    funext ω
    by_cases hω : Z ω = 0 <;> simp [I, Function.support, hω]
  have hI_int : (∫⁻ ω, I ω ∂mu) = mu (Function.support Z) := by
    simp [I, measurableSet_support hZ]
  have hHolder' :
      (∫⁻ ω, Z ω ∂mu) ≤
        (mu (Function.support Z)) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, Z ω ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
    rw [hIZ, hI_sq, hI_int] at hHolder
    exact hHolder
  calc
    (∫⁻ ω, Z ω ∂mu) ^ 2 ≤
        ((mu (Function.support Z)) ^ (1 / (2 : ℝ)) *
          (∫⁻ ω, Z ω ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ))) ^ 2 :=
      ENNReal.pow_le_pow_left hHolder'
    _ = mu (Function.support Z) * (∫⁻ ω, (Z ω) ^ 2 ∂mu) := by
      rw [mul_pow]
      simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

/-- Zero-threshold Paley--Zygmund inequality for a measurable nonnegative
random variable.  The extended-real formulation handles zero or infinite
second moment without adding side conditions. -/
theorem paleyZygmund_zero_lintegral {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) :
    (∫⁻ ω, Z ω ∂mu) ^ 2 / (∫⁻ ω, (Z ω) ^ 2 ∂mu) ≤
      mu (Function.support Z) := by
  let first := ∫⁻ ω, Z ω ∂mu
  let second := ∫⁻ ω, (Z ω) ^ 2 ∂mu
  have hCS : first ^ 2 ≤ mu (Function.support Z) * second := by
    simpa [first, second] using
      (lintegral_sq_le_measure_support_mul_lintegral_sq (mu := mu) hZ)
  by_cases hsecond_zero : second = 0
  · have hfirst_sq : first ^ 2 = 0 := by
      apply le_antisymm
      · simpa [hsecond_zero] using hCS
      · exact bot_le
    simp [first, second, hsecond_zero, hfirst_sq]
  by_cases hsecond_top : second = ∞
  · simp [second, hsecond_top]
  · apply (ENNReal.div_le_iff_le_mul (Or.inl hsecond_zero) (Or.inl hsecond_top)).2
    simpa [mul_comm] using hCS

/-- Event-notation form of `paleyZygmund_zero_lintegral`, matching (1.5). -/
theorem paleyZygmund_zero {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) :
    (∫⁻ ω, Z ω ∂mu) ^ 2 / (∫⁻ ω, (Z ω) ^ 2 ∂mu) ≤
      mu {ω | 0 < Z ω} := by
  simpa [Function.support, pos_iff_ne_zero] using
    (paleyZygmund_zero_lintegral (mu := mu) hZ)

end PaleyZygmund

section SubGaussianTails

open ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

                                                                      
                                                                      
                                                                    
                                 
                                                       
                                                          
                                                                   
                                 
                                          
         
                 
             
      
                                              
                                                         
                              
                                                                       
            
                                 
                                           
                                                  

                                                                          
                                                                              
                                                                         
                                                                                 
                                                                  
                                                              
                          
                             
                                               
      
                             
                                                                    
                                 
                                                 
                      
                                                      
                                      
                 
                                                       
            
                    

end SubGaussianTails

section BinomialTail

open ProbabilityTheory

                                                                        
                                                                                  
            
                                                                   
                                                                
                                                               
              
                            
            
                                                           
                                   
                                
           
      

                                                                    
                                                                     
                                                       
                                                         
                               
                                                         
                                
                                                  
                        
                                                
                                                         
                                  
                                             
                                                                     
                         
      
                                                         
                               
                                                   
                                                                                     
                                            
                                                           
                                 
                                                                  
                                                                   
                             
                   
                               
                   
                                                       
                                                     
                               
               
            
                          

                                                                           
                                 
                                                                      
                                                                   
                                   
                                       
            
                                                                      
                                                               
                                               
                             
                           
          

                                                                         
                                                 
                                                  
                                                         
                               
                                    
      
                                                         
                               
                                                      
                                               
                                   
                                                                
                                      
                             
             
          

end BinomialTail

end Erdos625
