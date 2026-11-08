/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Moments of centred real Gaussian variables

For `v ≥ 0` the centred real Gaussian law `gaussianReal 0 v` has

* `∫ x² = v`, `∫ x⁴ = 3 v²` and `∫ x⁶ = 15 v³`;
* `∫ x^(2k+1) = 0`.

The even moments are the derivatives at `0` of the moment generating function
`t ↦ exp (v t² / 2)` (`ProbabilityTheory.iteratedDeriv_mgf_zero`). Each derivative is
`P_k(t) exp (v t² / 2)` for an explicit polynomial `P_k`, with `P_{k+1} = P_k' + v t P_k`.

The second part transfers these identities to a real random variable `Y` with a Gaussian law and
mean zero: `E[Y⁴] = 3 E[Y²]²` and `E[Y⁶] = 15 E[Y²]³`. These are the scalar inputs of the
Isserlis–Wick formulas in `RegularityStructures.Probability.Isserlis`.
-/

public section

open MeasureTheory ProbabilityTheory Real Polynomial
open scoped NNReal

namespace RegularityStructures

/-! ### Derivatives of `exp (v t² / 2)` -/

section GaussExp

variable (v : ℝ)

                                                                                       
                                                                                    
                                                    
                                                           
                                                                                               
                                                                
                        
             
        
                           
      

                                                                                           
                                                  
                                                                           
                                                                       
                                                                       
                                                                            
                             
          
                                                                

                                                                         
                                   
                                                     
                                                               
                                                       
                                                                                           
                                                       
                                                                                         
                                    
                                                             
                                                               
        
                                                                                      
                                                                                   
                            
                                                    
                                                                                          
                                                    
                                                                    
                                             
                                                    
                                                                          
                                             
                                                    
                                                                                               
                                             
                     
           
            
        
           
            
        
           
            
        

end GaussExp

/-! ### Moments of `gaussianReal 0 v` -/

section GaussianReal

variable (v : ℝ≥0)

/-- Every power of the identity is integrable for a real Gaussian law. -/
theorem integrable_pow_gaussianReal (μ : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal μ v) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) k

                                                                                             
                                                            
                                                                                          
                                                                                            
                                   
                                     
        
      

                                                                         
                                                                                  
      

                                                                                             
                                                                                    
      

end GaussianReal

/-! ### Centred real Gaussian random variables -/

end RegularityStructures

namespace ProbabilityTheory.HasGaussianLaw

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}

                                                                                           
                                                                         
                            
                                                       
                                 

                                                                  
theorem integrable_pow (hY : HasGaussianLaw Y P) (k : ℕ) :
    Integrable (fun ω => Y ω ^ k) P := by
  have h := integrable_pow_gaussianReal (Var[Y; P]).toNNReal (∫ ω, Y ω ∂P) k
  rw [← hY.map_eq_gaussianReal] at h
  exact (integrable_map_measure (continuous_pow k).aestronglyMeasurable hY.aemeasurable).mp h

                                                                                     
                      
                                                                                  
                                                                           
                                                      
                                                                         

                                                                         
                                                
                                                      

                                                                   
                                                                            
                                                     
                                                                                  

end ProbabilityTheory.HasGaussianLaw

end
