module

public import Paper.GaussianHeat
public import Paper.RSFunctional
public import Paper.GaussianConvolution
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section


/-!
# The weak Parisi equation and its concrete Duhamel operator

The potential has linear growth and is not required to be bounded.  The
weak spatial gradient is separately represented and essentially bounded.
Tests for the terminal equation have compact support away from time zero;
their support is allowed to meet time one, so the terminal trace is retained.

The Gaussian operators below are actual integrals, not abstract kernels.
The estimates are the preliminary bounds for a bounded-gradient fixed point.
No existence or uniqueness of the general weak PDE is asserted in this file.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff

namespace Paper

/-- Lebesgue measure on the time strip used by the distributional equation. -/
noncomputable def parisiSpaceTime : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod volume

/-- Spatial and time derivatives of a smooth test on the full plane. -/
noncomputable def parisiTestX (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => φ (p.1, x)) p.2

noncomputable def parisiTestXX (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => parisiTestX φ (p.1, x)) p.2

noncomputable def parisiTestT (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun t => φ (t, p.2)) p.1

/-- Distributional spatial derivative on the open time strip.
Integrability is explicit so that an undefined Bochner integral cannot
trivially satisfy the distributional identity. -/
def IsParisiWeakGradient (u v : ℝ × ℝ → ℝ) : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1} →
    Integrable (fun p => u p * parisiTestX φ p + v p * φ p) parisiSpaceTime ∧
      (∫ p, u p * parisiTestX φ p + v p * φ p ∂parisiSpaceTime) = 0

/-- The weak terminal-value problem in Jagannath--Tobasco's solution class.
The smooth compactly supported tests are supported in positive times, but
need not vanish at the terminal boundary. -/
structure IsParisiWeakSolution (β : ℝ) (μ : ParisiMeasure)
    (u v : ℝ × ℝ → ℝ) : Prop where
  continuous_potential : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ)
  measurable_gradient : AEStronglyMeasurable v parisiSpaceTime
  bounded_gradient : ∃ M : ℝ, ∀ᵐ p ∂parisiSpaceTime, ‖v p‖ ≤ M
  weak_gradient : IsParisiWeakGradient u v
  terminal : ∀ x : ℝ, u (1, x) = Real.log (Real.cosh x)
  equation : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1} →
    Integrable (fun p => -u p * parisiTestT φ p + β ^ 2 / 2 *
      (u p * parisiTestXX φ p + parisiCDF μ p.1 * v p ^ 2 * φ p)) parisiSpaceTime ∧
    Integrable (fun x => φ (1, x) * Real.log (Real.cosh x)) ∧
    (∫ p, -u p * parisiTestT φ p + β ^ 2 / 2 *
      (u p * parisiTestXX φ p + parisiCDF μ p.1 * v p ^ 2 * φ p)
      ∂parisiSpaceTime) +
      (∫ x, φ (1, x) * Real.log (Real.cosh x)) = 0

                                                                              
                                   

                                                         
                                                           
                                                                     
                                          
                                                                                                    
                                              

                                                                
                                                               
                                                                             
                                                                         
                                                 

                                                 
                                                     
                                                           
                                              
                                                         
                                                                          
                                                         

                                                                      
                                                           
                                             
                                                    
      
                                             
                                                                   
                                                                             
                        
                            

                                                                          
           
                                                              
                                      
                                                                           

                                                               
                                                   
                                                 
                                        
                                                                 
                                             
                                    
                                                                                   

                                                            
                                                               
                                                
                                              
           
                 
                                                   
                                     
                                                               
                              
      
                                                      
                                                                                 
                                                                      
                                   
                          

                                                                       
                                               
                                         
                                                                 
                                                                                       
                                                                   
                                                                           

                                                                            
                                                                     
                                      
                                                       

                                                                          
                                                                    
                                    
                                                                       
                                       

                                                                   
                                                 
                               
                                                                             
                                                              
                                                                            
                                              
                                
                                                                                         
      
                                                             
                                                                                  
                                              

                                                                
                                                             
                                                           
                                             
                                                                                   
                                                        
                 
                                                    
                                                        
                 
                                                    
                                                                  
                                                      
                                                                           
                                                                                  
                                                                     
                                                                   
                                                                      
                                               
                                     
                                                               
                              
                         
                          
                                                                                

                                                                          
                                                 
                                                                       
                                                             
                                                           
                                                           
                                          
                                                                          
                                                                       
                                                                       
                                                              
                                                                            
                           
                                              
                                
                                                                 
                                                                             
      
                                                            
                                                                            
                                                   
                                          

                                                                         
noncomputable def gaussianAbsMoment : ℝ := gaussianExpectation (fun z => ‖z‖)

                                                           
                                          

                                                                           
                                                                   
noncomputable def heatGradient (ell : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt ell)⁻¹ * gaussianExpectation (fun z => z * f (x + Real.sqrt ell * z))

                                                               
                                                               
                                                                                 
                                                                                     
                                                 

theorem norm_heatGradient_le (ell : ℝ) (f : ℝ → ℝ) (M : ℝ)
    (hb : ∀ y, ‖f y‖ ≤ M) (x : ℝ) :
    ‖heatGradient ell f x‖ ≤ (Real.sqrt ell)⁻¹ * gaussianAbsMoment * M := by
  have h : ‖gaussianExpectation (fun z => z * f (x + Real.sqrt ell * z))‖ ≤
      M * gaussianAbsMoment := by
    have hb' : ∀ᵐ z ∂gaussianReal 0 1,
        ‖z * f (x + Real.sqrt ell * z)‖ ≤ M * ‖z‖ :=
      Filter.Eventually.of_forall fun z => by
        rw [norm_mul, mul_comm M]
        exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg z)
    have hi := norm_integral_le_of_norm_le
      (integrable_standardGaussian_id.norm.const_mul M) hb'
    simpa [gaussianExpectation, gaussianAbsMoment, integral_const_mul] using hi
  unfold heatGradient
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  calc
    (Real.sqrt ell)⁻¹ * ‖gaussianExpectation (fun z => z * f (x + Real.sqrt ell * z))‖ ≤
      (Real.sqrt ell)⁻¹ * (M * gaussianAbsMoment) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (Real.sqrt ell)⁻¹ * gaussianAbsMoment * M := by ring

                                                
                                                     
                                                           
                                             
                                                       
                                         
                   
                                                                       
                                                                  

theorem intervalIntegrable_inv_sqrt_sub (t b : ℝ) (htb : t ≤ b) :
    IntervalIntegrable (fun s => (Real.sqrt (s - t))⁻¹) volume t b := by
  have heq : EqOn (fun s => (Real.sqrt (s - t))⁻¹)
      (fun s => (s - t) ^ (-(1 / 2 : ℝ))) (uIoo t b) := by
    intro s hs
    rw [uIoo_of_le htb] at hs
    dsimp only
    rw [Real.rpow_neg (sub_nonneg.mpr hs.1.le), ← Real.sqrt_eq_rpow]
  apply (intervalIntegrable_congr_uIoo heq).mpr
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b - t)
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).comp_sub_right t
  simpa using hi

/-- The heat-gradient singularity has a finite and explicit time integral. -/
theorem integral_inv_sqrt_sub (t b : ℝ) (htb : t ≤ b) :
    (∫ s in t..b, (Real.sqrt (s - t))⁻¹) = 2 * Real.sqrt (b - t) := by
  have heq : EqOn (fun s => (Real.sqrt (s - t))⁻¹)
      (fun s => (s - t) ^ (-(1 / 2 : ℝ))) (uIoo t b) := by
    intro s hs
    rw [uIoo_of_le htb] at hs
    dsimp only
    rw [Real.rpow_neg (sub_nonneg.mpr hs.1.le), ← Real.sqrt_eq_rpow]
  rw [intervalIntegral.integral_congr_uIoo heq,
    intervalIntegral.integral_comp_sub_right (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) t]
  simp only [sub_self]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  ring

                                                                
                                                                  
                                      
                                                                          

                                                                   
                                                   
                                                     
                                        
                                                                       
                                                                  
                                                        
                                       
                                                                                    
                                                

                                                                
                                                               
                                        
                                                                       
                                                       
                 
                                                   
                                     
                                                               
                              
                             
               
      
                                                                                  
                                                                          
                                                                                      
                                                                         
                                                                        
          

                                                                           
                                               
                                                     
                                                                     
                                                      
                                                  
                                                                         
                                                                                 

                                                                      
                                      
                                                           

                                                                          
                                                                
                                                                    
                                                 
                               
                                            
                                                               
                                                            
                                                                                          
                                                        
                                          
                                                                              
                                 
                                                                                         
      
                                                                 
                                                                                    
                                                   
                                                                 
                         
                 
                                                 
                       
                  

                                                                    
                                                             
                                                           
                                             
                                                                           
                                                                             
                                                        
                 
                                                    
                                                        
                 
                                                    
                                                                  
                                                      
                                                                          
                                                                 
                                                                               
                                                                    
                                                                   
                                                                      
                                              
                                     
                                                               
                              
                             
                          
      
                                                                                 
                                                                 
                                                                                  
                                                           
                                                                               
                                                                        
          

                                                                    
                                                                      
                                                                        
                                                             
                                                           
                                                           
                                                                                   
                                                                   
                                                                             
                                                                             
                                                            
                                           
                                                                          
                                                        
                                                
                                                                              
                                 
                                                                 
                                                                             
      
                                                                
                                                     
                                                                                
                                                     
                                                                     
                         
                 
                                                 
                       
                  

                                                                           
                             
                                                                   
                                                                                            

end Paper
