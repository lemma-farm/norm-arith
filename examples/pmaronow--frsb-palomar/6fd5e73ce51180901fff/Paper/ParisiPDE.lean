module

public import Paper.GaussianHeat
public import Paper.RSFunctional
public import Paper.GaussianConvolution
public import Mathlib
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

theorem gaussianAbsMoment_nonneg : 0 ≤ gaussianAbsMoment :=
  integral_nonneg (fun _ => norm_nonneg _)

                                                                           
                                                                   
                                                                   
                                                                                  

                                                               
                                                               
                                                                                 
                                                                                     
                                                 

                                                          
                                   
                                                                            
                                                                           
                                 
                                      
                                                    
                                             
                                 
                                                              
                                          
                                                           
                                                                               
                     
                                                                                      
      
                                                                                        
                                                    
                                                   
                                                            

                                                
                                                     
                                                           
                                             
                                                       
                                         
                   
                                                                       
                                                                  

                                                                 
                                                                        
                                                  
                                                          
              
                             
              
                                                                    
                                               
                                                                             
                                                             
                

                                                                             
                                                       
                                                                      
                                                  
                                                          
              
                             
              
                                                                    
                                               
                                                                                 
                      
                                                                     
          
                          
      

                                                                
                                                                  
                                      
                                                                          

                                                                   
                                                   
                                                     
                                        
                                                                       
                                                                  
                                                        
                                       
                                                                                    
                                                

                                                                
                                                               
                                        
                                                                       
                                                       
                 
                                                   
                                     
                                                               
                              
                             
               
      
                                                                                  
                                                                          
                                                                                      
                                                                         
                                                                        
          

                                                                           
                                               
                                                     
                                                                     
                                                      
                                                  
                                                                         
                                                                                 

                                                                      
                                      
                                                           

                                                                          
                                                                
                                                                    
                                                 
                               
                                            
                                                               
                                                            
                                                                                          
                                                        
                                          
                                                                              
                                 
                                                                                         
      
                                                                 
                                                                                    
                                                   
                                                                 
                         
                 
                                                 
                       
                  

                                                                    
                                                             
                                                           
                                             
                                                                           
                                                                             
                                                        
                 
                                                    
                                                        
                 
                                                    
                                                                  
                                                      
                                                                          
                                                                 
                                                                               
                                                                    
                                                                   
                                                                      
                                              
                                     
                                                               
                              
                             
                          
      
                                                                                 
                                                                 
                                                                                  
                                                           
                                                                               
                                                                        
          

                                                                    
                                                                      
                                                                        
                                                             
                                                           
                                                           
                                                                                   
                                                                   
                                                                             
                                                                             
                                                            
                                           
                                                                          
                                                        
                                                
                                                                              
                                 
                                                                 
                                                                             
      
                                                                
                                                     
                                                                                
                                                     
                                                                     
                         
                 
                                                 
                       
                  

                                                                           
                             
                                                                   
                                                                                            

end Paper
