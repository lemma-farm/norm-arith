module

public import SphericalAging.CriticalEndpoint
public import SphericalAging.SpectralLaplace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Map

public section

/-!
# Normalizing the stationary scalar equation

This file proves the change of time and profile in Lemma 16.3 of the manuscript.
The hypotheses below are the actual stationary-profile facts used in that lemma:
continuous differentiability, `c' = -r`, `c(0)=1`, the scalar memory equation,
and the plateau identity. They are not assertions that the normalized equation
already holds. Derivatives at zero are derivatives within the nonnegative ray.
-/

open MeasureTheory Set
open scoped Topology

namespace SphericalAging.StationaryNormalization

noncomputable section

/-- Profile after the change to normalized time. -/
@[expose] def normalizedProfile (q : ℝ) (c : ℝ → ℝ) (z : ℝ) : ℝ :=
  (c ((1 - q) * z) - q) / (1 - q)

/-- Positive normalized response, the negative derivative of the profile. -/
@[expose] def normalizedResponse (q : ℝ) (r : ℝ → ℝ) (z : ℝ) : ℝ := r ((1 - q) * z)

/-- Memory after subtraction of its plateau value. -/
@[expose] def normalizedMemory (q : ℝ) (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 - q) * (φ (q + (1 - q) * y) - φ q)

/-- Causal convolution on the nonnegative time ray. -/
@[expose] def causalConvolution (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in 0..t, f (t - s) * g s

                                                                                
                                                                 
                          
                                    
            
      

                                                                                 
                                     
                          
                                    
                

                                                     
                                                           
            
                                                 

                                                                       
                                                                                      
                          
                                                                   
                                                                      

                                                                        
                                                                                       
                                                                                               

                                                                     
                                                                                          
                          
                                                             
                                                                    

                                                                             
                                                                   
                          
                                                                                        
                                    
                                          
                                                           
                                                                            
                                                                         
                                                                                         
                   
       
                             
              

                                                                        
                                                                   
                          
                                                                                   
                                                                             
                                                             

                                                               
                                                          
                                      
                                                        

                                                                     
                                                                     

                                                                   
                                                                                        
                                                              
                            
                                                                                        
                                                             
                                                                          
                                             
               
         
                                       
            
            
                                         
                           
                                                                 

                                                                    
                                                    
                                            
                                                                    
                         
           

                                                           
                                                                      
                                                               
                   
                                                                   
                          
                                                                               
                                                     
                                                      
                                                                                   
                                                                                       
                                                                     
                                 
                                                                                          
                               
                                                                              
          

                                                                              
                                                           
                                                                
                                                                                   
                   
                                                                   
                                  
                                      
                                            
                          
                                                                             
                                                                                 
                                                                            
                                          
                                                     
                                                      
                                                                        
                                                                                   
                                                   
                           
            
                                                                                             
                     
                              
                                                                     
                                         
                           
                                               
                                                                                      
                      
                                                                                                     
                                                           
                                                   
                                        
                                                                                   
                                               
                                                                                 
                                        
                                              
                            
                                                    
                                         
              
              
                                                           
        
                    
                                            
                                                                       
                                                         
                                                                                          
                                                                  
                                                                                  
                                        
                            
                                        
                                         
              
              
                                                       
                                                                                    
        
            
          

                                                           
@[expose] def purePhi (p : ℕ) (b γ y : ℝ) : ℝ := γ + b * (p : ℝ) * y ^ (p - 1)

                                                                  
                                                                   
                                                                            

                                                                        
@[expose] def memoryCoefficient (p : ℕ) (q : ℝ) (j : ℕ) : ℝ :=
  (1 / ((p : ℝ) - 1)) * ((p - 1).choose j : ℝ) * ((1 - q) / q) ^ (j - 1)

                                                     
                                          
                                                                               
                                 
      

                                                                
                                                         
                                          
                                                                                        
                            
                                              
                                     
                                                                                                   
                       
                           
                                           
            
                             
                                        
      

                                                                   
                                                              
                                                                         
                                                         
                                     
                                                                  
                                                      
                                                       
                                              
                                                                                    
      
                                                                  
                                                  
                                                
                                                              
                         
          
                                                                
                                                                               
                                                
                                             
                                                                        
                                   
                             

                                                              
                                                                      
                                     
                                                                
                                                
                                           
                            
                                                              
                              
                                                               
                          
              
            

                                                              
                                                            
                                     
                                                
                                           
                              
                                                                                     
                                    
            

                                                                        
                                       
                                                                        
                                                                
                                          
                                                                                       
                                
                                                                                              
                                                                                   
                              
              
                                                                 
                                                 
           
                                               
                                     
                                                                        
               

                                                                           
                                                                  
                                                                          
                                                
                                           
                                         
                          
            

                                                                            
                                                                         
                                                                            
                                                
                              
                                           
                            
                                                               
                          
                                            
          
            
      

                                                                               
                                                                       
                                                  
                                                                   
                                                                                      
                                                                                  
                                                                                     
                                                                                                               

                                                                   
                                                                          
                                 
                                                                   
                                      
                                                  
                                                       
                                                     
                                                        
                                        
                                                     
                                   
              
                                                                                    
                                                           
              
                                                          
                                       

                                                      
                                                                            
                                                 
                                                                   
                                      
                                                  
                                                      
                                                     
                                                        
                                                  
                                                                                    
                                   
                   
                                                                                      
                                                            
                                                                  
                                            
                                                     

                                                                          
                                            
                                                    
                                 
                                                                   
                                                                     
                                                   
            
                                                                    
                                                              
                                       

                                                                   
                                                             
                                 
                                                                   
                                      
                                                                                     
                                                                  
                                     
                                                              
                                   
                            
                                                                 
                                                          
                                     

                                                                        
                                                                
                                 
                                                                   
                                      
                                                                       
                                     
                                                                        
                                                     
                          
                                                  

                                                                      
                                                                            
                                                   

                                                                       
                                                                              
                                                                      

                                                   
                                                                    
                                                                                        
                                            
                                                 
                                                                                            
        
                                                                                     
                                                                                       

                                                                          
                                                                               
                                            
                                                               
                                                            
                                        
             
                                
                                                                    
                                     
                                                
                                                      
               

                                                                             
                                                                                 
                                            
                                                               
                                                              
                                                                    
                                  
                

                                                                                      
                                            
                                                               
                                                   
                                        
                                                                    
                                  
                                                                  
                                               
                                                                
         
                                                                 
           
                                
                                                                   
                                     
                                                                                                 
               

                                                                        
                                                                                 
                                                                          
                                                 
                                                       
                                     
               
                                       
                                        
                                                                                          
                                  
                                                      
                                                

                                                                      
                     
                                                                                    
                                                                           
                          
                                                                                  
                                                         
                                                                                        
                                                  
                                                                                                             
                       
                                        
                                                                                      
                                            
                

                                                                                  
                                                                                         
                                                                 
                                                                          
                                  
                                                                  
                                             
                                                                                   
                                
                                                                                             
                         
         
                         
                       
                                                           

                                                                         
                                                                 
                                                                                     
                                                        
                                                             
                                                                 
                          
                                                                                             
                                              
                          
                                                              
                                                                                          
      

                                                                           
                                                                                 
                                            
                                                               
                                                        
                                                                      
                                                                                    
             
                                                   
                                                                                   
      

                                                                             
                                                                       
                                                                                  
                                                        
                                                             
                                                                 
                                  
                                                                      
                                                                      
                                                            
                                   
                                                                  
                           
                                                                                                 
          

                                                                                 
                                                                             
                                                          
                                                             
                                                                 
                                                                   
                          
                                                                                                      
                                                                      
                                                                                                       
                                                       
                                   
                                                                  
                           
                                                                                                 
        
                          
          

                                                                        
                                                                            
                                                                           
                                                          
                                 
                                                             
                                                                 
                                                                     
                                                       
                                                                      
                                                                                
                                                                                             
            
                                                                    
                                              
                                                                           
                                               
                                                                                       
                                                      
                                                                                   
               
                                                         
                                                      

                                                                       
                                                                            
structure NormalizedStationaryConclusions (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ) : Prop where
  profile_C1 : ContDiffOn ℝ 1 (normalizedProfile q c) (Ici 0)
  derivative : ∀ z : ℝ, 0 ≤ z →
    derivWithin (normalizedProfile q c) (Ici 0) z = -normalizedResponse q r z
  equation : ∀ z : ℝ, 0 ≤ z →
    derivWithin (normalizedProfile q c) (Ici 0) z + normalizedProfile q c z +
      causalConvolution (fun t => normalizedMemory q (purePhi p (β ^ 2) γ) (normalizedProfile q c t))
        (fun t => derivWithin (normalizedProfile q c) (Ici 0) t) z = 0
  initial_profile : normalizedProfile q c 0 = 1
  memory_expansion : ∀ y : ℝ, normalizedMemory q (purePhi p (β ^ 2) γ) y =
    y + ∑ j ∈ Finset.range (p - 2), memoryCoefficient p q (j + 2) * y ^ (j + 2)
  quadratic_coefficient : memoryCoefficient p q 2 = CriticalEndpoint.relaxationParameter p q
  coefficients_nonnegative : ∀ j : ℕ, 0 ≤ memoryCoefficient p q j
  spectral_probability : ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Ioi 0) = 1 ∧
    ∀ z : ℝ, 0 ≤ z → normalizedProfile q c z = ∫ η : ℝ, Real.exp (-η * z) ∂μ
  profile_positive : ∀ z : ℝ, 0 ≤ z → 0 < normalizedProfile q c z
  profile_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (normalizedProfile q c) (Ioi 0)
  complete_monotonicity : ∀ n : ℕ, ∀ z : ℝ, 0 < z →
    0 < (-1 : ℝ) ^ n * iteratedDeriv n (normalizedProfile q c) z
  profile_limit : Filter.Tendsto (normalizedProfile q c) Filter.atTop (𝓝 0)
  response_continuous : ContinuousOn (normalizedResponse q r) (Ici 0)
  response_positive : ∀ z : ℝ, 0 ≤ z → 0 < normalizedResponse q r z
  response_nonincreasing : AntitoneOn (normalizedResponse q r) (Ici 0)
  initial_response : normalizedResponse q r 0 = 1
  response_integrable : IntegrableOn (normalizedResponse q r) (Ioi 0)
  response_mass : (∫ z in Ioi 0, normalizedResponse q r z) = 1

                                                                         
                                                                          
                                                                     
                                                                                    
                                                                     
                                   
                                                                   
                                      
                                                
                                      
                                                              
                                                    
                                                                 
                                                       
                                            
                                                             
                                                                   
                                                     
                                                                                    
                             
                             
                                                                        
                                                                                  
                                                             
                                                                  
                                                                             
                                                   
                                                   
                                                             
                                                                
                                       
                                                                    
                                    
                                                
                                                  
                                                                                      
                                                         
                                                                                        
                                                              
                                                                           
                                                
                                               
                                         
                                                                                             
                                    
                                                                   
                                                                         

end
end SphericalAging.StationaryNormalization
