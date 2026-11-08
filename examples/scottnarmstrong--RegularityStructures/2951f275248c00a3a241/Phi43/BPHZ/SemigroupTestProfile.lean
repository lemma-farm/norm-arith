/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreePsiBallMass
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# Profiles of semigroup test functions on space-time

A *semigroup test profile* at scale `lam` and base point `x` is a measurable function
`g : ℝ × T³ → ℝ` that is bounded by `B lam⁻⁵` and whose absolute moments
`∫ |g| s(· - x)^r` are integrable and at most `Mom r lam^r` for every `r ≥ 0`.  Here
`s = torusParabolicSize`.  This is the abstract shape of the periodised semigroup kernel
`q^♯_t(x, ·)`, `lam = t^(1/4)`, which has a rapidly decaying (non-compactly supported) tail.

The two pieces of information (sup bound and moments) suffice for all the weighted integral bounds
of the chaos reduction:

* `SemigroupTestProfile.integral_rpow_le`: `∫ |g| s(· - x)^a ≤ C lam^a` for every `a > -5`;
* `SemigroupTestProfile.integral_mul_rpow_sub_le`: `∫ |g v| s(u - v)^(-q) dv ≤ C lam^(-q)` for
  `0 < q < 5`, uniformly in `u`.

For negative exponents the singularity is integrated against the sup bound on the ball
`s ≤ lam`, and the exterior is controlled by `lam^(-p)` times the `L¹` norm.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

/-- A semigroup test profile at scale `lam > 0` and base point `x`: measurable, bounded by
`B lam⁻⁵`, with integrable absolute moments `∫ |g| s(· - x)^r ≤ Mom r lam^r`, `r ≥ 0`. -/
structure SemigroupTestProfile (x : SpaceTime) (lam B : ℝ) (Mom : ℝ → ℝ)
    (g : SpaceTime → ℝ) : Prop where
  measurable : Measurable g
  abs_le : ∀ u, |g u| ≤ B * (lam ^ 5)⁻¹
  integrable_moment : ∀ r : ℝ, 0 ≤ r →
    Integrable (fun u => |g u| * torusParabolicSize (u - x) ^ r)
  integral_moment_le : ∀ r : ℝ, 0 ≤ r →
    ∫ u, |g u| * torusParabolicSize (u - x) ^ r ≤ Mom r * lam ^ r

                                                               
                                                              
                                                     

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}

namespace SemigroupTestProfile

                                                                 
                                  
                                             

                                                                 
                                     
                                          

                                                                             
                                                                                             

                                                                  
                            
                                           

                                                                                            
                                                  
                                            
                                       

                                                                               
                                                                 

                                                                                    
                                  
                                      
                                                              
                                                      
                                                        
                                                       
                
                                                       

                                                                          
                                                                             
                     
                                                                                
                                               
                                                         
                                                            
                                           
            
                                             
                                                                            
                                           
               
              
                                                           
                                                                            
              

                                                                                                  
                                                                               
                                                                                    
                                                                                        
                         
                                       
                                                                       
                                
                                                         
                                                                                 
           
                         
                                                    
                                                          
                                                     
                                                          
                                                       
                  
                                                                               
                                                       
                                                                         
                                                                               
                                                                                         
                                    
                
                                                                                
                                                                      
                                              
                                                                      
                                                                                               
                               
                                                        
                                                        
                                                            
                                                             

                                                                                  
                                                       
                                                                       
                                                 
                                                          
                                                        
                                                            
           
        
                                                                                         
                             

                                                                                               
                                                                                          
                                    
                                                                     
                                                      
                                                       
                                                                       
                                                                 
                                                                                          
                                                                            
                                                     
                                                    
                                                     
                                                                                                 
                                                                   
                                               
                                                          
                                                           

                                                                     
                                                                                       
                      
                                                                  
                                                   
                                                     
                     
                                                   
                                                               
                                   
                                                        
                               
                                                    
                                            
                  
              

                                                               
                                                                              
                                                                                 
                                                                 
                                                                     
                                                      
                                                       
                                                                       
                                                                                     
                                                                                          
                                                                                  
                                                     
                                                    
                                                     
                                                                                                 
                                                                   
                                               
                                                          
                                                           

end SemigroupTestProfile

end RegularityStructures

end
