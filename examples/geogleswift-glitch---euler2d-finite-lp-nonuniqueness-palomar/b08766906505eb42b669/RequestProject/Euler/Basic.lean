module

public import Mathlib

/-!
# Two-dimensional Euler on the torus: definitions and principal statements

This file formalizes Section 1 of the paper (*Definitions and principal statements*):
the square torus `𝕋² = ℝ² / (2π ℤ)²`, weak Euler solutions (Definition `def:weak-euler`),
and the objects in which the main theorem (`Theorem main`) is stated.

## Modelling conventions

* A field on the torus is modelled by a field on `ℝ²` restricted to the fundamental square
  `torusBox = [0, 2π)²`.  Elements of `L²(𝕋²; ℝ²)` are elements of the Lebesgue space
  `Lp ℝ² 2` for the Lebesgue measure restricted to `torusBox` (total mass `4π²`).
* Periodicity enters through the test functions: all test functions are smooth and
  `2π`-periodic in each space variable, so that distributional derivatives are the
  distributional derivatives on the torus.
* The space–time `L²((0,T) × 𝕋²)` norm is written as the iterated integral
  `∫₀ᵀ ‖u(t)‖²_{L²(𝕋²)} dt`.
* `L^∞(0,T; L^p)` bounds on the vorticity are stated as a uniform bound valid at *every*
  time `t ∈ [0,T]` (which is what the paper proves).
-/

@[expose] public section

open MeasureTheory Real
open scoped ContDiff

namespace Euler2D

/-- The Euclidean plane `ℝ²`. -/
abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- The fundamental square `[0,2π)²` of the torus `𝕋² = ℝ²/(2πℤ)²`. -/
def torusBox : Set R2 := {x | ∀ i, x i ∈ Set.Ico 0 (2 * π)}

/-- Lebesgue measure on the torus (realized on the fundamental square), of total mass `4π²`. -/
noncomputable abbrev μT : Measure R2 := volume.restrict torusBox

                    
                                      

                                                                                        
                                                      
                                                                       

                                        
                                                                         
                                            
                                          

                                                 
                                                                          

                                                                     
                                                
                                   
                                                                           

                                                                     
                                                               
                                               
                                
                                                                                       

                                                                                        
                                                
                                                
                                                                            
                                         
                                                                         

                                                                        
                                                                                        
                                                       
                                                            
                                            
                                       
                                                      
                                              

                                                                                       
                                                                                        
                                                                                    

                                                                                             
                           
                                                                                          
                                                                           
                                           
                                            
                    
                               
                                                                      
                                                

                                                                                               
                                                       
                                                                       
                                  
                                                               

                                                                                           
                                       
                                                             
                                

                                                                                   
                                                                
                                    

                                                                                    
                                                                    
                                        

end Euler2D

end
