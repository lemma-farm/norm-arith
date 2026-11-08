import QuadraticCarleson.KrauseLaceyBadScaleInputs
import Mathlib
/-!
# Actual nonstandard intervals and their diagonal energy

The nonstandard test is the source's adjoint-composition test, rather than
the desired `L²` estimate. Its right side is the actual unit-window
convolution of the restricted bad input. The diagonal estimate below is
derived from this test and the proved stopping-cell local-mass bound.
-/

open Function MeasureTheory Set
open scoped ComplexConjugate Classical

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction

set_option autoImplicit false

/-- The near-diagonal positive convolution in the source nonstandard test. -/
noncomputable def localUnitMass (I : RealInterval) (b : ℝ → ℂ) (x : ℝ) : ℝ :=
  ∫ t in Icc (x - 1 / 2) (x + 1 / 2), ‖I.centralThird.indicator b t‖

/-- Literal source nonstandard condition, with the concrete near-diagonal
constant multiplied by `100`. We use the equivalent a.e. form. -/
def IsNonstandard (k : ℤ) (I : RealInterval) (b : ℝ → ℂ) : Prop :=
  ∀ᵐ x ∂volume, x ∈ I.centralThird →
    ‖(krauseLaceyPositiveKernel k).adjoint.applyIntegral
      (krauseLaceyLocalizedPiece 1 k I b) x‖ ≤
      (1600 * positiveDyadicAmplitudeBound ^ 2 / I.length) * localUnitMass I b x

                                                                       
                                                                             
                                       
                                                                            
                          
                                          
                                                   
                                                             

                                                                    
                                                                        
noncomputable def nonstandardIntervals
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) : Finset RealInterval :=
  (goodCollection S f 0 I₀).filter fun I ↦
    I.length = (2 : ℝ) ^ (scale I + 2) ∧ k₀ ≤ scale I + 2 - s ∧
      IsNonstandard (scale I) I (badScaleInput S f I₀ k₀ (scale I + 2 - s))

theorem nonstandardIntervals_subset (S : Finset RealInterval) (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ) :
    nonstandardIntervals S f I₀ k₀ s scale ⊆ S := by
  intro I hI
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).1

                                                                                     
                                                                         
                                                                                   
                        
         
                                       

                                                  
                                            
                                                      
                                                 
                                                         
                                                   
                                                 
                                                              

                                                                   
                                                                            
                       
                                                      
                                                              
                        
                                              
                                                          
                                                     
                                                      
                                            
                                      
                                     
                                                                     
                                                                         
            
                                                                               
                                                                             
                    
                                                        
                                                
                                                                       
                                                                   
                                                   
                                                                           
                         
                                                                       
                                                     
      
                                                                                            
                                      
                            
                                                          
                                     
                                     
                                       
                                                                                          
                                         
               
                             
             
                                                                                                      

                                                                  
                                                             
                                              
                                                             
                                    
                                                          
                                                                                   
                                     
                                            
                                                              
                        
                                                                     
                                          
                                                     
                                                                          
                         
                                                                              
                                              
                                                                           
                                                                        
                             
                                                                                   
                                                                     
                                                                
                                    
                      
      
                                                              
                                                                   
                                          
                                           
                                                                                     
               
                                                                                  
                                                    
                                                
                       
                         

                                                                         
                                                                            
                                                  
                                                             
                                                                            
                                                          
                                                                                   
                                     
                                            
                                                                                 
                                                           
                                                           
                                                                          
                                          
                                                                              
                  
                                                                             
      
                                           
                                                           
                             
                
                                                 
                                                                                         
                                      
                                           
                                                                                    
                                                                                            
                                                                
                                                         


end KrauseLaceyBadScale
end QuadraticCarleson
