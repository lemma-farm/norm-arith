import QuadraticCarleson.KrauseLaceySparseDilation
import QuadraticCarleson.KrauseLaceyFiniteRadiusSmoothSparse
import QuadraticCarleson.HardyLittlewoodBoundaryControl

/-!
# Arbitrary smooth radii versus adjacent dyadic radii

Rounding an arbitrary positive smooth radius upward to the next dyadic radius
costs at most `24` times the centered Hardy--Littlewood maximal function.  This
is a bound for the actual difference of the two smooth operators, obtained
from the two cutoff-boundary terms and the sharp annular rounding term.

The same single error bounds every finite maximum, with no cardinality loss.
The lower index of the comparison dyadic maximum is taken from the actual
radii, so a common real scale offset is not incorrectly treated as preserving
the original integer-dyadic lower index.  Pairing comparisons use `normInput`
on their right sides, avoiding cancellation of complex test functions.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal Topology ComplexConjugate

namespace QuadraticCarleson.KrauseLaceyScaleOffsetPointwise

open QuadraticHilbertMaximalMeasurable KrauseLaceySharpSmoothAdapter
open KrauseLaceySparseDilation KrauseLaceyFiniteRadiusSmoothSparse
open KrauseLaceyCompactPairingStabilization KrauseLaceySparseReflection
open HardyLittlewoodBoundaryControl

set_option autoImplicit false

noncomputable section

/-- The actual difference between adjacent smooth cutoffs is one annular
error, uniformly dominated by the same maximal function. -/
theorem enorm_smoothHighPass_sub_le_maximal
    (lam : ℝ) {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ) (hρε : ρ ≤ 2 * ε)
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    ‖smoothQuadraticHighPass lam ε f x - smoothQuadraticHighPass lam ρ f x‖ₑ ≤
      24 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  have hρ : 0 < ρ := hε.trans_le hερ
  have hεeq := quadraticHilbertTrunc_eq_smoothHighPass_add_boundary lam hε hfi x
  have hρeq := quadraticHilbertTrunc_eq_smoothHighPass_add_boundary lam hρ hfi x
  have hround := quadraticHilbertTrunc_sub_rounded_eq_boundary lam hε hρ hfi x
  have heq : smoothQuadraticHighPass lam ε f x - smoothQuadraticHighPass lam ρ f x =
      ((∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y) -
        ∫ y, cutoffBoundaryKernel lam ε (x - y) * f y) +
          ∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y := by
    rw [← hround, hεeq, hρeq]
    ring
  rw [heq]
  calc
    _ ≤ (‖∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y‖ₑ +
        ‖∫ y, cutoffBoundaryKernel lam ε (x - y) * f y‖ₑ) +
          ‖∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y‖ₑ :=
      (enorm_add_le _ _).trans (add_le_add enorm_sub_le le_rfl)
    _ ≤ (8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x +
        8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
          8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x :=
      add_le_add (add_le_add
        (radiusRoundingBoundaryOperator_enorm_le_maximal lam hε hερ hρε f hf x)
        (cutoffBoundaryOperator_enorm_le_maximal lam hε f hf x))
        (cutoffBoundaryOperator_enorm_le_maximal lam hρ f hf x)
    _ = _ := by ring

                                                         
                                  
                                                                  
                                        
                                                                   
                                                               
                                                                          
                                               

                                                         
                                  
                                                                  
                                          
                                                                  
                                                                    
      
                                                                  
                                            
                                                                          
             
          
                                                        
                                                                          

                                                                      
                                                                     
                                                                                 

                                                                     
                                             
                                                                   
                                                     
                           

                                          
                                                                                       
                              
                                                                   
                                                                                   
                                               
                                                                                
                                                                                     
             
                                                
         
                                                                                         
         
                            
                                                                                       
              

                                                       
                                                                
                                          
                                                                  
                    
                                                        
                                                                                     
                                                  
     

                                                                            
                                                                         
                                                      
                                                                          
                                          
                                                                               
                                                                    
                                    
                     
            
                                                                  
                                            
                                                                             

                                                      
                                                                          
                                         
                                                                              
                                                                
                                                                    
                                                           
                                                                
                                                                              
                                                               
                                                
                                                              
                                                                          
                        

                                                                       
                                                                   
                                                   
            
                                                                       

                                                                       
                                                                            
                                                              
                                                                    
                                                           
                                                                                         
                            
                                                                                            
                             
                                                                                             
                                                                                               
                                                                    
                                             
                                                                              
                                                                                        
                                                                      
                                                                            
                                                                                         
                                
                                                                                           
                                          
                                                                                            
                                                                                             
                                          
                                              
                                                                             
                                                                            
                                                                
                       
                                        
      
                                                                                 
                                                                      
                                
                                                                                  
                    


end
end QuadraticCarleson.KrauseLaceyScaleOffsetPointwise
