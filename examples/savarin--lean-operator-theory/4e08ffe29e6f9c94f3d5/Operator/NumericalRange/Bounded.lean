/-
# Boundedness of the numerical range (L1.2)

The numerical range of a continuous linear operator `A` on a complex inner product space is
contained in the closed disk of radius `‖A‖`: for a unit vector `x`, Cauchy–Schwarz gives
`‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ ≤ ‖x‖ ^ 2 * ‖A‖ = ‖A‖`.

## Main declarations

* `norm_le_of_mem_numericalRange` — `‖z‖ ≤ ‖A‖` for every `z ∈ numericalRange A`.
* `numericalRange_subset_closedBall` and `isBounded_numericalRange` — the
  corresponding set-level forms.
* `numericalRadius` — the supremum of `‖z‖` over the numerical range, with
  its elementary nonnegativity and operator-norm bound.

No completeness assumption on `E` is needed. (Recreated in run-003; the original file was not
recovered after the accidental deletion.)
-/
import Mathlib
import Operator.NumericalRange.Basic

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The numerical range lies in the closed disk of radius `‖A‖`: for a unit vector `x`,
Cauchy–Schwarz gives `‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ ≤ ‖A‖`. -/
theorem norm_le_of_mem_numericalRange (A : E →L[ℂ] E)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc ‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm x (A x)
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by gcongr; exact A.le_opNorm x
    _ = ‖A‖ := by rw [hx]; ring

                                                                        
                                 
                                                          
                                                    
            
                                             
                                          

                                                                      
                                                  
                                             
                                                                         

                                                                       
                                                                       
                                             
                                                        
                             

                                           
                                                
                            
                                                                   

                                                                        
          
                                               
                                                                       
                        
                  
                                                                 
             
                           
                      
                          
                         
                                           

                                                                  
                                                 
                                 
                        
                                                   
                    
                                                                  
