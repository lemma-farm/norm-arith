/-
# Affine changes of variables for complex polynomials

This file records how evaluation, degree, and `polynomialSupNorm` behave when a
complex polynomial is precomposed with the affine map `z ↦ a * z + b`.

## Main declarations

* `Polynomial.affineComposition` — precomposition by `z ↦ a * z + b`;
* `Polynomial.eval_affineComposition` and `Polynomial.aeval_affineComposition` — scalar and
  algebra-valued evaluation;
* `Polynomial.natDegree_affineComposition_le` and
  `Polynomial.natDegree_affineComposition` — the degree bounds, with equality when `a ≠ 0`;
* `polynomialSupNorm_affineComposition_image` — exact transport of the polynomial sup-norm.
-/
import Mathlib
import Operator.SpectralSet.Basic

open scoped Polynomial

namespace Polynomial

/-- Precomposition of a complex polynomial with the affine map `z ↦ a * z + b`. -/
noncomputable def affineComposition (p : ℂ[X]) (a b : ℂ) : ℂ[X] :=
  p.comp (C a * X + C b)

/-- Evaluating an affine composition is evaluation after the corresponding scalar affine map. -/
@[simp]
theorem eval_affineComposition (p : ℂ[X]) (a b z : ℂ) :
    (affineComposition p a b).eval z = p.eval (a * z + b) := by
  simp only [affineComposition, eval_comp, eval_add, eval_mul, eval_C, eval_X]

                                                                     
       
                                                                      
                                  
                                                                           
                                                                      
                                                                             

                                                                                
                                                             
                                                           
                        
                                               
                        
                                                           
      
                                      
                                                                      
                                                   
                                    

                                                                           
                                                                       
                                                           
                                        
                                                 
                                                                                           
                            
                        

end Polynomial

                                                                                             
                                                                                               
                                           
                                                                                    
                                                   
                                                               
                                                                  
                                     
                                      
                                               
                                                         
                             
                                        
                                                                       
                                                                
             
              
                                                                           
                                                                              
                                         
                                                              
