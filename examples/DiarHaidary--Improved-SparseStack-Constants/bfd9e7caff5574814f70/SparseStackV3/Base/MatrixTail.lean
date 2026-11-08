/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

VENDORED BASE MODULE.  This file is copied verbatim (apart from its import
paths and this header) from the author's Version 2.0 formalization at
https://github.com/DiarHaidary/Nelson-Nguyen-conjecture-upper-bound-palomar
(`SparseFockFormal/MatrixTail.lean`).  The sketch distribution, the Parseval-frame
encoding of `U`, the finite-probability API and the operator-norm/trace
bridge are unchanged between Version 2.0 and Version 3.0 of the manuscript,
so they are reused rather than reproved.
-/
import SparseStackV3.Base.SparseStackDistribution
import SparseStackV3.Base.FiniteProbability
import Mathlib
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace SparseFock

namespace MatrixTail

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

                                                                          
                                                              
                                                                           
                                                       
                          
                                
      
                                                  
                             
                                                                        
                                       
                              
                                                           
                                                                       
                                  
         

                                                                           
                                                                    
                                                       
                                  
                                                   
      
                   
                                                 
                               
                                                                                     
                                                                          
                                                
                               
                                                                                       
                  
                                                       
                                                    
                                                                                          
                                           
                                         
                                                                                    
                                                              
                                       
                                                         
             

                                                                         
                                                
                                  
                                 
                                        
                                                                                     

                                                                            
                                                                  
                                                         
                                                     
                                             
                                        
                                      
                                                         
           
      
                                                                   
                                      
                                                                          
                                             
                                
                                                                     
                           

                                          
                                                                           
                                            
                                                   
                                               
                                             
                                  
             
                             
                                                 
             
                            
             
                              
                                                       

                                                                          
                                                                        
                                                                            
                                                  
                                            
                                                      
                          
                            
                                                                     
                                                                             
                                                                           
         
                                                                   
             
      
                                                
                                                               
                    
                                                         
                            
                                                                       
                                      
                                                                             
                                  

                                                                           
def quadraticForm (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A x, x⟫_ℝ

/-- For a real symmetric matrix, L2 operator-norm control is exactly uniform
control of its homogeneous quadratic form. -/
theorem opNorm_le_iff_quadraticForm (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖A‖ ≤ ε ↔
      ∀ x : EuclideanSpace ℝ ι,
        |quadraticForm A x| ≤ ε * ‖x‖ ^ 2 := by
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) A
  have hT : (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι).IsSymmetric := by
    change (Matrix.toEuclideanLin A).IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  constructor
  · intro hop x
    have hTx : ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
    have hTop : ‖T‖ ≤ ε := by simpa [T, Matrix.l2_opNorm_toEuclideanCLM] using hop
    calc
      |quadraticForm A x| = |⟪T x, x⟫_ℝ| := rfl
      _ ≤ ‖T x‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right hTx (norm_nonneg x)
      _ ≤ (ε * ‖x‖) * ‖x‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hTop (norm_nonneg x)) (norm_nonneg x)
      _ = ε * ‖x‖ ^ 2 := by ring
  · intro hquad
    change ‖T‖ ≤ ε
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro x
    by_cases hx : x = 0
    · simpa [hx] using hε
    · have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
      have hxquad := hquad x
      rw [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, abs_div,
        abs_of_nonneg hxpos.le]
      apply (div_le_iff₀ hxpos).2
      simpa [quadraticForm, T] using hxquad

                                                                            
                                                  
                           
                                           
                                           

                                                
                              
                                                               
                                      

                                                                         
                                                                            
                           
                                                          
                                               
                                     
                                                                  
                                                    
             
             
                  
                                    
                     
                             
             
                              
                                      
                             

open ParsevalFrame SparseStackModel

                                                                            
                                              
                                        
                                        
                                    
                                                        
                                                                         

                                                                          
                                                       
                                        
                                     
                                                                 

                                                      
                                                           
                                                             
                                                              
                              
                                                      
                                         

universe u_m u_n

                                                                         
                                         
                                                                         
                                                                       
                                                   
                              

                                                                        
                                                
                                                      
                                           
                                                 
                                                                       
                                                                  
                                                       
                            
                                
                                                               

                                                                           
                                                      
                                                                      
                                                      
                                                   

                                                                           
                               
                                                
                                                     
                                                                            
                                 
                                                 
                                             
                                                                           
            
                                                                          

                                                                        
                                            
                                                                     
                     
               
                                                       
                                                       

                                                               
                                                
                                                                 
                           
                                                           
                                                           

                                                                         
                                                                            
                                  
                                                                  
                                                             
                                                      
                                                     
                                              

open SparseStackDistribution

                                                                          
                                        
                                                                 
                                                               
                                
                                              
                                    
                                                                   
                         
                                                  
                                       
                                                                         

                                                                             
                                                  
                                                               
                                                               
                                
                                                   
                                    
                                                                   
                         
      
                                
                                                   
                                    
                                                    
                               
                
                                                               
                              
                     
                                             
                                      
                                                                   
                                                                    

                                                                         
                                                                        
                                                                      
                                                             
           
              
                                    
                                                                   
                          
                                        
                                                   
                                     
                                           
                                                           
        
                                          
                                      
                                                           
           
                                        
                                                                     
                                                                    
                      
      
                                                        
                                   
                                               
                                                                           
                                    
                                                      

end

end MatrixTail

end SparseFock
