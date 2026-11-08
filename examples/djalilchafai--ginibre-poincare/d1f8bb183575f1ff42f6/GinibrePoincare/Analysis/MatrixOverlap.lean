module

public import Mathlib
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.Complex.BigOperators

@[expose] public section

/-! # Spectral-projector overlap algebra

The overlap convention is exactly `O j k = Tr (P k * (P j)ᴴ)`.
These results are unconditional finite-dimensional algebra; they do not assert
the Ginibre spectral pushforward or eigenvalue differentiability.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace GinibrePoincare
noncomputable section

variable {ι n : Type*} [Fintype ι] [Fintype n]

/-- Columns consist of the entries of each spectral projector. -/
def matrixProjectorColumns (P : ι → Matrix n n ℂ) : Matrix (n × n) ι ℂ :=
  fun rc j => P j rc.1 rc.2

/-- The overlap Gram matrix, in the paper's index convention. -/
def matrixOverlap (P : ι → Matrix n n ℂ) : Matrix ι ι ℂ :=
  fun j k => Matrix.trace (P k * (P j)ᴴ)

omit [Fintype ι] in
theorem matrixOverlap_eq_gram (P : ι → Matrix n n ℂ) :
    matrixOverlap P = (matrixProjectorColumns P)ᴴ * matrixProjectorColumns P := by
  ext j k
  simp only [matrixOverlap, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, matrixProjectorColumns, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _

                                                  
                                                         
                                      
                            
                                                  

                                                          
                                                                             

                                                                                  
def matrixHSNormSq (A : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (A * Aᴴ)).re

theorem matrixHSNormSq_eq_sum (A : Matrix n n ℂ) :
    matrixHSNormSq A = ∑ r, ∑ c, Complex.normSq (A r c) := by
  simp [matrixHSNormSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Complex.mul_conj, Complex.re_sum]

                                                                             
                            
                                                                                         

                                                 
def matrixProjectorCombination (P : ι → Matrix n n ℂ) (a : ι → ℂ) : Matrix n n ℂ :=
  ∑ j, a j • P j

/-- The overlap-weighted energy. -/
def matrixOverlapEnergy (P : ι → Matrix n n ℂ) (a : ι → ℂ) : ℝ :=
  (star a ⬝ᵥ (matrixOverlap P *ᵥ a)).re

theorem matrixOverlapEnergy_eq_HS (P : ι → Matrix n n ℂ) (a : ι → ℂ) :
    matrixOverlapEnergy P a = matrixHSNormSq (matrixProjectorCombination P a) := by
  unfold matrixOverlapEnergy
  rw [matrixOverlap_eq_gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]
  rw [matrixHSNormSq_eq_sum]
  simp only [dotProduct, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp [Matrix.mulVec, dotProduct, matrixProjectorColumns, matrixProjectorCombination,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

                                                                       
                                     
                                
                               

                   
                                                                                 
                                                                             
                        
                                                                                     
                                                                 

                                                                      
                        
                                                                       
                                                           
                                       

                                                         
                                              
                                                                
                            

                                                    
                                                             
                                                   
                                                                                      
                     
                            
           
                     
          

                                                                                               
                                                                           
                                             

                                                                      
                                                                      
                                                                               
                                                                                
                              

                                                                                    
                                                                     
                        
                                                       
                                                      
                                                                                  
                                                                         
                

                                              
                                                          
                             

                   
                                                              
                                           
                                                                           
                                                                                      
         
                                                                                     
            

                   
                                                           
                         
                                                                                        
                                                                       
         
          
                                                   

                                                        
                                                               
                                                        
         
                                                                         
                                                           
                            
           
      

                   
                                                                        
                                  
                                                           
                     
                                                                       
                                                                             
                                                                   
                                    
                    
                 
        

                                                    
                                                                 
                                                                                

                                                                       
                                                                          
                                                                           
                                                                            
                                                                                 
                                                             
                      
                            
           
                            
           
      

                   
                                                            
                                                                    
         
                                                                     

                   
                                                                 
                                                                     
                                                     
                                                                 
                                                               
                                 

                                                                         
                                                                        
                                                                 
                                                             
                                                                         
         
                                        
                              
                        

                                                                       
                                                                         
                                                                         
                                     
                                                                                   
                                                                                   
                                      

                                                                             
                                      
                                       
                                         
                                       
                                        
                                   
                                                 
                                              
                                       
                                             

end
end GinibrePoincare
