/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

module
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
@[expose] public section

/-!
# Frobenius pairing, entrywise positive part, and the Schur product

This file records the real Frobenius inner product `⟨B, C⟩ = tr(Bᵀ C)`, the
entrywise positive part of a matrix, the rank-one Laplacian
`vecMulVec (e i - e j) (e i - e j)`, and the Schur product theorem for real
positive semidefinite matrices.
-/

namespace BN

open Matrix
open scoped Matrix

variable {m n : Type*}

/-! ### N06 — Frobenius pairing -/

/-- The real Frobenius pairing `⟨B, C⟩ = tr(Bᵀ C)`. -/
def inner [Fintype n] (B C : Matrix n n ℝ) : ℝ :=
  (Bᵀ * C).trace

section Inner

variable [Fintype n]

                                          
                                                                   
                                                                    

                                                               
                                               
                                                     
                                                 

                                                                
lemma inner_add_right (B C₁ C₂ : Matrix n n ℝ) :
    inner B (C₁ + C₂) = inner B C₁ + inner B C₂ := by
  simp [inner, mul_add, trace_add]

                                                                  
                                                    
                                         
                                                                 

                                                                   
                                                     
                                         
                                                        

                                                                               
                                                                
                                                           
lemma inner_eq_sum (B C : Matrix n n ℝ) :
    inner B C = ∑ i, ∑ j, B i j * C i j := by
  simp only [inner, trace, diag, mul_apply, transpose_apply]
  rw [Finset.sum_comm]

                                                                   
                                     
                                         
                              

end Inner

/-! ### N08 — Entrywise positive part -/

                                                                     
                                                
                             

       
                                                        
                                    
     

                                                         
                        
                  

                                                             
                                              
               

                                           

                                                  
                                        
               

                                             
                                                                        
                                                                            
                                              
                        

                                                                             
                                                                        
               
                                           
                             
                                  
                                   
                                   
                  
                                                   
                        

                                                           

                                                            
                                                                
                                                 
                                     
                   
                    
                           
                                                              
                                            
                                                         
                           
                 
                                                          
                                                                        
                                                                        
                                                                           
                                                                    
                                   
                
                                   
                      
                       
                                                                                  
                                             
                                                            
                                                                
                
                                   
                      
                  
                                                            
                                         
                   
      

                                              

                                                                  
                                              
                                                              
                                
                                                               
                                                                             
                                   
                                               

                                                      
                                                                
                         
                                                    
         
                                                         
                                           
                                                           

                                                                              
                       
                                                                   
                                             
                               
                                                              
                                                            
                                      
                                                                               
                                                                   
                                                            

                                                                                
                                                                    
                                    
                                                         
         
                                                                    
      

                                                                    
                                                                    
         
                                                         

                                                                      
                                                                      
                                                        
                                                  
                                                      
                                                                      

                                                                         
                                                           
                                                       
                                                                  
                            
                                                                     
                                                             
                                   
                                                                              

                                                        
                                                            
                                                                  
                           

end BN
