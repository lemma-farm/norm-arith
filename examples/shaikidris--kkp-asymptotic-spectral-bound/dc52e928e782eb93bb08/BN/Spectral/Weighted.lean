/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

module
public import BN.Spectral.Perron
public import BN.Basic.Spectrum
public import BN.Basic.Inner
                            
public import BN.M.Main
public import BN.MS.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Rank
@[expose] public section

/-!
# Rank-at-most-two spectral slice of a symmetric nonnegative matrix

A symmetric entrywise-nonnegative matrix `B` has a rank-at-most-two PSD slice
`X = a uuᵀ + b vvᵀ` built from a nonnegative Perron vector for `λ_max` and,
when `λ₂ > 0`, a unit eigenvector for `λ₂` orthogonal to it. This slice
satisfies `⟨B, X⟩ = ⟨X, X⟩ = F B` and is a Gram matrix of planar vectors in
the closed right half-plane. If `B` is zero-diagonal and supported on `E(G)`,
the Motzkin–Straus bound on `M X` yields `F B ≤ turanFactor G * ⟨B, B⟩`.
-/

namespace BN

open Matrix Module WithLp Submodule
open scoped InnerProductSpace Matrix

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {B : Matrix n n ℝ}

lemma sum_sq_eq_dotProduct (x : n → ℝ) : ∑ i, x i ^ 2 = x ⬝ᵥ x := by
  simp [dotProduct, pow_two]

                                                                        
                                     
                         
                                                             
                                                 

                                                                   
                                                         
                                        

lemma vecMulVec_mulVec (u v x : n → ℝ) :
    vecMulVec u v *ᵥ x = (v ⬝ᵥ x) • u := by
  ext i
  simp [mulVec, vecMulVec_apply, dotProduct, smul_eq_mul]
  trans u i * ∑ j, v j * x j
  · simp_rw [mul_assoc]
    exact (Finset.mul_sum (Finset.univ) (fun j => v j * x j) (u i)).symm
  · ring

                                               
                                                              
                                                                                
                             

variable [Nontrivial n]

                                            
                                       
                                                                                   

                                         
                                          
                                                                                      

                                                                                             
         
                          
                                                                             
                            

                                                       
                                                      
                                                                  

                                                          
                                                            
                                                                        

                                                            
                                                        
                                                                                
                                                    

                                                                                
                                                                                
                                                                   
                                                       
                                                    
                                  

                                                                                           
                                                 
                                                                         
                                 
                                                
                                        
                                                      
                                                         
                                              
                                                                                          
                                                 
                                                   
                                                  
                                                                 
                                                                 
                             
                                                                      
                                                                     
                                                                           
                                                     
                                                         
                                  
                                    
                  
                                     
                                  
                                                                
                             
        
                                                    
                                                              
                            
           
                                  
                     
                    
                                
                                        
                                                   
                                                           
            
                                                                    
                                          
                                                 
                                        
                                                 
                                     
                                         
                                
               
                          
                                             
                               
                            
                
                                                 
                                                  
                             
                                    
            
                                             
                                             
                                        
                                                
                                                  
                   
                                          
                                                                             
                                  
              
              
                                     
                                              
                                     
                                                    
                                
                                                                         
                                                     
                                                                                      
                                      
                                                 

/-- Data of the rank-at-most-two spectral slice of a symmetric nonnegative matrix. -/
structure SpectralSlice (hB : B.IsHermitian) (hnn : ∀ i j, 0 ≤ B i j) where
  a : ℝ
  b : ℝ
  u : n → ℝ
  v : n → ℝ
  X : Matrix n n ℝ
  ha : a = lambdaMax hB
  hb : b = max (lambdaSecond hB) 0
  hu_nonneg : ∀ i, 0 ≤ u i
  hu_unit : ∑ i, u i ^ 2 = 1
  hu_eigen : B *ᵥ u = a • u
  hv_sq : ∑ i, v i ^ 2 = if 0 < b then 1 else 0
  hv_ortho : u ⬝ᵥ v = 0
  hv_eigen : B *ᵥ v = b • v
  hX : X = a • vecMulVec u u + b • vecMulVec v v

                                                 
                                                                               
                           
                                                               
                    
                             
                               
                               
                                  
                                                  
                      
                       
                          
            
            
                                                                         
               
                                    
                      
                    
                     
                 
                                    
                            
                                    
                                    
                 
      
                       
            
            
            
                                       
               
                                              
                      
                    
                     
                      
                         
                         
                     

namespace SpectralSlice

variable {hB : B.IsHermitian} {hnn : ∀ i j, 0 ≤ B i j}
variable (s : SpectralSlice hB hnn)

lemma a_nonneg : 0 ≤ s.a := by
  have huu : s.u ⬝ᵥ s.u = 1 := by simpa [sum_sq_eq_dotProduct] using s.hu_unit
  have : s.a = s.u ⬝ᵥ B *ᵥ s.u := by
    rw [s.hu_eigen, dotProduct_smul, smul_eq_mul, huu, mul_one]
  rw [this, dot_mulVec_eq_sum_sum]
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => ?_
  exact mul_nonneg (mul_nonneg (s.hu_nonneg i) (hnn i j)) (s.hu_nonneg j)

lemma b_nonneg : 0 ≤ s.b := by
  rw [s.hb]
  exact le_max_right _ _

                                                          
                                            

/-- **SP04.** The spectral slice is positive semidefinite. -/
lemma posSemidef : s.X.PosSemidef := by
  have huu : (vecMulVec s.u s.u).PosSemidef := by
    simpa using posSemidef_vecMulVec_self_star (R := ℝ) s.u
  have hvv : (vecMulVec s.v s.v).PosSemidef := by
    simpa using posSemidef_vecMulVec_self_star (R := ℝ) s.v
  rw [s.hX]
  exact (huu.smul s.a_nonneg).add (hvv.smul s.b_nonneg)

                      
                                                               
       
                                                      
      

                                                         
                                      
           
                                
                                            
                                                 
                         
              
                                          
                 
                                                          
                                                                         
                                    
                                                                            
                                                           
                                                    
                                                     
            

                                                             
                                                                              
                                                                                                
                                                                              
                   
        
                                                                  
                       

                                                               
                                                                              
                                                                    
                                                
                                                                    
                                                                    
                                                                    
                        
                                                                                
                                 
                                                                                                
                                                                                          
                                                   
                   
        
                                                                  
                       

                                         
                                          
                                                                 
                                                           

                                            
                                                                 
                                                           

                                                             
                                    

                                                            
                                     
           
                                                        
                                               
                                             
                                                                                   
             
                                                              
                                                                                           
                                             
                                                                
                                          
                        
                                                  
                                           
                                                 
                                      
                             
                                        
                                           
                                                        
                                    
         
                                                             
                                                                                         
                                          
                                                            

                                                                       
                                                       
                        
                                                     
                        

                                                   
                                              
                                                 

                                                     
                                                      
              
                                                       

                                                                
                                                             
                                                                                
                                                                                
                                                                           
                                
                                    
                                                         
                                                               
                                              
      
                                                                   
                                                           
                                                                             
                                                           
                                                                      
                                         

                                                                  
                                                                                 
                                       
           
               
       
                                           
           
                           
              
                                                              
           
                                                                      
                                         
             
                              
           
                                     

                                                               
                                                                                        
                                                                                    
                                                                                               
                                                                                
                                             
                                                               
                     
                                                                             
                        
               
                                        
                                       
                                            
                                                              
                                                                 
                                                              
                                                                                
             
                                 

end SpectralSlice

/-! ### SP09–SP10 — support bound and Frobenius Cauchy–Schwarz -/

section Support

variable {G : SimpleGraph n} [DecidableRel G.Adj]

                      
                                                                                
                                                                       
                                                        
                                                     
                                              
                                                         
                                 
                                                                     
                                           
                          
                                                                                 
                    
                                                                     
                        
               
                                                 
                                                            

                      
                                                                             
                                                         
                                         
                             
                                                                           
                        
                    
                                               
                                              
                          
            
                       
                                                                                   
                     
                            
                                                                    
                                                     
            
                                                                       
                   
                                                                    
                                       
            
                                   
                                                                           
                              
                                             
                      
            
                                                                                   
                                                           
                                                                          
                                        
                               
                   
                                                                               
            
                           
                                                     
                                    
                         
                                 

end Support

/-! ### SP11–SP12 — algebra of the weighted inequality -/

namespace SpectralSlice

variable {hB : B.IsHermitian} {hnn : ∀ i j, 0 ≤ B i j}
variable (s : SpectralSlice hB hnn)
variable {G : SimpleGraph n} [DecidableRel G.Adj]

include s hnn

                                                                       
                                
                            
                                              
                                          
                                     
                      
                            
                                      
                         
                                                                            
                                                  
                    
                                              
                                             
                                  
                       
                                                                          
                                                
                  
                          
                              
                        
                           
                                                            
                                                                      
                          
                         
                           
                          
                      
                                                                 
                          
               
               
                          
                               
                 
                                                                   
                                                                           
                                                      
                                                  
                                   
                                  
                     
                                                                                 
                                                                    
                                                     
                                                     
                               
                                                                            
                                        
                                                                 
                                                
                                                                             
                        
                       
                                                                                     
                                                                                          
                                                          
                                           
                                       
                                                               
                                          
                                                                        
                         
                    
            
                                                      

end SpectralSlice

                                        
                                                         
                                                 
                            
                                              
                                       
                                                               

end BN
