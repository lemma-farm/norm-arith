/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

VENDORED BASE MODULE.  This file is copied verbatim (apart from its import
paths and this header) from the author's Version 2.0 formalization at
https://github.com/DiarHaidary/Nelson-Nguyen-conjecture-upper-bound-palomar
(`SparseFockFormal/ParsevalFrame.lean`).  The sketch distribution, the Parseval-frame
encoding of `U`, the finite-probability API and the operator-norm/trace
bridge are unchanged between Version 2.0 and Version 3.0 of the manuscript,
so they are reused rather than reproved.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace SparseFock

namespace ParsevalFrame

open scoped BigOperators InnerProductSpace

noncomputable section

/-- The real Euclidean space used for the rows of the input matrix. -/
abbrev EVec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Squared Euclidean norm, kept as an inner product so all finite sums remain exact. -/
def normSq {d : ℕ} (x : EVec d) : ℝ := ⟪x, x⟫_ℝ

theorem normSq_eq_norm_sq {d : ℕ} (x : EVec d) : normSq x = ‖x‖ ^ 2 := by
  exact real_inner_self_eq_norm_sq x

/-- The rank-one matrix `x yᵀ`. -/
def outer {d : ℕ} (x y : EVec d) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b ↦ x a * y b

       
                                                          
                                    

                                                                     
                                                
                                           
         
                                                

                                                                             
structure Frame (n d : ℕ) where
  u : Fin n → EVec d
  parseval : (∑ i, outer (u i) (u i)) = (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The `n × d` matrix whose row `i` is `u i`. -/
def rowMatrix {n d : ℕ} (u : Fin n → EVec d) : Matrix (Fin n) (Fin d) ℝ :=
  fun i a ↦ u i a

                                                        
                                                                              
                        

                                                                                        
def applyMatrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : EVec d) : EVec d :=
  WithLp.toLp 2 (A.mulVec fun a ↦ x a)

@[simp]
theorem applyMatrix_one {d : ℕ} (x : EVec d) :
    applyMatrix (1 : Matrix (Fin d) (Fin d) ℝ) x = x := by
  ext a
  simp [applyMatrix]

                                                                                               
                                                                   
                                                      
                                                                                  
             
           
            
           
                                                                              
           
            
           
                                                                              

                                                           
                                               
                                       
                                                

                                                         
def analyze {n d : ℕ} (F : Frame n d) (x : EVec d) (i : Fin n) : ℝ :=
  ⟪F.u i, x⟫_ℝ

/-- Synthesis using only coefficients whose indices lie in `S`. -/
def synthesize {n d : ℕ} (F : Frame n d) (S : Finset (Fin n))
    (a : Fin n → ℝ) : EVec d :=
  ∑ i ∈ S, a i • F.u i

/-- The positive partial frame operator `Σ_{i∈S} uᵢuᵢᵀ`. -/
def partialFrameOperator {n d : ℕ} (F : Frame n d) (S : Finset (Fin n)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun a b ↦ ∑ i ∈ S, F.u i a * F.u i b

theorem synthesize_inner {n d : ℕ} (F : Frame n d) (S : Finset (Fin n))
    (a : Fin n → ℝ) (x : EVec d) :
    ⟪synthesize F S a, x⟫_ℝ = ∑ i ∈ S, a i * ⟪F.u i, x⟫_ℝ := by
  simp [synthesize, sum_inner, real_inner_smul_left]

/-- The partial frame operator applied to `x` is synthesis of its analysis coefficients. -/
theorem partialFrameOperator_mulVec {n d : ℕ} (F : Frame n d)
    (S : Finset (Fin n)) (x : EVec d) :
    applyMatrix (partialFrameOperator F S) x = synthesize F S (analyze F x) := by
  ext a
  simp only [applyMatrix, PiLp.toLp_apply, partialFrameOperator, Matrix.mulVec, dotProduct,
    synthesize, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    PiLp.inner_apply, analyze, Pi.smul_apply, smul_eq_mul, Real.inner_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Exact reconstruction by a Parseval frame. -/
theorem reconstruct {n d : ℕ} (F : Frame n d) (x : EVec d) :
    synthesize F Finset.univ (analyze F x) = x := by
  rw [← partialFrameOperator_mulVec]
  have hpartial : partialFrameOperator F Finset.univ =
      (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext a b
    have hab := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M a b) F.parseval
    simpa [partialFrameOperator, Matrix.sum_apply, outer] using hab
  rw [hpartial]
  exact applyMatrix_one x

/-- Parseval's exact energy identity. -/
theorem analysis_energy_eq {n d : ℕ} (F : Frame n d) (x : EVec d) :
    (∑ i, (analyze F x i) ^ 2) = normSq x := by
  have hrec := reconstruct F x
  calc
    (∑ i, (analyze F x i) ^ 2) =
        ⟪synthesize F Finset.univ (analyze F x), x⟫_ℝ := by
          rw [synthesize_inner]
          apply Finset.sum_congr rfl
          intro i hi
          simp [analyze, pow_two]
    _ = ⟪x, x⟫_ℝ := by rw [hrec]
    _ = normSq x := rfl

                                                      
                            
                                                                      
                  
                                                   
      
                                    
                                   
                                                                          
                                          

                                                
                                    
                                                                       
                     
                                                        
                                    
                                           
                                                
                       
                                               
                                                                       
                                     
             
                                
                                                       
        
                                                             
                                
            
                                                
                                                     
                                                         
                                   
                                                 
                                                  
                                                     
                    
                                    

                                                                     
                                                                    
                            
                                         
                                         
                                
                                                        
                                            
           

                                                                  
                                                                  
                     
                                    
                             
                                 

                                                                       
                                                       
                                                                  
                                       
                                                                      
                                  
      
                                           
                                                                          
                                                             
                                         

end

end ParsevalFrame

end SparseFock
