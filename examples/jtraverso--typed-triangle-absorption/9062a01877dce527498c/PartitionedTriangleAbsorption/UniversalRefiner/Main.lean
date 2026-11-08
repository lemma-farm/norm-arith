/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Loads
                                                                     
public import Mathlib.Data.Nat.Log

/-!
# The universal bounded ordinary refiner (one-part triangle family)

`exists_universal_refiner`: for a finite host `G` on `n` vertices of minimum degree at least
`3n/4`, a reserve `X ⊆ E(G)` of maximum degree at most `2ρn`, and parameters
`0 < λ ≤ 1/64`, `0 < ρ`, `2^24 ρ ≤ λ²`, `ρn ≥ 1`, `λn ≥ 256`, there is one fixed library
`P` (indexed by `indices`) and one fixed remainder `R ⊆ E(G) \ X` such that every integrally
divisible `L ⊆ X` is exactly partitioned by `R ∪ L`-covering disjoint pieces of the library
(`RefinerAssembly.RefinesReserve`), with bounded pieces, `Δ(R) ≤ 4λn`,
`|indices| ≤ 1224 ρ n²`, and total incidence at most `4096 λn` at every vertex.

The hub hierarchy is the binary heap of `UniversalRefiner.Heap` with
`2^p = 2^⌊log₂ ⌊128ρn/λ⌋⌋`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset AntiEdgeSelection OnePart

/-- Choice of the number `p` of interior hub levels. -/
theorem exists_heap_height (n : ℕ) (lam rho : ℝ) (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64)
    (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2) (hn1 : 1 ≤ rho * n) :
    ∃ p : ℕ, 1 ≤ p ∧ 2 ^ (p + 1) ≤ n ∧ 64 * rho * n ≤ lam * 2 ^ p ∧
      lam * 2 ^ p ≤ 128 * rho * n := by
  set y : ℝ := 128 * rho * n / lam with hy
  have hy0 : 0 ≤ y := by positivity
  have hy8 : 8192 ≤ y := by
    rw [hy, le_div_iff₀ hlam]
    nlinarith
  set m := ⌊y⌋₊ with hm
  have hm2 : 2 ≤ m := Nat.le_floor (by norm_num; linarith)
  set p := Nat.log 2 m with hp
  have hp1 : 1 ≤ p := Nat.log_pos (by norm_num) hm2
  have hpow : 2 ^ p ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hlt : m < 2 ^ (p + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hpowR : (2 : ℝ) ^ p ≤ y := by
    calc (2 : ℝ) ^ p = ((2 ^ p : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (m : ℝ) := by exact_mod_cast hpow
      _ ≤ y := Nat.floor_le hy0
  have hltR : y < 2 * (2 : ℝ) ^ p := by
    have h1 := Nat.lt_floor_add_one y
    have h2 : ((m + 1 : ℕ) : ℝ) ≤ ((2 ^ (p + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at h2
    rw [pow_succ] at h2
    linarith
  have hlam2 : lam ^ 2 ≤ lam / 64 := by nlinarith
  have hrl : 256 * rho ≤ lam := by nlinarith
  refine ⟨p, hp1, ?_, ?_, ?_⟩
  · have : (2 : ℝ) ^ (p + 1) ≤ n := by
      rw [pow_succ]
      have h1 : 2 * y ≤ n := by
        rw [hy, mul_div_assoc', div_le_iff₀ hlam]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      linarith
    exact_mod_cast this
  · have := (div_lt_iff₀ hlam).mp (show 128 * rho * n / lam < 2 * 2 ^ p by rw [← hy]; exact hltR)
    linarith
  · have := (le_div_iff₀ hlam).mp (show (2 : ℝ) ^ p ≤ 128 * rho * n / lam by rw [← hy]; exact hpowR)
    linarith


/-- Real estimate for the size of the hierarchy. -/
theorem size_bound_real (xc S p n : ℕ) (lam rho : ℝ) (hlam : 0 < lam) (hrho : 0 < rho)
    (hscale : 2 ^ 24 * rho ≤ lam ^ 2) (hS : S ≤ xc + 2 ^ (p + 1) * 2 ^ p)
    (hX : (xc : ℝ) ≤ rho * (n : ℝ) ^ 2) (hP2 : lam * 2 ^ p ≤ 128 * rho * n) :
    (S : ℝ) ≤ 2 * rho * (n : ℝ) ^ 2 := by
  set P2 : ℝ := (2 : ℝ) ^ p with hP2def
  have h1 : (S : ℝ) ≤ xc + 2 * P2 * P2 := by
    have : ((xc + 2 ^ (p + 1) * 2 ^ p : ℕ) : ℝ) = xc + 2 * P2 * P2 := by
      push_cast; rw [pow_succ]; ring
    rw [← this]; exact_mod_cast hS
  have h2'' : 2 * P2 * P2 * lam ^ 2 ≤ rho * (n : ℝ) ^ 2 * lam ^ 2 := by
    have hlp0 : 0 ≤ lam * P2 := by positivity
    have hsq : (lam * P2) ^ 2 ≤ (128 * rho * n) ^ 2 := pow_le_pow_left₀ hlp0 hP2 2
    nlinarith
  have h3 : 2 * P2 * P2 ≤ rho * (n : ℝ) ^ 2 :=
    le_of_mul_le_mul_right h2'' (by positivity)
  linarith

/-- Real estimate for the root load. -/
theorem root_bound_real (n p D N : ℕ) (lam rho : ℝ) (hlam : 0 < lam) (hlam64 : lam ≤ 1 / 64)
    (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2) (hn2 : 256 ≤ lam * n)
    (hnR : (4 : ℝ) ≤ n) (hP1 : 64 * rho * n ≤ lam * 2 ^ p) (hP2 : lam * 2 ^ p ≤ 128 * rho * n)
    (hDR : (D : ℝ) ≤ 2 * rho * n) (hNR : (N : ℝ) ≤ 34 * rho * (n : ℝ) ^ 2 + 2) :
    ((2 * D + 10 * ((n / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) + 8 +
      12 * ((N + 1) / n + 1) : ℕ) : ℝ) ≤ lam * n := by
  set P2 : ℝ := (2 : ℝ) ^ p with hP2def
  have hnpos : (0 : ℝ) < n := by linarith
  have hlam2 : lam ^ 2 ≤ lam / 64 := by nlinarith
  have hrl : 2 ^ 30 * rho ≤ lam := by nlinarith
  have hrn : rho * n ≤ lam * n / 2 ^ 30 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  set A : ℝ := ((n / 2 ^ p : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have hAP : A * P2 ≤ n := by
    have : ((n / 2 ^ p * 2 ^ p : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n (2 ^ p)
    push_cast at this; exact this
  have hAD : A * (2 * rho * n) ≤ lam * n / 32 := by
    rw [le_div_iff₀ (by norm_num)]
    have : A * (64 * rho * n) ≤ A * (lam * P2) := mul_le_mul_of_nonneg_left hP1 hA0
    nlinarith
  set B : ℝ := (((N + 1) / n : ℕ) : ℝ) with hB
  have hB0 : 0 ≤ B := Nat.cast_nonneg _
  have hBn : B * n ≤ N + 1 := by
    have : (((N + 1) / n * n : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (N + 1) n
    push_cast at this; exact this
  have hBR : B ≤ 34 * rho * n + 1 := by
    have e : (34 * rho * n + 1) * n = 34 * rho * (n : ℝ) ^ 2 + n := by ring
    have : B * n ≤ (34 * rho * n + 1) * n := by rw [e]; linarith
    exact le_of_mul_le_mul_right this hnpos
  have hP44 : 44 * P2 ≤ lam * n / 2000 := by
    rw [le_div_iff₀ (by norm_num)]
    have h1 : lam * (44 * P2 * 2000) ≤ 11264000 * (rho * n) := by linarith
    have h2' : 11264000 * rho ≤ lam * lam := by nlinarith
    have h3 : 11264000 * (rho * n) ≤ lam * (lam * n) := by
      have := mul_le_mul_of_nonneg_right h2' hnpos.le
      linarith
    exact le_of_mul_le_mul_left (h1.trans h3) hlam
  have hrcast : ((2 * D + 10 * ((n / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) + 8 +
      12 * ((N + 1) / n + 1) : ℕ) : ℝ) =
      2 * D + 10 * ((A + 1) * D) + 22 * (2 * P2) + 8 + 12 * (B + 1) := by
    simp only [hA, hB, hP2def]
    push_cast
    ring
  rw [hrcast]
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have h1 : (A + 1) * D ≤ lam * n / 32 + 2 * rho * n := by
    have : (A + 1) * D ≤ (A + 1) * (2 * rho * n) := mul_le_mul_of_nonneg_left hDR (by linarith)
    have e : (A + 1) * (2 * rho * n) = A * (2 * rho * n) + 2 * rho * n := by ring
    linarith
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

                                                  
                                                                         
                                                                
                                                             
                                     
                                                                       
                                                  
                                                                                     
                                                   
                                                                             
                                       
                                                                               
                                                             
                                                                                
                                               
                                                                  
                                                                                              
                                 
                                                                                           
                                       
                                       
                        
                                                                               
         
                                                 
                                         
                                                                
                                                 
                                               
                                             
                                               
                                                   
                     
                                     
                                 
                                                   
                                
           
                          
                            
                                                             
                                   
                                                  
                                                                        
                                    
                                                                      
                                                                  
                        
                                                      
                                          
                                                                          
                                                                          
               
                                                                                              
                                                                           
                 
                   
             
                          
                                                                
                                                                 
                                               
                                                                       
                                                          
                                                                   
                                                       
                                                       
            
                                                                   
                                          
                                                                                        
                                                                                             
             
              
                                                                                              
                                      
                                                             
                                                                                               
           
                                                       
                                                                                         
                                                                    
                                                                                     
                                                            
                                                                          
                                                       
                                                                
                                             
         
                                    
              
                                                                                         
                     
                                                              
                                                                                         
                                           
                                               
              
            
                       
                                     
                       
                                                                  
                                                           
                                                   
                                                         
                                                                        
                                    
                                          
                                                        
                                                                                               
                                                            
                        
                                                                        
                                                                                    
                                                                                           
                          
                                                             
           
                                                                                   
                                           
                                      
                                                                    
                                 
           
                                                               
                                                                              
                                                           
                                                                                       
                                                                                            
                                                                       
                                       

end PartitionedTriangleAbsorption.UniversalRefiner
