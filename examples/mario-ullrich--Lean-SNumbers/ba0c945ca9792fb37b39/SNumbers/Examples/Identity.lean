/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import SNumbers.Approximation
import SNumbers.Examples.ExHelpers
import Mathlib.Analysis.MeanInequalities

/-!
# Example: s-numbers of the identity embedding `ℓ^q_m → ℓ^p_m`

The identity map `id : ℓ^q_m → ℓ^p_m` between finite-dimensional sequence spaces
with **different** exponents (`p ≤ q`). Its s-numbers are a classical example
(Pietsch, *Eigenvalues and s-numbers*, §11.11).

This is the **unit-diagonal** case of the diagonal operators, and it is kept
self-contained: it depends only on the core s-number theory and the shared
helpers, not on any diagonal machinery. (The general diagonal operator, for all
pairs of exponents, is `SNumbers.Examples.DiagonalMatrices`, which builds on
this file.)

This file develops the case `1 ≤ p ≤ q < ∞`:

* `piLp_norm_restrict_le` / `piLp_norm_le_card_rpow_mul` — the cross-exponent
  norm comparison `‖f‖_p ≤ (card s)^{1/p-1/q} · ‖f‖_q` (via the
  power-mean inequality `Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg`);
* `idEmbed` and `norm_idEmbed` — the embedding and its operator norm
  `‖id‖ = m^{1/p-1/q}` (sharp, attained at the all-ones vector);
* `approximationNumber_idEmbed_le` — the upper bound `aₙ(id) ≤ (m-n)^{1/p-1/q}`
  (hence `sₙ(id) ≤ (m-n)^{1/p-1/q}` for every s-number, via `sₙ ≤ aₙ`);
* `approximationNumber_idEmbed_eq` — the exact value `aₙ(id) = (m-n)^{1/p-1/q}`,
  via the geometric input `exists_norm_ratio_ge_idEmbed` (the classical
  Gelfand-width lower bound, Pietsch §11.11): every subspace of dimension `≥ m-n`
  contains a vector with `p`/`q`-norm ratio `≥ (m-n)^{1/p-1/q}`, proved from the
  flatness / extreme-point lemma `exists_flat_vector` of
  `SNumbers.Examples.ExHelpers`.
-/

universe u

open scoped ENNReal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}

                                                                           
                                                                 
                                                                               
                   
                                                                      
                                                                   
                             
                                                     
                                                      
                                                               
                                                
                                                    
                                                   
                                                              
                   
                   
                                               
                                                                    
                                                                  
                                                                                                 
                                                                
                                                                                                 
                                                               
                                                               
                                                                                      
                                                                                      
                                                
                                              
                                                               
                                                                 
                                                           
                                                        
                                                        
                         
                        
           
                                             
                                              
                                                         
                                                           
                                                
                                                                                              
                              
                                                    
                                                                  
                    

                                                                         
                                                                       
                   
                                                                           
                                                
                                                     
                                                 
                                                               
                                                                                                  
                                               

                                                                     
                                                                  
                                                                                 
                                                   
                          
                                                                                      
                                          
           

                                                                

                                                                                
                               
                                                                      
                                                                    
                                 
                                                     
                                           
                                              

                                                                      
                                                                                  

                                                          
                                          
                                                                          
                                
                                                                                   
                                                
                                                                             
                                                                       
                                                           
                                                        
                                                
                                                                                     
                                                              
                                                            
                                                      
            

                                                                              

                                                                           
                                                                     
                                                                         
                                                                         

                                                                              
                                                   
                                                                            
                                                                               
                                                                
                                                      
                                                                                   
                       
         
                                                                              
               
                                              
                                                               
                                                     
                                                                             
                                                      
       

                                                                            
                                          
                                                                                 
                                                     
                                                         
                                                               
                                                                            
                                                                          
                      
                                                                          
                                     
                                                                                           
                                          
                                                                           
                                                  
                                                                                      
                                                                                           
                  
                                                                     
                                                                  
                             
                                           
                                                   
                                                               
                                                        
               
                                                                                      
                                                                                         
                
                                                                             
                   
                                                                           
                                
                                                 
                                                          
                                                                          
                                                                                                  
                                                
                                                           
                                                                                              
                                                                              
                                                             

                                                           

                                                                        
                                                                             
                                                                              
                                                                            
                                                                            
                                                   
                                                                       
                              

                                                                                  
                                                                                
                                                                                
                                                                                 
private lemma norm_ratio_of_flat {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {k : ℕ} (hk : 1 ≤ k) (w : Fin m → 𝕜)
    (hle : ∀ i, ‖w i‖ ≤ 1)
    (hk_card : k ≤ (Finset.univ.filter (fun i => ‖w i‖ = 1)).card) :
    (k : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
        ‖(WithLp.toLp q w : PiLp q (fun _ : Fin m => 𝕜))‖
      ≤ ‖(WithLp.toLp p w : PiLp p (fun _ : Fin m => 𝕜))‖ := by
  have hpf : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hP : 0 < p.toReal := toReal_pos_of_ne_top hpf
  have hQ : 0 < q.toReal := toReal_pos_of_ne_top hq
  have hPQ : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  set P := p.toReal
  set Q := q.toReal
  set Sp : ℝ := ∑ i, ‖w i‖ ^ P with hSp
  set Sq : ℝ := ∑ i, ‖w i‖ ^ Q with hSq
  have hSpnn : 0 ≤ Sp := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hSqnn : 0 ≤ Sq := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hnp : ‖(WithLp.toLp p w : PiLp p (fun _ : Fin m => 𝕜))‖ = Sp ^ (1 / P) := by
    rw [PiLp.norm_eq_sum hP]
  have hnq : ‖(WithLp.toLp q w : PiLp q (fun _ : Fin m => 𝕜))‖ = Sq ^ (1 / Q) := by
    rw [PiLp.norm_eq_sum hQ]
  rw [hnp, hnq]
  have hkSp : (k : ℝ) ≤ Sp := by
    have hcard_le : ((Finset.univ.filter (fun i => ‖w i‖ = 1)).card : ℝ) ≤ Sp := by
      rw [hSp]
      calc ((Finset.univ.filter (fun i => ‖w i‖ = 1)).card : ℝ)
          = ∑ _i ∈ Finset.univ.filter (fun i => ‖w i‖ = 1), (1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = ∑ i ∈ Finset.univ.filter (fun i => ‖w i‖ = 1), ‖w i‖ ^ P := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Finset.mem_filter] at hi; rw [hi.2, Real.one_rpow]
        _ ≤ ∑ i, ‖w i‖ ^ P :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => Real.rpow_nonneg (norm_nonneg _) _)
    exact le_trans (Nat.cast_le.mpr hk_card) hcard_le
  have hSp_pos : 0 < Sp := lt_of_lt_of_le (by exact_mod_cast hk) hkSp
  have hSqSp : Sq ≤ Sp := by
    rw [hSq, hSp]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h0 : ‖w i‖ = 0
    · simp only [h0, Real.zero_rpow hP.ne', Real.zero_rpow hQ.ne', le_refl]
    · exact Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))
        (hle i) hPQ
  have hexp : 0 ≤ 1 / P - 1 / Q := by
    have : 1 / Q ≤ 1 / P := one_div_le_one_div_of_le hP hPQ
    linarith
  calc (k : ℝ) ^ (1 / P - 1 / Q) * Sq ^ (1 / Q)
      ≤ (k : ℝ) ^ (1 / P - 1 / Q) * Sp ^ (1 / Q) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hSqnn hSqSp (by positivity))
          (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    _ ≤ Sp ^ (1 / P - 1 / Q) * Sp ^ (1 / Q) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg k) hkSp hexp)
          (Real.rpow_nonneg hSpnn _)
    _ = Sp ^ (1 / P) := by rw [← Real.rpow_add hSp_pos]; congr 1; ring

                                                                          
                                                                           
                                                            
                                                                             
                                                   
                                                                                       
                                                                            
                                               
                                                          
                                              
                     
                                                                                     
                                                           
                                                                                        
                                                   
                                                           
                                                                      
                                                       

                                                                          
                                                          
                                                                                 
                                                     
                                                     
                                                                   
                                                    
                       
                                                                 
                                                                                                                                
                                                      
                                                                
                                                                                                                               
                                     
                            
         
                                                                          
                                                                                            
                                                
                                                                         
                         
                                               
                                        
                                                              
                                  
                                                               
                                                    
                                                       

                                                                      
                                                                   
                                  
                                                                                 
                                                     
                                                         
                                                            
                                                                                                      
