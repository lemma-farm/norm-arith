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

/-- **Cross-exponent norm comparison, restricted to a finite support.** For
`1 ≤ p ≤ q` (with `q ≠ ∞`) and `f` supported on a finite set `s`,
`‖f‖_p ≤ (card s)^{1/p - 1/q} · ‖f‖_q`. The power-mean inequality, applied over
the support `s`. -/
lemma piLp_norm_restrict_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) (s : Finset (Fin m)) (f : Fin m → 𝕜)
    (hf : ∀ i ∉ s, f i = 0) :
    ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜))‖
      ≤ (s.card : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
        ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜))‖ := by
  have hpf : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hP : 0 < p.toReal := toReal_pos_of_ne_top hpf
  have hQ : 0 < q.toReal := toReal_pos_of_ne_top hq
  have hPQ : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  set P := p.toReal
  set Q := q.toReal
  rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hQ]
  -- Restrict both sums to the support `s` (the other terms vanish).
  rw [← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
        rw [show (WithLp.toLp p f) i = f i from rfl, hf i hi, norm_zero, Real.zero_rpow hP.ne']),
    ← Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
        rw [show (WithLp.toLp q f) i = f i from rfl, hf i hi, norm_zero, Real.zero_rpow hQ.ne'])]
  set SP : ℝ := ∑ i ∈ s, ‖(WithLp.toLp p f) i‖ ^ P with hSP_def
  set SQ : ℝ := ∑ i ∈ s, ‖(WithLp.toLp q f) i‖ ^ Q with hSQ_def
  have hSP : 0 ≤ SP := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hSQ : 0 ≤ SQ := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hr : 1 ≤ Q / P := (one_le_div hP).mpr hPQ
  have hPQe : P * (Q / P) = Q := by field_simp
  -- Power-mean over `s`: `SP^(Q/P) ≤ (card s)^(Q/P - 1) * SQ`.
  have key : SP ^ (Q / P) ≤ (s.card : ℝ) ^ (Q / P - 1) * SQ := by
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := s) (f := fun i => ‖(WithLp.toLp p f) i‖ ^ P)
      hr (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
    rw [hSP_def, hSQ_def]
    refine h.trans_eq ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Real.rpow_mul (norm_nonneg _), hPQe]
  -- Raise to the power `1/Q` and simplify the exponents.
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hSP _) key
    (le_of_lt (by positivity : (0 : ℝ) < 1 / Q))
  rw [Real.mul_rpow (by positivity) hSQ, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (s.card:ℝ)),
    ← Real.rpow_mul hSP] at h2
  have e1 : Q / P * (1 / Q) = 1 / P := by field_simp
  have e2 : (Q / P - 1) * (1 / Q) = 1 / P - 1 / Q := by field_simp
  rwa [e1, e2] at h2

/-- **Cross-exponent norm comparison** on all of `ℓ^p_m`: for `1 ≤ p ≤ q`
(`q ≠ ∞`), `‖f‖_p ≤ m^{1/p - 1/q} · ‖f‖_q`. Sharp, with equality at the
all-ones vector. -/
lemma piLp_norm_le_card_rpow_mul {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) (f : Fin m → 𝕜) :
    ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜))‖
      ≤ (m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
        ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜))‖ := by
  have h := piLp_norm_restrict_le hpq hq Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- The `L^p` norm of the all-ones vector on `Fin m` is `m^{1/p}`. -/
lemma piLp_norm_const_one {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ‖(WithLp.toLp p (fun _ : Fin m => (1 : 𝕜)))‖ = (m : ℝ) ^ (1 / p.toReal) := by
  have hP : 0 < p.toReal := toReal_pos_of_ne_top hp
  rw [PiLp.norm_eq_sum hP]
  have hsum : (∑ i : Fin m, ‖(WithLp.toLp p (fun _ : Fin m => (1 : 𝕜))) i‖ ^ p.toReal)
      = (m : ℝ) := by simp [Real.one_rpow]
  rw [hsum]

/-! ## Stage 1 — the identity embedding and its operator norm -/

/-- The **identity embedding** `id : ℓ^q_m → ℓ^p_m`: the same underlying vector,
re-measured in the `p`-norm. -/
noncomputable def idEmbed (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    PiLp q (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (WithLp.ofLp x)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

                                                                      
                                                                                  

                                                          
                                          
theorem norm_idEmbed [NeZero m] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) :
    ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ = (m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by
  have hpf : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  refine le_antisymm (opNorm_le_bound _ (by positivity) fun x => ?_) ?_
  · exact piLp_norm_le_card_rpow_mul hpq hq (WithLp.ofLp x)
  · have hb := (idEmbed (𝕜 := 𝕜) (m := m) p q).le_opNorm
      (WithLp.toLp q (fun _ : Fin m => (1 : 𝕜)))
    rw [show idEmbed (𝕜 := 𝕜) (m := m) p q (WithLp.toLp q (fun _ : Fin m => (1 : 𝕜)))
          = WithLp.toLp p (fun _ : Fin m => (1 : 𝕜)) from rfl,
      piLp_norm_const_one hpf, piLp_norm_const_one hq] at hb
    rw [Real.rpow_sub hm, div_le_iff₀ (by positivity)]
    exact hb

/-! ## Stage 2 — the upper bound `aₙ(id) ≤ (m-n)^{1/p-1/q}` for every s-number

Truncating to the first `n` coordinates gives a rank-`≤ n` approximant; the
residual is the embedding on the remaining `m-n` coordinates, of norm
`(m-n)^{1/p-1/q}` by the restricted norm comparison. As the approximation
numbers are the largest s-numbers, the bound holds for every s-number. -/

                                                                              
                                                   
                                                                            
                                                                               
                                                                
                                                      
                                                                                   
                       
         
                                                                              
               
                                              
                                                               
                                                     
                                                                             
                                                      
       

                                                                            
                                          
                                                                                 
                                                     
                                                         
                                                               
                                                                            
                                                                          
                      
                                                                          
                                     
                                                                                           
                                          
                                                                           
                                                  
                                                                                      
                                                                                           
                  
                                                                     
                                                                  
                             
                                           
                                                   
                                                               
                                                        
               
                                                                                      
                                                                                         
                
                                                                             
                   
                                                                           
                                
                                                 
                                                          
                                                                          
                                                                                                  
                                                
                                                           
                                                                                              
                                                                              
                                                             

                                                           

                                                                        
                                                                             
                                                                              
                                                                            
                                                                            
                                                   
                                                                       
                              

                                                                                  
                                                                                
                                                                                
                                                                                 
                                                                           
                                                                   
                          
                                                                    
                                             
                                                         
                                                               
                                                
                                                    
                                                   
                                                              
                   
                   
                                       
                                       
                                                                                        
                                                                                        
                                                                                   
                            
                                                                                   
                            
               
                                
                                                                                   
              
                                                               
                                                                         
                                                        
                                                                          
                                                      
                                                                  
                             
                                                                        
                                                               
                                                     
                                                                     
                            
                 
                                          
                           
                                                                           
                                                                                          
                   
                                     
                                                           
            
                                               
                                                   
                                                                                 
                                                  
                                              
                                                                                    
                                    
                                                                      

                                                                          
                                                                           
                                                            
                                                                             
                                                   
                                                                                       
                                                                            
                                               
                                                          
                                              
                     
                                                                                     
                                                           
                                                                                        
                                                   
                                                           
                                                                      
                                                       

                                                                          
                                                          
                                                                                 
                                                     
                                                     
                                                                   
                                                    
                       
                                                                 
                                                                                                                                
                                                      
                                                                
                                                                                                                               
                                     
                            
         
                                                                          
                                                                                            
                                                
                                                                         
                         
                                               
                                        
                                                              
                                  
                                                               
                                                    
                                                       

                                                                      
                                                                   
                                  
                                                                                 
                                                     
                                                         
                                                            
                                                                                                      
