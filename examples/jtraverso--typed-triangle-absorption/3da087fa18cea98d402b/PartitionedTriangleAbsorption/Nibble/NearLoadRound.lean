/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.Asymptotic

/-! # The near-unit-load physical round (producer)

Parameters `bmax, γ, θ, ε` are fixed first. Then for every sufficiently large
vertex set, every family of distinct physical triangles on an active edge set
`B`, with weights `0 ≤ w ≤ b/n` (`0 < b ≤ bmax`) and edge loads in
`[1-δ, 1+δ]` (`δ ≤ 1/4`), the following holds in the single product space in
which triangle `i` is retained independently with probability `γ w i`:

* the probability that the outcome fails the three round conclusions is `< 1`;
* hence there is an outcome of positive probability satisfying all three at once,
  for which also `B \ E(P) = B' ⊔ W` (exact residual identity).

The packing `P` consists only of retained triangles sharing no edge with another
retained triangle, `Q` is the set of all edges touched by retained triangles,
`B' = B \ Q` and `W = Q \ E(P)`. Nothing in the conclusion is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.Nibble

open BernoulliExposure BernoulliConcentration Finset

theorem cubeWeight_nonneg {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (ω : Fin n → Bool) : 0 ≤ cubeWeight q ω :=
  prod_nonneg fun i _ => by split_ifs; exacts [(hq i).1, by linarith [(hq i).2]]

/-- A good outcome of positive probability exists when the failure probability is `< 1`. -/
theorem exists_pos_weight_of_cubeProb_lt_one {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (P : (Fin n → Bool) → Prop) (h : cubeProb q P < 1) :
    ∃ ω, 0 < cubeWeight q ω ∧ ¬ P ω := by
  classical
  by_contra hne
  push Not at hne
  have hsum : ∑ ω, cubeWeight q ω = 1 := by
    have := cubeMean_eq_sum_prod q (fun _ => (1 : ℝ))
    rw [cubeMean_const] at this
    simpa using this.symm
  rw [cubeProb_def, cubeMean_eq_sum_prod] at h
  have : ∑ ω, cubeWeight q ω * (if P ω then (1 : ℝ) else 0) = ∑ ω, cubeWeight q ω := by
    apply sum_congr rfl
    intro ω _
    by_cases hP : P ω
    · simp [hP]
    · have h0 : cubeWeight q ω = 0 :=
        le_antisymm (not_lt.mp fun hpos => hP (hne ω hpos)) (cubeWeight_nonneg q hq ω)
      simp [h0]
  linarith

                                         
                                                                         
                                                   
                                                                           
                                                                                    
                                              
                                                        
                                         
                                                            
                         
                                                                             
                                                         
                                                            
                                                             
                                                        
                                                                                          
                                               
                                                            
                                                                                              
                                                              
                                                      
                                                  
                                          
                                                        
                                                     
              
               
               
                         
                                           
                                           
               
               
               
               
              
                                              
                   
                                                                                  
                                                         
                                                                                 
                    
                                                                                
                   
                                                    

end PartitionedTriangleAbsorption.Nibble
