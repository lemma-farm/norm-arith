/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.
-/
import SparseStackV3.Op.Projection
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt

/-!
# The Euclidean norm on the state space: Cauchy-Schwarz and the triangle inequality

This file supplies, for Version 3.0 of *SparseStack Is an Optimal Oblivious
Subspace Embedding* (Diar Heidary), the metric structure that the majorant
argument of Lemma `new:majorant` uses on the state space of subsection
`new:local`.

The manuscript tensors the local spaces `L²({±1} × [b])` over the sites
`(g,i) ∈ [s] × [n]` and then with `ℝ^d`, and writes `‖·‖` for the resulting
Hilbert norm; it is this `‖·‖` that appears in Proposition `new:cutoff`,
`𝔼 tr E^{2q} = ∑_a ‖M_q^q(v_a ⊗ Ω)‖²`, in the componentwise vector
`w(z)_α = ‖P_α z‖` of the proof of Lemma `new:majorant`, and in the hypothesis
`‖P_α M_q P_β‖ ≤ G_{αβ}` of equation `new:scalar-majorant`.

As in `SparseStackV3.Op.Space` and `SparseStackV3.Op.Projection`, the tensor
product is realized concretely as `Vec d s b n = RawSample s b n → (Fin d → ℝ)`
with the `L²(Ω ; ℝ^d)` inner product `SparseStackV3.Op.ip`; the norm is
therefore simply `nrm hb F = √(nrm2 hb F)`.

Deliberately, **no** `InnerProductSpace` instance is placed on `Vec d s b n`
(the space carries no `NormedAddCommGroup` structure here), so Mathlib's
`inner_mul_le_norm_mul_norm` is unavailable and Cauchy-Schwarz is proved from
scratch: for every real `t` the expansion `nrm2_add_smul`,
`‖F + tG‖² = ‖F‖² + 2t⟨F,G⟩ + t²‖G‖²`, is nonnegative, so the quadratic
`t ↦ ‖G‖² t² + 2⟨F,G⟩ t + ‖F‖²` has nonpositive discriminant
(`discrim_le_zero`), which is `ip_sq_le`; taking square roots gives `abs_ip_le`.

## Main results

* `SparseStackV3.Op.abs_ip_le` — **Cauchy-Schwarz**, `|⟨F,G⟩| ≤ ‖F‖‖G‖`.
* `SparseStackV3.Op.nrm_add_le` — the **triangle inequality**,
  `‖F + G‖ ≤ ‖F‖ + ‖G‖`.
* `SparseStackV3.Op.nrm_sum_le` — its **finite-sum form**,
  `‖∑_i F_i‖ ≤ ∑_i ‖F_i‖`, which is the inequality the proof of
  Lemma `new:majorant` applies to the family expansion `new:families` of the
  operator `new:operator`.
* `SparseStackV3.Op.nrm_P_le` and `SparseStackV3.Op.nrm_sq_eq_sum` — the
  sector decomposition of subsection `new:local` restated for the norm:
  each `P_p` is a contraction, and `‖F‖² = ∑_p ‖P_p F‖²`.
-/

open scoped BigOperators

namespace SparseStackV3.Op

open SparseFock
open SparseFock.SparseStackDistribution
open SparseStackV3.Occupation

variable {d s b n : ℕ}

                              
                                                                                 

                               
                                                                   
                    

                                            
                                                                             
                                 

                                                      

                                                                  
                                         
theorem nrm2_add_smul (hb : 0 < b) (t : ℝ) (F G : Vec d s b n) :
    nrm2 hb (fun z a => F z a + t * G z a)
      = nrm2 hb F + 2 * t * ip hb F G + t ^ 2 * nrm2 hb G := by
  simp only [nrm2]
  rw [ip_add_left hb F (fun z a => t * G z a) (fun z a => F z a + t * G z a),
    ip_add_right hb F F (fun z a => t * G z a),
    ip_add_right hb (fun z a => t * G z a) F (fun z a => t * G z a),
    ip_smul_right hb t F G,
    ip_smul_left hb t G F,
    ip_smul_left hb t G (fun z a => t * G z a),
    ip_smul_right hb t G G,
    ip_comm hb G F]
  ring

                                                                  
                                                   
                                      
                                                   
                  
                                                    
                          
                          
                   
      

                                                         
                                                          
                                                            
                  
                                                                         
      

                        

                                                                          
                     
theorem nrm2_add_smul_nonneg (hb : 0 < b) (F G : Vec d s b n) (t : ℝ) :
    0 ≤ nrm2 hb G * (t * t) + (2 * ip hb F G) * t + nrm2 hb F := by
  calc (0 : ℝ) ≤ nrm2 hb (fun z a => F z a + t * G z a) :=
        nrm2_nonneg hb (fun z a => F z a + t * G z a)
    _ = nrm2 hb F + 2 * t * ip hb F G + t ^ 2 * nrm2 hb G := nrm2_add_smul hb t F G
    _ = nrm2 hb G * (t * t) + (2 * ip hb F G) * t + nrm2 hb F := by ring

/-- **Cauchy-Schwarz, squared form**: `⟨F,G⟩² ≤ ‖F‖²‖G‖²`.  A nonnegative real
quadratic has nonpositive discriminant. -/
theorem ip_sq_le (hb : 0 < b) (F G : Vec d s b n) :
    (ip hb F G) ^ 2 ≤ nrm2 hb F * nrm2 hb G := by
  have hd : discrim (nrm2 hb G) (2 * ip hb F G) (nrm2 hb F) ≤ 0 :=
    discrim_le_zero (nrm2_add_smul_nonneg hb F G)
  rw [discrim] at hd
  nlinarith [hd]

                                                                               
                                             
                                                    
                                           
                 
                                                                
                                           

                                                 

                                                                    
                                                                      
                                                     
                                                                 
                                              
                                               
                                     
                                                               
                                           
                                                                                  
                                      
                                        
                                                             
                                                                       
                              
                                                                     

                                                          
                                                         
                                                        
                 
                                                                         

                        

                                                 
                                                                    
                 

                                         
                                                                  
                                               

                                                                              
                                     
                                                                 
                                                                
                            
                                                    
                                                     

                                            

                                                                        
                                       
                                                                        
                    
                                                                      
                                              
            
                                  
                                  
                     
                                                             
                                              
                                                       
                  
                            
                                  
                                                                        
                                                

                                                                             
                                              
                           
                                                                               
                                                                   
                                    

                                                         

                                                                              
                                                                                
                                                                           
                                                                   
                                                 
                 
                                                       

                                                                    
                                                                             
                                                      
                                                      
                                                                                
                                                    
                                                                              

end SparseStackV3.Op

