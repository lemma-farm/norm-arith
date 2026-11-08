/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Coordinate embedding and projection between `ℓ^p_n` and `ℓ^p_m`

Elementary facts about the finite-dimensional sequence spaces `ℓ^p_k`, and two
coordinate maps relating `ℓ^p_m` to the lower-dimensional `ℓ^p_n` along the
inclusion `Fin.castLE : Fin n → Fin m` (for `n ≤ m`):

* `piLp_norm_mono` — the `L^p` norm is monotone under coordinatewise domination
  of the norms;
* `finrank_piLp` — the dimension of `ℓ^p_k` is `k`;
* `projFin` keeps the first `n` coordinates;
* `padFin` extends a vector by zeros in the remaining coordinates.

Both maps are contractions (`norm_projFin_clm_le`, `norm_padFin_clm_le`;
`padFin` is in fact an isometry), and `projFin ∘ padFin = id`. They are used
to build finite-rank approximants and compressions: in the diagonal-operator
example (`SNumbers.Examples.DiagonalMatrices`) and in the determinant
quantities `Δₖ(S)` (`SNumbers.MaxDifference`).

This is generic `PiLp` material (no s-number content); it is a candidate for
upstreaming to `Mathlib.Analysis.Normed.Lp.PiLp`.
-/

universe u

open scoped ENNReal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ## Norm monotonicity and the dimension of `ℓ^p_k` -/

/-- If `‖x i‖ ≤ ‖y i‖` for every coordinate `i`, then `‖x‖ ≤ ‖y‖` in `PiLp p`.
Proved by the `p = ∞` (suprema) and `1 ≤ p.toReal` (sums of `p`-th powers)
cases of the explicit norm formula. -/
lemma piLp_norm_mono {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] {x y : PiLp p β}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases p.dichotomy with (rfl | hp)
  · rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
    exact ciSup_mono (Finite.bddAbove_range _) h
  · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
    rw [PiLp.norm_eq_sum hp0, PiLp.norm_eq_sum hp0]
    have hsum : (∑ i, ‖x i‖ ^ p.toReal) ≤ ∑ i, ‖y i‖ ^ p.toReal :=
      Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (h i) hp0.le
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
      hsum (one_div_nonneg.mpr hp0.le)

omit [Fact (1 ≤ p)] in
/-- The dimension of `ℓ^p_k = PiLp p (Fin k → 𝕜)` is `k`. -/
lemma finrank_piLp (k : ℕ) :
    Module.finrank 𝕜 (PiLp p (fun _ : Fin k => 𝕜)) = k := by
  rw [(WithLp.linearEquiv p 𝕜 (Fin k → 𝕜)).finrank_eq, Module.finrank_pi 𝕜, Fintype.card_fin]

/-! ## The coordinate maps -/

/-- The **coordinate projection** `ℓ^p_m → ℓ^p_n` keeping the first `n`
coordinates (along `Fin.castLE h`). -/
noncomputable def projFin (h : n ≤ m) :
    PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin n => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (fun j => x (Fin.castLE h j))
      map_add' := fun x y => by ext j; simp
      map_smul' := fun c x => by ext j; simp }

@[simp] lemma projFin_apply (h : n ≤ m) (x : PiLp p (fun _ : Fin m => 𝕜)) (j : Fin n) :
    (projFin (p := p) h x) j = x (Fin.castLE h j) := rfl

/-- The **coordinate embedding** `ℓ^p_n → ℓ^p_m` extending by zeros past the
first `n` coordinates. -/
noncomputable def padFin :
    PiLp p (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp p (fun i => if hi : (i : ℕ) < n then y ⟨i, hi⟩ else 0)
      map_add' := fun y z => by ext i; by_cases hi : (i : ℕ) < n <;> simp [hi]
      map_smul' := fun c y => by ext i; by_cases hi : (i : ℕ) < n <;> simp [hi] }

@[simp] lemma padFin_apply (y : PiLp p (fun _ : Fin n => 𝕜)) (i : Fin m) :
    (padFin (p := p) (m := m) y) i = if hi : (i : ℕ) < n then y ⟨i, hi⟩ else 0 := rfl

/-- Embedding the first `n` coordinates back gives the **coordinate truncation**
`Pₙ = padFin ∘ projFin` on `ℓ^p_m`: it keeps the first `n` coordinates and zeros
the rest. -/
lemma padFin_projFin_apply (h : n ≤ m) (x : PiLp p (fun _ : Fin m => 𝕜)) (i : Fin m) :
    (padFin (projFin (p := p) h x)) i = if (i : ℕ) < n then x i else 0 := by
  by_cases hi : (i : ℕ) < n
  · rw [padFin_apply, dif_pos hi, projFin_apply, if_pos hi]
    congr 1
  · rw [padFin_apply, dif_neg hi, if_neg hi]

                                                                         
                                                                     
                                      
                                    
                                               
                                                 
                               
                                                   
                                 
                                                                                                  
                                                      
                                                   
                                                                                               
                                 
                             
                                                            
                                                                        
                                                                         
             
                                                                      
                                                       

                                                         
                                                                            
                                                               
                                           

                                                                                 
                                                                               
                                                             
                                                                          
         

                                                                         
                                                                              
                     
                                                                    
                                            
                                    
                                               
                                                 
                               
                                                   
                                 
                               
                                      
                                                                                 
                                                       
                                                     
                                                      
                                                   
                  
           
                                                                        
                                                 
                                                             
                                                               
                  
                                            
                                                                                  
                                                                       
                                                                             
                                                               

                                                        
                                      
                                                         
                                                               
                                          

end SNumbers
