/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.BUCSpatialRegularity
public import Planarwave.Analysis.BUCNonlinear
public import Mathlib.Topology.Order.Lattice

@[expose] public section

/-!
# Common bounds for genuine spatial derivative fields

The maximum of derivative norms through order `k` is represented by its
upper-bound predicate. This avoids choosing derivative fields before their
existence is proved. Product rules cost at most `2^k`; a regular trajectory
has a continuous, least such upper bound, suitable for integral Grönwall.
-/

open Set

namespace Planarwave

noncomputable section

universe u v w

variable {E : Type} {F : Type u} {G : Type v} {H : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Every genuine BUC derivative through order `k` has norm at most `A`. -/
def BUCSpatialBound : (k : ℕ) → {F : Type u} →
    [NormedAddCommGroup F] → [NormedSpace ℝ F] → BUC E F → ℝ → Prop
  | 0, _, _, _, f, A => ‖f‖ ≤ A
  | k + 1, F, _, _, f, A => ‖f‖ ≤ A ∧
      ∃ f' : BUC E (E →L[ℝ] F), BUCSpatialBound k f' A ∧
        ∀ x, HasFDerivAt f (f' x) x

namespace BUCSpatialBound

theorem norm_le {k : ℕ} {f : BUC E F} {A : ℝ} (hf : BUCSpatialBound k f A) : ‖f‖ ≤ A := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

theorem nonneg {k : ℕ} {f : BUC E F} {A : ℝ} (hf : BUCSpatialBound k f A) : 0 ≤ A :=
  (norm_nonneg f).trans hf.norm_le

theorem mono {k : ℕ} {f : BUC E F} {A B : ℝ} (hf : BUCSpatialBound k f A) (hAB : A ≤ B) :
    BUCSpatialBound k f B := by
  induction k generalizing F with
  | zero => exact hf.trans hAB
  | succ k ih =>
    obtain ⟨hn, f', hf', hd⟩ := hf
    exact ⟨hn.trans hAB, f', ih hf', hd⟩

theorem of_succ {k : ℕ} {f : BUC E F} {A : ℝ} (hf : BUCSpatialBound (k + 1) f A) :
    BUCSpatialBound k f A := by
  induction k generalizing F with
  | zero => exact hf.1
  | succ k ih =>
    obtain ⟨hn, f', hf', hd⟩ := hf
    exact ⟨hn, f', ih hf', hd⟩

                                                                         
                                                                           
                                
                              
                                                            
             

theorem add {k : ℕ} {f g : BUC E F} {A B : ℝ}
    (hf : BUCSpatialBound k f A) (hg : BUCSpatialBound k g B) :
    BUCSpatialBound k (f + g) (A + B) := by
  induction k generalizing F with
  | zero => exact (norm_add_le _ _).trans (add_le_add hf hg)
  | succ k ih =>
    obtain ⟨hfn, f', hf', hdf⟩ := hf
    obtain ⟨hgn, g', hg', hdg⟩ := hg
    refine ⟨(norm_add_le _ _).trans (add_le_add hfn hgn), f' + g', ih hf' hg', ?_⟩
    intro x
    simpa only [BUC.add_apply] using! (hdf x).add (hdg x)

                                          
                                                                                    
                                 
           
                            
                                                                                              
                
                                  
                                   
                                                                                                
             
                                                            

                                         
                                                                 
                                                                         

                                                                        
theorem bilinear {k : ℕ} {f : BUC E F} {g : BUC E G} {A C : ℝ}
    (hf : BUCSpatialBound k f A) (hg : BUCSpatialBound k g C)
    (B : F →L[ℝ] G →L[ℝ] H) :
    BUCSpatialBound k (BUC.bilinearBUC B f g) ((2 : ℝ) ^ k * ‖B‖ * A * C) := by
  have hA := hf.nonneg
  have hC := hg.nonneg
  induction k generalizing F G H with
  | zero =>
    change ‖BUC.bilinearBUC B f g‖ ≤ _
    simpa only [pow_zero, one_mul] using
      (BUC.norm_bilinearBUC_le B f g).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg
          (norm_nonneg _) (mul_nonneg (norm_nonneg B) hA))
  | succ k ih =>
    have hfk := hf.of_succ
    have hgk := hg.of_succ
    obtain ⟨hfn, f', hf', hdf⟩ := hf
    obtain ⟨hgn, g', hg', hdg⟩ := hg
    have hR := (ih hfk hg' (B.precompR E)).mono
      (B := (2 : ℝ) ^ k * ‖B‖ * A * C) (by
        gcongr; exact ContinuousLinearMap.norm_precompR_le E B)
    have hL := (ih hf' hgk (B.precompL E)).mono
      (B := (2 : ℝ) ^ k * ‖B‖ * A * C) (by
        gcongr; exact ContinuousLinearMap.norm_precompL_le E B)
    refine ⟨?_, BUC.bilinearBUC (B.precompR E) f g' + BUC.bilinearBUC (B.precompL E) f' g,
      ?_, ?_⟩
    · calc
        _ ≤ ‖B‖ * A * C := (BUC.norm_bilinearBUC_le B f g).trans (by gcongr)
        _ ≤ (2 : ℝ) ^ (k + 1) * ‖B‖ * A * C := by
          have hpow : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_right hpow (show 0 ≤ ‖B‖ * A * C by positivity)]
    · convert hR.add hL using 1
      ring
    · intro x
      simpa only [BUC.add_apply, BUC.bilinearBUC_apply] using!
        B.hasFDerivAt_of_bilinear (hdf x) (hdg x)

                                                                                  
                                                             
                                                               
                                                                   
                                                             
      
                                     
            
                       
                       
                                                 
                    

                                                                                           
                                                              
                                                       
                                                
                                   
                                                                                            
                
                
                   
               
                                   
                                                                          
                                            
                             

end BUCSpatialBound

                                                                          
                                                                             
                                                                                    
                                      
                                            
                                                                                    
                                 
                                                                           
                
                                  
                                 
                                                         
              
                                                                                      
              
                                                                     

                                                                                           
                                                                       
                                                                             
                                                                   
                                   
                                                                                                   
                                                 
                                                
          
                                 
                    
                
                                 
                                  
                                                                                      
                  
                                                                   
                                              
                                          
                                              
                                                        
                                                                             

end

end Planarwave
