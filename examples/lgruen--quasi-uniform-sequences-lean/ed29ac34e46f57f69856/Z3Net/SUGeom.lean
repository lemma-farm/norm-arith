module
public import Mathlib
public import Z3Net.SURows
public import Z3Net.SUThm1
public import Z3Net.TwoGeom

@[expose] public section

/-!
# Entry U, part 6: digits, cells and carries of `𝒫^s_{k,q}` (Lemma S_s, geometric part)

The point `Upoint s q k v` has, in coordinate `c`, digits `D_c(v) = UGen s q k c · v`: the first
`k` are the cell digits `v_{ck+i}` (graph form), digit `k + r` is `∑_{d,l} Φ'_cd[r,l] v_{dk+l}`.
Adapted from the 4D entry (`Z3Net/D4Geom.lean`) to `s` coordinates; carry classes are capped at
`min(s-2, k-1)`.
-/

namespace Z3NetU.Proofs

open Finset Matrix Z3NetU

noncomputable section

variable (s q : ℕ)

                                                                  
                                                                                                 

                                                                
                                                                                                 

                                                                                   
                                                                             
                            

                                                                                   
                                        
                                                                                                         
                        

                                       

variable [NeZero q]

/-- Total digit accessor (as natural numbers). -/
def dv (k : ℕ) (D : Fin (s * k) → ZMod q) (j : ℕ) : ℕ :=
  if h : j < s * k then (D ⟨j, h⟩).val else 0

                                                                               
                      
                       
                             

                                                     
def tail (k : ℕ) (D : Fin (s * k) → ZMod q) : ℕ :=
  ∑ j ∈ Ico (k + 1) (s * k), dv s q k D j * q ^ (s * k - 1 - j)

                                                                        
                                            
             
                                                                          
                                                                                              
                                              
                                
                             
                                                                    

lemma coord_split (k : ℕ) (hsk : k + 1 ≤ s * k) (D : Fin (s * k) → ZMod q) :
    ∑ j : Fin (s * k), (D j).val * q ^ (s * k - 1 - (j : ℕ)) =
      q ^ (s * k - k) * (∑ i ∈ range k, dv s q k D i * q ^ (k - 1 - i)) +
        q ^ (s * k - k - 1) * dv s q k D k + tail s q k D := by
  rw [show ∑ j : Fin (s * k), (D j).val * q ^ (s * k - 1 - (j : ℕ)) =
      ∑ j : Fin (s * k), dv s q k D j * q ^ (s * k - 1 - (j : ℕ)) by
        refine sum_congr rfl fun j _ => ?_; simp [dv, j.isLt],
    Fin.sum_univ_eq_sum_range (fun j => dv s q k D j * q ^ (s * k - 1 - j)),
    ← sum_range_add_sum_Ico _ (show k ≤ s * k by omega),
    sum_eq_sum_Ico_succ_bot (show k < s * k by omega), tail, mul_sum]
  rw [show s * k - 1 - k = s * k - k - 1 by omega]
  have : ∑ i ∈ range k, dv s q k D i * q ^ (s * k - 1 - i) =
      ∑ i ∈ range k, q ^ (s * k - k) * (dv s q k D i * q ^ (k - 1 - i)) := by
    refine sum_congr rfl fun i hi => ?_
    simp only [mem_range] at hi
    rw [show s * k - 1 - i = (s * k - k) + (k - 1 - i) by omega, pow_add]; ring
  rw [this]; ring

/-! ## Cells and carries -/

/-- Level `i` digit (as a natural number) of the cell of axis `d`. -/
def ad (k : ℕ) (v : Fin (s * k) → ZMod q) (d : Fin s) (i : ℕ) : ℕ :=
  if h : i < k then (v (ix k d ⟨i, h⟩)).val else 0

lemma ad_lt (k : ℕ) (v : Fin (s * k) → ZMod q) (d : Fin s) (i : ℕ) : ad s q k v d i < q := by
  unfold ad; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_neZero q

/-- The cell `n_d ∈ [0, q^k)` of axis `d`. -/
def cellN (k : ℕ) (v : Fin (s * k) → ZMod q) (d : Fin s) : ℕ :=
  ∑ i ∈ range k, ad s q k v d i * q ^ (k - 1 - i)

                                                                                          
                                                                          

                                                                
                                                                                      
                                     
                             
         
                                                         
                                             
                             

lemma cellN_digit (hq : 1 < q) (k : ℕ) (v : Fin (s * k) → ZMod q) (d : Fin s) (l : Fin k) :
    cellN s q k v d / q ^ (k - 1 - (l : ℕ)) % q = (v (ix k d l)).val := by
  have hl := l.isLt
  unfold cellN
  rw [Z3Net.Two.digit_extract_be q hq k _ (ad_lt s q k v d) _ (by omega),
    show k - 1 - (k - 1 - (l : ℕ)) = l by omega]
  simp [ad, hl]

lemma zmod_digit (hq : 1 < q) (k : ℕ) (v : Fin (s * k) → ZMod q) (d : Fin s) (l : Fin k) :
    v (ix k d l) = ((cellN s q k v d / q ^ (k - 1 - (l : ℕ)) : ℕ) : ZMod q) := by
  rw [← ZMod.natCast_mod, cellN_digit s q hq, ZMod.natCast_zmod_val]

                                                                                         
                                                                                           
                                                      

                                                                                                   
                                          
lemma carry_digits (hq : 1 < q) (k : ℕ) (v w : Fin (s * k) → ZMod q) (d : Fin s)
    (h : cellN s q k w d = (cellN s q k v d + 1) % q ^ k) (l : Fin k) :
    w (ix k d l) - v (ix k d l) =
      if q ^ (k - 1 - (l : ℕ)) ∣ cellN s q k v d + 1 then 1 else 0 := by
  have hl := l.isLt
  set t := k - 1 - (l : ℕ) with ht
  have htk : t < k := by omega
  rw [zmod_digit s q hq k w, zmod_digit s q hq k v, h, ← ht]
  have e1 : (cellN s q k v d + 1) % q ^ k / q ^ t = (cellN s q k v d + 1) / q ^ t % q ^ (k - t) := by
    rw [show q ^ k = q ^ t * q ^ (k - t) by rw [← pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self]
  rw [e1, ← ZMod.natCast_mod, Nat.mod_mod_of_dvd _ (dvd_pow_self q (by omega)), ZMod.natCast_mod,
    Nat.succ_div]
  split_ifs <;> simp

                                                                       
                                                                                        

                                                                                   

                                                                 
                                         
             
                                           
           
                                        
                                                                                   
                                    

                                                                                        
                     
                                                                                       
                                        
                                                                                       

                                                                                 
                                                           
                                                              
            
                                      
                                                            
                                          
                                                           
                                             
                                                             

                                                                                  
                                                           
                                                                 
            
                                             
                                       

                                                                                 
                                                                            
           
                                                     

                                          

                                                            
                                                                               
                                    
                                                                                              
                                                                  
                                                        
                                                                                                                
             
                                     
                                                              

                                                                                            
             
                      
         
       
                        

                                        
                                                                     

                                                                                        
                                                   
                                                                                    
                                                                                     
                                                                                                  
                        
                                                                             
                                                                         
                                             
                                        
                                    
                                                                                         
           
              
                                    
                               
                                       
                           
                                                              

                                                                                              
                     
                                                                                     
                                                                                   
                        
                                                                                 
                     
                                                             
                     
                             
                                                             

end

end Z3NetU.Proofs
