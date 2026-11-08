module
public import Mathlib
public import Z3Net.Defs
public import Z3Net.TwoRows

@[expose] public section

/-!
# Theorem 2 (`thm:two`), part 4: digits, cells and carries of `𝒬_{k,p}`

The point `Qpoint p k v` has, in coordinate `c`, digits `D_c(v) = QGen k c · v`: the first `k`
are the cell digits `v_{ck+i}` (graph form), digit `k + r` is `∑_{d,l} Φ_cd[r,l] v_{dk+l}`.
-/

namespace Z3Net.Two

open Finset Matrix

noncomputable section

lemma idx_lt (k : ℕ) (d : Fin 3) (l : Fin k) : (d : ℕ) * k + l < 3 * k := by
  have := d.isLt; have := l.isLt
  calc (d : ℕ) * k + l < (d : ℕ) * k + k := by omega
    _ = ((d : ℕ) + 1) * k := by ring
    _ ≤ 3 * k := Nat.mul_le_mul_right _ (by omega)

/-- The index digit `v_{dk+l}` (level `l` of the cell of axis `d`). -/
def ix (k : ℕ) (d : Fin 3) (l : Fin k) : Fin (3 * k) := ⟨(d : ℕ) * k + l, idx_lt k d l⟩

                                                                             
                                                           
                                                        
                                                             
                                                

                                                                             
                
                                                                                                
      

                                                                             
                
                                                                                      

variable (p : ℕ)

                                                     
                                                                                                   

                                                                  
                                                                               
                                               

                                                                
                                                                                             

                                                                                                   
                                           
                                                                                 
                                             
             
              
                       
                                        

                                                                               
                                  
                                                                                    
                                                                      
                
                                                             
                        
         
                                                                                                           
                          
                                                            
                  
         
             
                      

                                   

                                                                          
                                            
                  
                
                
                                 
                
                                                                                
                                                       
                                                                                         
         

lemma reflect_digits (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range n, f i * p ^ (n - 1 - i) = ∑ t ∈ range n, f (n - 1 - t) * p ^ t := by
  rw [← sum_range_reflect (fun i => f i * p ^ (n - 1 - i)) n]
  refine sum_congr rfl fun t ht => ?_
  simp only [mem_range] at ht
  rw [show n - 1 - (n - 1 - t) = t by omega]

                                                                             
                                                      
                                                                   

lemma digit_extract (hp : 1 < p) (k : ℕ) (g : ℕ → ℕ) (hg : ∀ t, g t < p) (s : ℕ) :
    (∑ t ∈ range k, g t * p ^ t) / p ^ s % p = if s < k then g s else 0 := by
  induction k generalizing g s with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ']
    have e : ∑ t ∈ range k, g (t + 1) * p ^ (t + 1) = p * ∑ t ∈ range k, g (t + 1) * p ^ t := by
      rw [mul_sum]; refine sum_congr rfl fun t _ => by ring
    rw [e, pow_zero, mul_one]
    rcases s with _ | s
    · rw [pow_zero, Nat.div_one, if_pos (Nat.succ_pos k), Nat.add_comm, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (hg 0)]
    · rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega),
        Nat.div_eq_of_lt (hg 0), zero_add, ih (fun t => g (t + 1)) (fun t => hg _) s]
      simp only [Nat.add_lt_add_iff_right]

lemma digit_extract_be (hp : 1 < p) (k : ℕ) (f : ℕ → ℕ) (hf : ∀ t, f t < p) (s : ℕ) (hs : s < k) :
    (∑ i ∈ range k, f i * p ^ (k - 1 - i)) / p ^ s % p = f (k - 1 - s) := by
  rw [reflect_digits, digit_extract p hp k _ (fun t => hf _) s, if_pos hs]

/-! ## Decomposition of a coordinate -/

variable [NeZero p]

/-- Total digit accessor (as natural numbers). -/
def dv (k : ℕ) (D : Fin (3 * k) → ZMod p) (j : ℕ) : ℕ := if h : j < 3 * k then (D ⟨j, h⟩).val else 0

                                                                             
                      
                       
                             

                                                     
def tail (k : ℕ) (D : Fin (3 * k) → ZMod p) : ℕ :=
  ∑ j ∈ Ico (k + 2) (3 * k), dv p k D j * p ^ (3 * k - 1 - j)

                                                                                                  
             
                                                                      
                                                                                  
                                        
                                
                             
                                                                

lemma coord_split (k : ℕ) (hk : 1 ≤ k) (D : Fin (3 * k) → ZMod p) :
    ∑ j : Fin (3 * k), (D j).val * p ^ (3 * k - 1 - (j : ℕ)) =
      p ^ (2 * k) * (∑ i ∈ range k, dv p k D i * p ^ (k - 1 - i)) + p ^ (2 * k - 1) * dv p k D k +
        p ^ (2 * k - 2) * dv p k D (k + 1) + tail p k D := by
  rw [show ∑ j : Fin (3 * k), (D j).val * p ^ (3 * k - 1 - (j : ℕ)) =
      ∑ j : Fin (3 * k), dv p k D j * p ^ (3 * k - 1 - (j : ℕ)) by
        refine sum_congr rfl fun j _ => ?_; simp [dv, j.isLt],
    Fin.sum_univ_eq_sum_range (fun j => dv p k D j * p ^ (3 * k - 1 - j)),
    ← sum_range_add_sum_Ico _ (show k ≤ 3 * k by omega),
    sum_eq_sum_Ico_succ_bot (show k < 3 * k by omega),
    sum_eq_sum_Ico_succ_bot (show k + 1 < 3 * k by omega), tail, mul_sum]
  rw [show 3 * k - 1 - k = 2 * k - 1 by omega, show 3 * k - 1 - (k + 1) = 2 * k - 2 by omega]
  have : ∑ i ∈ range k, dv p k D i * p ^ (3 * k - 1 - i) =
      ∑ i ∈ range k, p ^ (2 * k) * (dv p k D i * p ^ (k - 1 - i)) := by
    refine sum_congr rfl fun i hi => ?_
    simp only [mem_range] at hi
    rw [show 3 * k - 1 - i = 2 * k + (k - 1 - i) by omega, pow_add]; ring
  rw [this]; ring

/-! ## Cells and carries -/

/-- Level `i` digit (as a natural number) of the cell of axis `d`. -/
def ad (k : ℕ) (v : Fin (3 * k) → ZMod p) (d : Fin 3) (i : ℕ) : ℕ :=
  if h : i < k then (v (ix k d ⟨i, h⟩)).val else 0

lemma ad_lt (k : ℕ) (v : Fin (3 * k) → ZMod p) (d : Fin 3) (i : ℕ) : ad p k v d i < p := by
  unfold ad; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_neZero p

/-- The cell `n_d ∈ [0, p^k)` of axis `d`. -/
def cellN (k : ℕ) (v : Fin (3 * k) → ZMod p) (d : Fin 3) : ℕ :=
  ∑ i ∈ range k, ad p k v d i * p ^ (k - 1 - i)

                                                                                        
                                                              

                                                                
                                                                                
                                     
                             
         
                                                                   
                                       

lemma cellN_digit (hp : 1 < p) (k : ℕ) (v : Fin (3 * k) → ZMod p) (d : Fin 3) (l : Fin k) :
    cellN p k v d / p ^ (k - 1 - (l : ℕ)) % p = (v (ix k d l)).val := by
  have hl := l.isLt
  unfold cellN
  rw [digit_extract_be p hp k _ (ad_lt p k v d) _ (by omega), show k - 1 - (k - 1 - (l : ℕ)) = l by omega]
  simp [ad, hl]

lemma zmod_digit (hp : 1 < p) (k : ℕ) (v : Fin (3 * k) → ZMod p) (d : Fin 3) (l : Fin k) :
    v (ix k d l) = ((cellN p k v d / p ^ (k - 1 - (l : ℕ)) : ℕ) : ZMod p) := by
  rw [← ZMod.natCast_mod, cellN_digit p hp, ZMod.natCast_zmod_val]

                                     
                                                                                         
                                                                                       
                                                  

                                                                                                      
                                       
lemma carry_digits (hp : 1 < p) (k : ℕ) (v w : Fin (3 * k) → ZMod p) (d : Fin 3)
    (h : cellN p k w d = (cellN p k v d + 1) % p ^ k) (l : Fin k) :
    w (ix k d l) - v (ix k d l) =
      if p ^ (k - 1 - (l : ℕ)) ∣ cellN p k v d + 1 then 1 else 0 := by
  have hl := l.isLt
  set s := k - 1 - (l : ℕ) with hs
  have hsk : s < k := by omega
  rw [zmod_digit p hp k w, zmod_digit p hp k v, h, ← hs]
  have e1 : (cellN p k v d + 1) % p ^ k / p ^ s = (cellN p k v d + 1) / p ^ s % p ^ (k - s) := by
    rw [show p ^ k = p ^ s * p ^ (k - s) by rw [← pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self]
  rw [e1, ← ZMod.natCast_mod, Nat.mod_mod_of_dvd _ (dvd_pow_self p (by omega)), ZMod.natCast_mod,
    Nat.succ_div]
  split_ifs <;> simp

                                               
                        
                                                                      
                                         

                                                                            

                                                                                         

                                                             
                                       
                                                                                         
                                                                                      
            
                  
        
                                                         
                                    
                                    

                                                                                      
                     
                                                                                       
                                    
                                                                                       

                                                                                              
                                                       
                                                        
            
                                    
                                                                                      
                                                         
                                             
                                                             

                                                                                               
                                                       
                                                           
            
                                              
                                       

                                                                                 
                                                                      
           
                                                   

                                           

                                                            
                                                                               
                                    
                                                                                              
                                                                  
                                                        
                                                                                                                
             
                                     
                                                              

                                                                                                     
                                                             
                                                                                   
                                                                                      
                                                                           
                                                                        
                                                                 
                                                                                               
                                        
                                    
                                                               
           
              
                                    
                    
                                   
                           
                                  

                                                                           
                                              

                                                                           
                                              

                                                                 
                                                                                       

                                                                 
                                                                                       

                                                                                                  
                                                                                     
                                                                                                
                                                                     
                     
                                                             
                     
                                                                              
                                                           

                           

                  
                                                                          
                                               

                  
                                                                                
             
                                            
                             
                                       
                                                                           
                                                      
           
                                                        
                                 
                  
                             
                                                
                                            
                                

                  
                                                                                                
                                                          
                                                             
                                            
             
                                                                          
                      
                                                    
                                                                      
                       
                          
                                                     
                                                                      
                                                                          
            

                  
                                                
                                                                     
                                                                                        
                                        
                                                                                    
                                                                                           
                                 
                                                                             
                                 
                                                                                    
                     
         
             
                                            
                                                               
                            
                     
                                                   
                                                              
                             
                      

end

end Z3Net.Two
