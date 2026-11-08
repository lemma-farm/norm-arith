module

public import LeanLab.Halupczok2012.U1439Combin
public import LeanLab.Halupczok2012.NonCoprime

/-!
# P0077 Halupczok 2012, Theorem 2 reduced to Theorem 5 and the main term step, unit U-1439

AI wrote the Lean code, Claude, run 20261021T1603Z-28836. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

The paper proves Theorem 2 by writing the ternary sum as `∑_{p₁} log p₁ · binSum(n - p₁)` and
splitting `binSum(n - p₁) - T(n,q,a) Y₁ Y₂ / …` into

* the BINARY PART `∑_q |∑_{p₁ ≡ a (q)} log p₁ (binSum(n - p₁) - 𝔖(n - p₁) Y₂)|`, bounded from
  the Perelli-Pintz mean square, the paper's Theorem 5, and its Lemma 1; and
* the MAIN TERM PART `∑_q |∑_{p₁ ≡ a (q)} log p₁ 𝔖(n - p₁) - 𝔗(n,q,a) Y₁|`, bounded from the
  Perelli-Pintz-Salerno short interval Bombieri-Vinogradov theorem, the paper's Theorem 3, and
  the singular series computation with the Chinese remainder theorem.

Here:

* `binaryPart`: the binary part is `≪ Y₁ Y₂ L^{-A}`. PROVED CONDITIONAL ON `Theorem5` only.
  The paper's Lemma 1 is NOT needed: in Theorem 2, `Q ≪ Y₁ X₁^{-1/2} L^{-B}` gives `Q² ≪ Y₁`,
  so the elementary divisor moment `divisor_moment` and Cauchy-Schwarz suffice.
* `theorem2_of_inputs : Theorem5 → MainTermMV → Theorem2`. CONDITIONAL ON both.
* `theorem2Zeroed_of_inputs`: the F-0008 repair, the all-`q` form with `T0`, CONDITIONAL ON the
  same two inputs instead of the paper's Theorem 2.

`MainTermMV` is still the paper's own main term step, its displays after (10); its standard
input is `Theorem3`, Perelli-Pintz-Salerno, stated below; `U1457SingSeries` derives
`MainTermMV` from `Theorem3` and the singular series facts proved in `U1462Tails`.
The lab's `PNTPort.BV.BombieriVinogradov` is for `ψ(x; q, a)` over `[1, x]`; it does not give
intervals of length `Y₁ = X₁^{3/5+ε}`, so it cannot replace `Theorem3`.
-/

@[expose] public section


namespace LeanLab.Halupczok2012

open Finset

/-! ### The cited inputs -/

/-- **Theorem 5 of the paper**, Perelli-Pintz: for `Y^{1/3+ε} ≪ R ≪ Y ≍ 2X₁ - X₂ - Y ≥ 0`,
`R ≤ X₁`, `X₂^{7/12+ε₂} ≪ Y ≤ X₂`,
`∑_{k ∈ [X₁, X₁+R]} |∑_{p₂+p₃=2k, p₂ ∈ [X₂,X₂+Y]} log p₂ log p₃ - 𝔖(2k) Y|² ≪ R Y² L^{-A}`,
`L = log Y`. Cited input. -/
def Theorem5 : Prop :=
  ∀ A ε ε2 : ℝ, 0 < A → 0 < ε → 0 < ε2 →
  ∀ c1 c2 c3 c4 c5 : ℝ, 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → 0 < c5 →
  ∃ C Y0 : ℝ, ∀ X1 X2 Y R : ℝ, Y0 ≤ Y →
    c1 * X2 ^ (7 / 12 + ε2) ≤ Y → Y ≤ X2 → c2 * Y ^ (1 / 3 + ε) ≤ R → R ≤ c3 * Y → R ≤ X1 →
    0 ≤ 2 * X1 - X2 - Y → c4 * Y ≤ 2 * X1 - X2 - Y → 2 * X1 - X2 - Y ≤ c5 * Y →
    ∑ k ∈ kRange X1 R, (binSum X2 Y (2 * k) - S (2 * k) * Y) ^ 2 ≤
      C * R * Y ^ 2 * Real.log Y ^ (-A)

                                                                               
                                                                    
                                              

                                                                                               
                                                                                            
                                                                                              
                                                                                        
                        
                                                                     
                                                                           
                                                                                          
                                                                                               
                                                                   
                                                                        

                                           
                                                          
                                                                                       
                                     

                                                                          
                                                      
                                                                                 
                                                                                              
                      
                                                                            
                                                                      
                                                         
                                             
                                                                                       

                  

                                                                     
                                                       
                                                                        

                                                          
                                                                                   
                                  

                                                               
                                                                              
                                               
                                                                             
                                     
                                                     
                                                 
                                                               
                                

                                                            
theorem kRange_subset_biUnion (X R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m) :
    kRange X R ⊆ (range m).biUnion (fun j => kRange (X + j * (R / m)) (R / m)) := by
  intro k hk
  unfold kRange at hk ⊢
  rw [Finset.mem_filter] at hk
  obtain ⟨-, hk1, hk2⟩ := hk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hRm : 0 < R / m := div_pos hR hm'
  set t := ((k : ℝ) - X) / (R / m) with ht
  have ht0 : 0 < t := div_pos (by linarith) hRm
  have htm : t ≤ m := by
    rw [ht, div_le_iff₀ hRm]; field_simp; linarith
  have hc1 : 1 ≤ ⌈t⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr ht0).ne'
  have hcm : ⌈t⌉₊ ≤ m := Nat.ceil_le.mpr htm
  rw [Finset.mem_biUnion]
  refine ⟨⌈t⌉₊ - 1, Finset.mem_range.mpr (by omega), ?_⟩
  have hj : ((⌈t⌉₊ - 1 : ℕ) : ℝ) = (⌈t⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hc1]; simp
  have hlt : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0.le
  have hge : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  have hkt : (k : ℝ) = X + t * (R / m) := by rw [ht]; field_simp; ring
  rw [Finset.mem_filter, hj]
  have hA : X + ((⌈t⌉₊ : ℝ) - 1) * (R / m) < k := by
    rw [hkt]; nlinarith
  have hB : (k : ℝ) ≤ X + ((⌈t⌉₊ : ℝ) - 1) * (R / m) + R / m := by
    rw [hkt]; nlinarith
  refine ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, hA, hB⟩
  have := hB.trans (Nat.le_ceil (X + ((⌈t⌉₊ : ℝ) - 1) * (R / m) + R / m))
  exact_mod_cast this

/-- A sum over a finite union of nonnegative terms. -/
theorem sum_biUnion_le_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Finset ℕ)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    ∑ k ∈ s.biUnion t, g k ≤ ∑ j ∈ s, ∑ k ∈ t j, g k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hj]
    have := Finset.sum_union_inter (s₁ := t j) (s₂ := s.biUnion t) (f := g)
    have h0 : 0 ≤ ∑ k ∈ t j ∩ s.biUnion t, g k := Finset.sum_nonneg (fun k _ => hg k)
    linarith

/-- Sum over the pieces of a cover. -/
theorem sum_kRange_le_pieces (X R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) :
    ∑ k ∈ kRange X R, g k ≤ ∑ j ∈ range m, ∑ k ∈ kRange (X + j * (R / m)) (R / m), g k :=
  (Finset.sum_le_sum_of_subset_of_nonneg (kRange_subset_biUnion X R hR m hm)
    (fun k _ _ => hg k)).trans (sum_biUnion_le_nonneg _ _ g hg)

                                                                 
                                                                             
                         
                                  
                                                                              
                                           
                                                                                     
              
                                                              
                                 
                                 
                                      
                                                
             
                                                               
                                                      
                                                                                    
                                                             
                                                                         
                             
                            
                       
                                       
                                           
             
                                                                                
                                                                         
                  
                                   
                                 
                                           
                          
                                                                       
                                                                               
                                             
                  
                     
                              
                                                                                      
                                                                                              
                  
                                                               
                                                                                   
                           

                                           
                                                 
                                                             
                                             
                                                                               
                                               
                                           
                                 
               

                                                                  
                                                                          
                                                                            

                                                                
                                                                                  
                                                            
                                                                                       
                                                                           
                                                                                            
                                                                                            
                                           
                                                                    
                                                   
                                                         
                              
                                                 
                           
                                                              
                                         
                                                                                         
                                                                        
                               
                                                                                               
                                                 
                                                                 
                                                                              
                                                
                                                                                  
                         
                                                  
                                                                        
                                  
                                                                        
                                                        
                                                                                            
                                                           
                                                         
                                                                   
                                                         
                                                            
                                                         
                                
                                                
                                          
                                  
                                                                     
                                           
                                  
                                  
                    
                                                                                     
                                                                                     
                                         
                                        
                                                             
                                                          
            
                                                                
                                                                                                  
                                                                            
                                                                            
                                                                                              
                                                  
           
            
                                                  
                                       
                                                                   
                                     
                                                                                 
                    
                                                            
                                                     
                  
            
        
                                 
                                                      
                                                              
                                                                   
                                                                                             
                                     
                                                            
                                                            
                                              
                                                         
                                                     
                 
                                                               
                                                
                                                                      
                                                                                
                          
                                                   
                                        
                                                 
                                                    
                                                    
                                                         
                                                                                               
                                                              
              
                                                          
                                            
                                                     
                                                               
                                                                   
                                                         
                                                             
                                                                 
                                                      
                                                  
              
                                              
                                                        
                                                  
                                                                                              
                    
                                                                                      
                                                     
            
                                                                      
                               
                               
                                                                                       
                                             
                                                                               
                                           
               
                                                    
                                                                 
              
                                            
                              
                                                      
                                                              
                                                     
                                                                             
                                
                                                     
                                                                                       
                                                
                                                                 
                                              
                                           
                                                         
                                                                               
           
            
                                         
                                                                                            
                                                                    
                                                                           
                                                          
                                             
                                              
                                                      
                                                             
                                                          
                                                                    
                                   
                                    
                                                                                     
            
                                                                         
                                                           
              
                                    
                                                         
                                               
                                      
                                                                         
                                                 
                                            
                                                              
                    
                                                 
           
                                                 
                             
                   
                                                                                      
                  
               
                                                 
              
                                                                     
              
                        
                        
                                         
                                                                          
                                              
                                                                 
                                                                                             
                      
                                         
                                                                  
                                                                          
                                                                                 
                                           
                                                                                          
                                                                              
                                                                                       
                                            
                                                                     
                                                                          
           
            
                                           
                                                                                            
                                                                                
                
                                                                
                                                                  
                                                                    
                                                      
                                               
                                                         
                                       
                                                          
                            
                                                                                         
                                                                  
                                                                     
                                             
                                                               
                                                                                         
                                                                   
                                                     
                                                            
             
                                  
                                                                              
                                               
                                                                   
                                                  
                                                                
                             
                                
                                                                                  
                                                  
                                                                     
                                                
                                                                     
                                           
                               
                                  
                
                                           
                                                               
                                                             
                                                                                           
                                        
                                                                  
                                                             
                                                                                      
                                
                                                                    
                                                               
                                                             

                                                                  

                                                                 
                                                                             
                               
                                                  
                                         
                                                                           
                                           
                                                                                   
                                                                                      
                                                                  
                                       
                                                                                                  
                                                                           
                                                                    
                                                                                 
           
                                     
                                                                    
                                                                                    
                                                                 
                                                   
                                                 
                   
                                                                             
                                                                                    
                                         
                                                                              
                                 
                                                      
                                                                            
                                                       
                                                                     
                                     
                                                                          
                                                  
                                                 
                                      
                 
                                    
                                     
                                                     
                                                                                        
        
          

                                                                                       
                                                                  
                                                                                      
                                                       

                                                         

                                                                                             
                            
                                          
                                                                                               
                                                                       
                                                                             
                                     

end LeanLab.Halupczok2012
