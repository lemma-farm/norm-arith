/-
# Window Turán–Kubilius substrate (Track R, A2-III, N3-h)

The in-tree Turán–Kubilius and sift bounds (`TuranKubilius.lean`,
`TypicalFactorization.lean`) run on the global range `Ico 1 N`.  The
band-energy schedule prices the atypical complement *per block*
`(A, A+Δ]`, so it needs the first/second prime moments and the sifted
log-average on a window — with errors measured against the window
harmonic mass, not `log N`.

This file builds that substrate from the exact fibre reindex: the
`d`-multiples of a window are the dilated quotient window, so every
moment computation reduces to comparing harmonic masses of quotient
windows.
-/
                                             
import MoltResearch.Discrepancy.RamareIdentity
import MoltResearch.Discrepancy.PlancherelHarness
import MoltResearch.Discrepancy.TypicalFactorization

namespace MoltResearch

open Finset

                                                                  
                                                                   
                                                                
                                                                
                                                         
                                                           
                                                               
           
                                                                         
                                                                      
                                    
                      
                                                  
                                     
              
                             
                         
                        
                                            
                                                               
                                                               
                                 
                         
                
                         
                
                                       
                           
                                            
                           
                                                         
                                                     
                                                    
           
            


                                                                  
                                                                  
                                                               
                                             
                                                               
                                                                 
                  
           
                                                                        
                                          
                                     
                                              
              
                
                                            
                                                              
                                                    
                                                   
                                      
                                                           
                                                                     
                                                      
                             
                  
                                        
                  
              
                                        
                                        
                                  
                                             
                             
                                                                
                                                            
                                                          
                                               
                                              
                         
                  
                      
                 
                        
                


                                   
                                                                
                                                                
                                                                   
                                                                    
                                                                  
                                                               
                                                              
         
                                                           
                                 
                                            
                                                            
                            
                                       
                       
                                                                    
                                              
                                  
                               
                                  
                               
                                                   
                                                            
         
                                              
         
                                                                        
         
                                              
         
                                          
                                                                   
              
                                                         
                                                               
                       
            
                                                    
                                           
              
                                                      
                                        
                       
            
                                                  
                                                        
                                          
              
                                                             
                                                                
                       
            
                                                                    
                                                   
              
                                                          
                                        
                       
            
                                                                     
             
        
                                                                     
             
        
                                                      
                                             
                                                                  
                                           
                                                    
                                             
                                                                       
                                                 
                                       
                                                      
                                             
                                                                  
                                           
                                                    
                                             
                                                                       
                                                 
                                       
                                                     
                                                      
                                                   
                                                  
                                               
                                                   
                                                  
                                              
                                    
                                             
                                       
                                                    
                             
                                       
                                    
                                             
                                       
                                                    
                             
                                       
                                                                       
                                         
                                                
                                                       
                                                                 
                
          
                                                 
                                              
                                                                    
            
                                                                       
                                         
                                                
                                                       
                                                                 
                
          
                                                 
                                              
                          
            
                                                  
                                
                             
                                          
                                            
                        
                                              
             
             
                                                     
                                                                   
                                                           
                                          
                                                                 
                    
            
                                          
                                                                 
                    
            
                 
                                   
                                                                        
                                                                   
                                                 
                                               
                         
                                   
                                                                   
                                                                         
                                  
                             
                                                                       
                                                     
                                                       
                                          
                                                                 
                    
            
                                          
                                                                 
                    
            
                 
                                   
                                                      
                                       
                                                           
                                         
                                                           
                         
                                                                
                                         
                                                     
                                 
                                  
                             


                                                                      
                                                                 
                                                           

                                                            

                                                                  
                                                                      
                                                          
                                                                  
                                                            
                                                             
                                
           
                                       
                                                                    
                                                                
                       
                                   
                                       
                                                         
               
                             
               
                         
                                               
                        
                                                 
                                             
                          
                                                      
                            
                      
                                                                
                                                    
                           
              
                                     
                                                 
                                               
                                                 
                                         
                                                                     
                                                                 
                                                   
                                                            
                                                
          
                                                                    
                                                 
                                       
                                                           
                
                                      
                       
                                                                  
                                                              
                                                                  
                                                                
                                     
                                                       
                                          
                                           
                                
            


                                                                     
                                                          

                                                          

                                                          
                                                       
                                                         
                                                             
                                                       
                                                 
           
                                 
                                         
                           
                                                        
             
                           
             
                                    
                       
                                             
                       
                                             
                                        
                                               
                                           
                      
                                           
                        


                                                               
                                                                    
                                                                    
                                  
                                              
                                                 
                                                    
                                                          
           
                                          
             
                   
                                           
                                                
           
                                           
                                     

                                                                      
                                                                    
                                                                    

                                                               

                                                               
                                                                  
                                
                                                             
                                                              
                   
                                                                
                             
                                                        
                                          
                                                     
           
                              
                                      
                                                                
                                                    
                           
                   
                                         
                                                              
                                                 
                                                                 
                                                   
                                                            
                                                
          
                                                                    
                                                 
                                       
                              
                                          
                         
                                                           
                
                                      
                             
                                  
                                                             
                                         
                                                                 
                                                        
                                               
              
                                      
           
                                                                                
          
                                                
                                 
                                                                      
                                  
                                                    
                                     
                                                         
                                          
                                                  
                                                                          
                                             
                       
                                                                 
                       
                      
                                                                 
                                                          
                                            
                                                  
                                            
                                               
                                                          
              
                                     
                       
                                                              
                                
                                
                                                                      
                                                              
                             
                
                                 
                                         
                                                              
                 
            
                
                                                               
                                                                  
                    
                                                          
                                            
                                                  
                                            
                                               
                                                                    
                                                      
                            
                                                                 
                        
                                                                      
                                                                  
                    
                                                          
                                            
                                                  
                                            
                                              
                                                                      
                                                        
                              
                                                                   
                          
                                                                        
                                   
            
              
                                         
            
                                         
                           
                                
                                                                      
                                                            
                                            
                                                                  
                                  
                                                        
                                               
                                              
                                                  
                                                           
                                                                  
                               
                                                           
                                                    
                          
          
                                                                 
                                                                 
                              
                                                                         
                                           
                                                     
            


                                                               
                                  

                                                                

                                          
                                                              
                                                                     
                                                                 
                                                                
                                                   
                                                              
                   
                         
                                                              
                                                          
                                                  
                                                              
           
                                        
                                              
                                                     
                                              
                       
                                     
                                                            
                                                                   
                              
                                                                     
                                                                      
                                    
                                                              
                                               
                                    
                                                   
                                                      
                
                               
                                  
                                    
                               
                
          
                              
                                                              
                               
                                                
                                      
                                                     
                                                      
                                  
                                                                     
                                  
                                        
                                                    
                                    
                                                     
                                                             
                                               
                      
                                                
                                                                  
                           
                                                            
                                                 
                                                        
                                    
                                                       
                                                
                                                                     
                                    
                                               
                                      
                                      
                                               
                                               
                                    
                                                  
                                                                   
                                      
                             
                                                                         
                           
                                                      
                                         
                                                       
                                
                                                                  
                          
                                                                   
                                
             
             
                  
                                  
                                                   
                                                   


                                                                     
                                                                     
                                                      

                                                        

                                                              
                                                               
                 
                                                 
                                                              
                                                    
                                 
                                                       
                                                             
                                                    
                                                           
                                      
           
                                                   
                                                                  
                                            
                                             
                                              
                                                                
              
                                
             
                                                                  
                      
                
              
                                           
                                                     
                              
                                                                 
                                      
                                       
                                                          
                                       
                                                   
                                          
                                                                 
                                    
                               
                                          
                                                                 
                                               
                                                                 
                                
                                          
                                                                     
                               
                         
                                                        


                   
                                                                     
                                                                    
                                                                   
                                           

                                                              

                                                                  
                                                                 
                                               
                              
                                         
                                                    
                 
                                                    
                                 
                                                     
                                          
                                                               
                                                      
                                                             
                                              
           
                       
          
                           
                     
                                                
                                                    
                                                           
                                                      
                                                         
                                                     
                                     
                                          
                                      
                                            
                                       
                                                                  
                                         
                                                   
                                    
                                                     
                                      
                                                       
                  
                                    
                                                                   
                                                  
                              
                                       
                                
                                                              
                                     
                                        
                                                     
                                      
                                                  
                                       
                                                                      
                                                  
                                                   
                                    
                                                        
                                          
                                                              
                                           
                                                               
                                          
                                        
                                                   
                                        
                                               
                                 
                                                          
                                                   
                                    
                                                           
                                                    
                
                                       
                                        
                                                              
                      
                       
                                                                 
                                                        
                                                               
                                    
                                              
                                   
                                                     
                                                            
                                          
                                                
                                                    
                                   


                             
                                                                    
                                                               
              

                                                  
                                                          

                                                                
                                                                   
                                                                 
                                                                     
                                                    
                                                                   
                                                                 
            
                                                          
                              
                                                
                                                            
                                                                    
                                                                   
                                        
                              
                                                                        
           
                                         
                                     
                                                                    
                                                         
                                         
         
                                                                     
                                                                     
                          
                                                   
                                                             
                         
                                                                   
                                            
                                                              
                
                                    
                           
                                                             
                                   
                                                             
                                                            
                                                           
                                      
                               
               
          
                               
               
                                                                         
                                       
                                                                
                                        
                                                                  
            
                                        
                              
                                                                     
                                              


                                    
                                                                 
                                                

                                                           

                                          

                                                                   
                                                                      
                                                                    
                                                                
                                                                      
                                                                    
                                                                        
                                                                
                                                
                                                   
                                                            
                                           
                                                                      
                                                
                                                                   
                                  
           
                                                                   
                 
                                                          
                                                 
                           
                                                                 
               
                                                     
                                           
                                                                  
                              
                                                                       
           
                                                      
                                                         
                                     
                                                     
                                                    
                                       
                            
                                                                       
                               
                                                                      
                                    
                                                                  
                                                     
              
                                         
                             
                                 
                           
                           
                           
                           
                       
               
                                             
                              
                                                                 
                                                    
                                                            
                              
                                                              
                                     
           
                                                     
                      
                                                                         
                 
                                                                  
                                     
                   
                       
                       
                                                          
                                                                      
                                     
            
                                                          
                                                                   
                                      
                         
                                                
             
        
            
                                                                            
              
                                       
                                        
                       
                                           
                              
                                                
                                  
                         
                                 
                   
                                   
                        
                            
                                                
                                              
                                                         
                                  
                                                
                                          
                 
               
                                                
                                              
                                                 
                  


                                                         

open Finset in
/-- **A difference of disjoint sums is one signed sum** (Track R,
A2-III, II-2c): for disjoint `S`, `S'`,

  `∑_{S} w − ∑_{S'} w = ∑_{S ∪ S'} (if · ∈ S then w · else −w ·)`.

The point is that a *difference* of two polynomials supported in one
collar is again a *single* polynomial supported in that collar, with
coefficients of the same size — so the mean value theorem applies to it
once, rather than twice through a square-splitting triangle. -/
theorem sum_sub_sum_eq_sum_union_signed (S S' : Finset ℕ)
    (hdisj : Disjoint S S') (w : ℕ → ℂ) :
    (∑ m ∈ S, w m) - (∑ m ∈ S', w m)
      = ∑ m ∈ S ∪ S', (if m ∈ S then w m else -w m) := by
  classical
  rw [Finset.sum_union hdisj]
  have h1 : ∑ m ∈ S, (if m ∈ S then w m else -w m) = ∑ m ∈ S, w m :=
    Finset.sum_congr rfl fun m hm => by simp [hm]
  have h2 : ∑ m ∈ S', (if m ∈ S then w m else -w m) = ∑ m ∈ S', (-(w m)) :=
    Finset.sum_congr rfl fun m hm => by
      have hmS : m ∉ S := Finset.disjoint_right.mp hdisj hm
      simp [hmS]
  rw [h1, h2, Finset.sum_neg_distrib]
  ring

open MeasureTheory Finset ExpSums in
/-- **The telescoping energy** (Track R, A2-III, II-2c): if two windows
`(a, b]` and `(a', b']` have left endpoints within `L₁` and right
endpoints within `L₂` of each other, then the two `1/n`-normalised phase
polynomials they carry differ, in energy, by two collars —

  `∫_{−T}^{T} ‖∑_{(a,b]} − ∑_{(a',b']}‖²
     ≤ 2e^π(T/a₀ + 4)(L₁/a₀) + 2e^π(T/b₀ + 4)(L₂/b₀)`,

with `a₀ = min a a'` and `b₀ = min b b'`.

This is the analytic half of the `[MR]` decomposition lemma, and it is
what lets the band assembly replace a `p`-dependent fibre window
`(A/p, (A+Δ)/p]` by a cell-uniform reference block: on an e-adic cell at
resolution `2N` the two endpoints move by at most `A/(N·p) + 1` and
`B/(N·p) + 1` respectively
(`div_le_div_add_div_add_one`), so the error is `O(1/N)` per prime and
sums to `O(1/N)` over the cell.

The proof is the identity `sum_Ioc_eq_sum_Ioc_add_collars` followed by
two applications of `collar_energy_length_le`.  Its one inefficiency is
the square-splitting `intervalIntegral_norm_add_sq_le`, unavoidable
because the two collars are anchored at different scales; the four
collars of the identity are *not* split, since each pair lives in one
collar interval and `sum_sub_sum_eq_sum_union_signed` merges it. -/
theorem intervalIntegral_norm_sq_window_sub_le
    (a b a' b' L₁ L₂ : ℕ) (hab : a ≤ b) (ha'b' : a' ≤ b')
    (haa' : max a a' ≤ min a a' + L₁) (hbb' : max b b' ≤ min b b' + L₂)
    (hLa : L₁ ≤ min a a') (hLb : L₂ ≤ min b b')
    (ha1 : 1 ≤ min a a') (hb1 : 1 ≤ min b b')
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T,
        ‖(∑ m ∈ Finset.Ioc a b, (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc a' b', (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖^2)
      ≤ 2 * (Real.exp Real.pi * (T/((min a a' : ℕ):ℝ) + 4)
              * ((L₁:ℝ)/((min a a' : ℕ):ℝ)))
        + 2 * (Real.exp Real.pi * (T/((min b b' : ℕ):ℝ) + 4)
              * ((L₂:ℝ)/((min b b' : ℕ):ℝ))) := by
  classical
  -- the two left collars are disjoint, as are the two right collars
  have hdisj13 : Disjoint (Finset.Ioc a (min b a')) (Finset.Ioc a' (min b' a)) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_Ioc] at hn hn'
    omega
  have hdisj24 :
      Disjoint (Finset.Ioc (max a b') b) (Finset.Ioc (max a' b) b') := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_Ioc] at hn hn'
    omega
  -- each pair sits inside a single collar interval
  have hsubA : (Finset.Ioc a (min b a')) ∪ (Finset.Ioc a' (min b' a))
      ⊆ Finset.Ioc (min a a') (min a a' + L₁) := by
    refine Finset.union_subset ?_ ?_ <;>
      intro n hn <;>
      simp only [Finset.mem_Ioc] at hn ⊢ <;>
      omega
  have hsubB : (Finset.Ioc (max a b') b) ∪ (Finset.Ioc (max a' b) b')
      ⊆ Finset.Ioc (min b b') (min b b' + L₂) := by
    refine Finset.union_subset ?_ ?_ <;>
      intro n hn <;>
      simp only [Finset.mem_Ioc] at hn ⊢ <;>
      omega
  -- the signed coefficients are still `1`-bounded
  have hd₁ : ∀ n : ℕ,
      ‖(if n ∈ Finset.Ioc a (min b a') then c n else -c n)‖ ≤ 1 := by
    intro n
    split_ifs with h
    · exact hc n
    · rw [norm_neg]; exact hc n
  have hd₂ : ∀ n : ℕ,
      ‖(if n ∈ Finset.Ioc (max a b') b then c n else -c n)‖ ≤ 1 := by
    intro n
    split_ifs with h
    · exact hc n
    · rw [norm_neg]; exact hc n
  -- pointwise, the difference of the two windows is two collar polynomials
  have hpt : ∀ ξ : ℝ,
      (∑ m ∈ Finset.Ioc a b, (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc a' b', (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
        = (∑ m ∈ (Finset.Ioc a (min b a')) ∪ (Finset.Ioc a' (min b' a)),
              ((if m ∈ Finset.Ioc a (min b a') then c m else -c m)/(m:ℂ))
                * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          + (∑ m ∈ (Finset.Ioc (max a b') b) ∪ (Finset.Ioc (max a' b) b'),
              ((if m ∈ Finset.Ioc (max a b') b then c m else -c m)/(m:ℂ))
                * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)) := by
    intro ξ
    have hpush : ∀ (S : Finset ℕ) (m : ℕ),
        (if m ∈ S then (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
          else -((c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)))
          = ((if m ∈ S then c m else -c m)/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
      intro S m
      split_ifs with h
      · rfl
      · ring
    have h1 := sum_sub_sum_eq_sum_union_signed (Finset.Ioc a (min b a'))
      (Finset.Ioc a' (min b' a)) hdisj13
      (fun m => (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
    have h2 := sum_sub_sum_eq_sum_union_signed (Finset.Ioc (max a b') b)
      (Finset.Ioc (max a' b) b') hdisj24
      (fun m => (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
    have h1' : (∑ m ∈ Finset.Ioc a (min b a'), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc a' (min b' a), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
        = ∑ m ∈ (Finset.Ioc a (min b a')) ∪ (Finset.Ioc a' (min b' a)),
            ((if m ∈ Finset.Ioc a (min b a') then c m else -c m)/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
      rw [h1]
      exact Finset.sum_congr rfl fun m _ => hpush _ m
    have h2' : (∑ m ∈ Finset.Ioc (max a b') b, (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc (max a' b) b', (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
        = ∑ m ∈ (Finset.Ioc (max a b') b) ∪ (Finset.Ioc (max a' b) b'),
            ((if m ∈ Finset.Ioc (max a b') b then c m else -c m)/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
      rw [h2]
      exact Finset.sum_congr rfl fun m _ => hpush _ m
    rw [sum_Ioc_eq_sum_Ioc_add_collars a b a' b' hab ha'b'
      (fun m => (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)), ← h1', ← h2']
    ring
  simp only [hpt]
  -- both collar polynomials are continuous
  have hchar : ∀ v : ℝ, Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ) := fun v =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hXc : Continuous fun ξ : ℝ =>
      ∑ m ∈ (Finset.Ioc a (min b a')) ∪ (Finset.Ioc a' (min b' a)),
        ((if m ∈ Finset.Ioc a (min b a') then c m else -c m)/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) :=
    continuous_finset_sum _ fun m _ =>
      continuous_const.mul (hchar (Real.log m))
  have hYc : Continuous fun ξ : ℝ =>
      ∑ m ∈ (Finset.Ioc (max a b') b) ∪ (Finset.Ioc (max a' b) b'),
        ((if m ∈ Finset.Ioc (max a b') b then c m else -c m)/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) :=
    continuous_finset_sum _ fun m _ =>
      continuous_const.mul (hchar (Real.log m))
  refine le_trans (intervalIntegral_norm_add_sq_le _ _ hXc hYc T hT.le) ?_
  have hXe := collar_energy_length_le (min a a') L₁ ha1 hLa
    ((Finset.Ioc a (min b a')) ∪ (Finset.Ioc a' (min b' a))) hsubA
    (fun m => if m ∈ Finset.Ioc a (min b a') then c m else -c m) hd₁ T hT
  have hYe := collar_energy_length_le (min b b') L₂ hb1 hLb
    ((Finset.Ioc (max a b') b) ∪ (Finset.Ioc (max a' b) b')) hsubB
    (fun m => if m ∈ Finset.Ioc (max a b') b then c m else -c m) hd₂ T hT
  linarith


open MeasureTheory Finset ExpSums in
/-- **The decomposition lemma on an e-adic cell** (Track R, A2-III,
II-2d): for two primes `q ≤ p` of the same e-adic cell at resolution
`2N`, the quotient windows they cut out of `(A, B]` carry phase
polynomials whose energies differ by two `1/N`-collars —

  `∫_{−T}^{T} ‖∑_{(A/p, B/p]} − ∑_{(A/q, B/q]}‖²
     ≤ 2e^π(T/(A/p) + 4)·(A/(Np) + 1)/(A/p)
       + 2e^π(T/(B/p) + 4)·(B/(Np) + 1)/(B/p)`.

This is `[MR]`'s decomposition lemma in the form the band assembly
consumes: every prime of a cell may be replaced by one fixed reference
prime of that cell, at a cost of `O(1/N)` per prime.  The main terms
`(A/(Np))/(A/p) ≈ 1/N` are the genuine collar cost; the `+1`s are the
`ℕ`-division floors, contributing `p/A` — negligible at the scales the
assembly runs at, but honestly carried here.

The polynomial runs over the *full* quotient window with a global
coefficient function `c`.  That is deliberate: in the assembly the
Ramaré fibre is a proper subset of the window (the typical-set
quotients), and it is recovered by letting `c` vanish off it — which is
also why the collars of `sum_Ioc_eq_sum_Ioc_add_collars` had to be
independent of the coefficients.

`eadicCell_ratio_le` supplies the arithmetic ratio, and
`div_le_div_add_div_add_one` turns it into the two collar lengths. -/
theorem intervalIntegral_norm_sq_cell_fibre_sub_le
    {P : Finset ℕ} {N v : ℕ} (hN : 0 < N) {p q : ℕ}
    (hp : p ∈ eadicCell P (2*N) v) (hq : q ∈ eadicCell P (2*N) v)
    (hq1 : 1 ≤ q) (hqp : q ≤ p)
    (A B : ℕ) (hAB : A ≤ B)
    (hLA : A/(N*p) + 1 ≤ A/p) (hLB : B/(N*p) + 1 ≤ B/p)
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T,
        ‖(∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc (A/q) (B/q), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖^2)
      ≤ 2 * (Real.exp Real.pi * (T/((A/p : ℕ):ℝ) + 4)
              * (((A/(N*p) + 1 : ℕ):ℝ)/((A/p : ℕ):ℝ)))
        + 2 * (Real.exp Real.pi * (T/((B/p : ℕ):ℝ) + 4)
              * (((B/(N*p) + 1 : ℕ):ℝ)/((B/p : ℕ):ℝ))) := by
  have hp1 : 1 ≤ p := le_trans hq1 hqp
  have hratio := eadicCell_ratio_le hN hp hq hp1 hq1
  have hAq := div_le_div_add_div_add_one A N p q hN hq1 hqp hratio
  have hBq := div_le_div_add_div_add_one B N p q hN hq1 hqp hratio
  -- the larger prime cuts the smaller window
  have hdivA : A/p ≤ A/q := Nat.div_le_div_left hqp hq1
  have hdivB : B/p ≤ B/q := Nat.div_le_div_left hqp hq1
  -- the side conditions, by hand: `omega` treats `A/(N*p)` (variable divisor)
  -- as an opaque atom and does not even know it is nonnegative
  have hcolA : A/q ≤ A/p + (A/(N*p) + 1) := by
    rw [← Nat.add_assoc]; exact hAq
  have hcolB : B/q ≤ B/p + (B/(N*p) + 1) := by
    rw [← Nat.add_assoc]; exact hBq
  have hA1 : 1 ≤ A/p := le_trans (Nat.le_add_left 1 (A/(N*p))) hLA
  have hB1 : 1 ≤ B/p := le_trans (Nat.le_add_left 1 (B/(N*p))) hLB
  have hminA : min (A/p) (A/q) = A/p := min_eq_left hdivA
  have hminB : min (B/p) (B/q) = B/p := min_eq_left hdivB
  have hmaxA : max (A/p) (A/q) = A/q := max_eq_right hdivA
  have hmaxB : max (B/p) (B/q) = B/q := max_eq_right hdivB
  have hkey := intervalIntegral_norm_sq_window_sub_le
    (A/p) (B/p) (A/q) (B/q) (A/(N*p) + 1) (B/(N*p) + 1)
    (Nat.div_le_div_right hAB) (Nat.div_le_div_right hAB)
    (by rw [hmaxA, hminA]; exact hcolA) (by rw [hmaxB, hminB]; exact hcolB)
    (by rw [hminA]; exact hLA) (by rw [hminB]; exact hLB)
    (by rw [hminA]; exact hA1) (by rw [hminB]; exact hB1)
    c hc T hT
  rwa [hminA, hminB] at hkey


                                    
                                                                  
                                                               
             

                                                                     
                                       

                                                                   
                                                                         
                                                                       
                              

                                            
                                                                 
                                                                       
                                          
                                                                      
                                                    
                                                       

                                                                        
                                                                    
                                                        
                                                                 
                                                
                                                   
                                                          
                          
                                                                                                          
                                                              
                                                                      
           
                                                                     
               
                                                                 
                                                          
                               
                           
                                                                    
                                                    
                                                                                                        
                                                                                            
           
                                     
                                                         
                     
                                       
                           
                               
                                                    
                                         
                                                                                          
                                                                                            
                                         
                                                     
                                                       
              
                                         
                             
                                           
                                                                   
                       
               
                                           
                                                
                                           
                                                                      
                                                                       
           
                                            
                                                        
                                                       
                                        
                                                               
                                                         
           
                                                          
                                                                          
                 
                                                                         
                    
                                                                            
                                                            
                                                             
                                                  
                                                           
                                                         
                          
                                                            
                                                                       
                                             
                         
                     
                                                                    
              
                                            
                                                          
                                       
                                                              
                       
                                           
                              
                                                
                            
                             
             
                         
                                                      
                   
                                                                               
                        
                                                 
                                                                      
                          
                                                                      
                         
                                       
                                                              
                                            


                                                                  
                           

                                

                                                                        
                                                                         
                                                                     
                                                               
                                                                           
                        

                                                                            
                                                                           
                                                              
                                                                             
                                                                       
                                                                            
                                                                     
                                                                 
                                                               

                                                                          
                                                                 
                                                                            
                                            
                                 
                                                                          
                       
                                                                    
                                        
                                          
                                                           
                                                                      
                                                                               


open MeasureTheory Finset ExpSums in
/-- **The cell-uniform replacement** (Track R, A2-III, II-2e): over an
e-adic cell at resolution `2N` with least member `q`, replacing every
prime's own fibre window by the reference window `(A/q, B/q]` costs

  `∫_{−T}^{T} ‖∑_{p∈𝒞} (g p/p)e(−ξ log p)·(Z_p − Z_q)‖²
     ≤ (∑_{p∈𝒞} 1/p)·∑_{p∈𝒞} (1/p)·E_p`,

where `E_p` is the two-collar energy of `intervalIntegral_norm_sq_cell_-
fibre_sub_le`.  This is `[MR]`'s decomposition lemma in force: after it,
the cell's contribution factors as `(∑_{p∈𝒞} (g p/p)e(−ξ log p))·Z_q` —
a product of two independent Dirichlet polynomials, each of which the
mean value theorem can see — plus this error.

Both factors of `(∑_{p∈𝒞} 1/p)` are genuine: one is the Cauchy–Schwarz
weight, the other the sum being estimated.  Since a cell at resolution
`2N` has prime mass `O(1/N)` by Mertens, the pair contributes `O(1/N²)`,
which is what makes the `J`-level ladder converge.

The error `E_p` is left inside the sum rather than maximised over the
cell: it depends on `p` through `A/p` and `B/p`, and the assembly's
Mertens step is sharper if that dependence is kept. -/
theorem intervalIntegral_norm_sq_cell_replace_le
    {P : Finset ℕ} {N v : ℕ} (hN : 0 < N) {q : ℕ}
    (hq : q ∈ eadicCell P (2*N) v) (hq1 : 1 ≤ q)
    (hqmin : ∀ p ∈ eadicCell P (2*N) v, q ≤ p)
    (A B : ℕ) (hAB : A ≤ B)
    (hLA : ∀ p ∈ eadicCell P (2*N) v, A/(N*p) + 1 ≤ A/p)
    (hLB : ∀ p ∈ eadicCell P (2*N) v, B/(N*p) + 1 ≤ B/p)
    (g c : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T, ‖∑ p ∈ eadicCell P (2*N) v,
        ((g p/(p:ℂ)) * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
          * ((∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
              - (∑ m ∈ Finset.Ioc (A/q) (B/q), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)))‖^2)
      ≤ (∑ p ∈ eadicCell P (2*N) v, (1:ℝ)/(p:ℝ))
          * ∑ p ∈ eadicCell P (2*N) v, ((1:ℝ)/(p:ℝ))
              * (2 * (Real.exp Real.pi * (T/((A/p : ℕ):ℝ) + 4)
                      * (((A/(N*p) + 1 : ℕ):ℝ)/((A/p : ℕ):ℝ)))
                 + 2 * (Real.exp Real.pi * (T/((B/p : ℕ):ℝ) + 4)
                      * (((B/(N*p) + 1 : ℕ):ℝ)/((B/p : ℕ):ℝ)))) := by
  classical
  have hchar : ∀ v : ℝ, Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ) := fun v =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  -- the prime weights are `1/p`-bounded and continuous
  have hwbd : ∀ p ξ, ‖(g p/(p:ℂ)) * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖ ≤ (1:ℝ)/(p:ℝ) := by
    intro p ξ
    rw [norm_mul, Circle.norm_coe, mul_one, norm_div,
      Complex.norm_natCast]
    gcongr
    exact hg p
  have hwcont : ∀ p : ℕ, Continuous fun ξ : ℝ => (g p/(p:ℂ)) * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ) :=
    fun p => continuous_const.mul (hchar (Real.log p))
  have hzcont : ∀ p : ℕ, Continuous fun ξ : ℝ =>
      (∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
        - (∑ m ∈ Finset.Ioc (A/q) (B/q), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)) := by
    intro p
    refine Continuous.sub ?_ ?_
    · exact continuous_finset_sum _ fun m _ =>
        continuous_const.mul (hchar (Real.log m))
    · exact continuous_finset_sum _ fun m _ =>
        continuous_const.mul (hchar (Real.log m))
  refine le_trans (intervalIntegral_norm_sq_freq_weighted_sum_le
    (eadicCell P (2*N) v) (fun p ξ => (g p/(p:ℂ)) * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
    (fun p => (1:ℝ)/(p:ℝ)) hwbd hwcont
    (fun p ξ => (∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
        - (∑ m ∈ Finset.Ioc (A/q) (B/q), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)))
    hzcont T hT.le) ?_
  -- per prime, the two-collar energy of the decomposition lemma
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp => ?_) ?_
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact intervalIntegral_norm_sq_cell_fibre_sub_le hN hp hq hq1
      (hqmin p hp) A B hAB (hLA p hp) (hLB p hp) c hc T hT
  · exact Finset.sum_nonneg fun p _ => by positivity


                                    
                                                                  
                                                                       
                           

                                    
                                                 

                                     
                                                             
                                                                 
                                                                      
                                                     

                                                               
                                                            
                                                             
                                                                      
                                                             
                                                                          
                                                                        
                                                          
                                         
                                   
                                                                                                               
                                                              
                                                                      
                                               
                                                              
                                                                                
                                                                                                                    
                                                                                
                                  
                                                                                                             
                                                                           
           


                                    
                                                                      
                                                                
                                                               

                              
                                                                       

                                                                             

                                                                         
                                                                         
                                                                      
                                                                        
                                                                     
                                          

                              

                                                                      
                                                                       
                            

                                                                          
                                                                           
                                                                          
                                                                           
                                                                         
                                                                       
                                                                    
                                                                   

                                                                         
                                                                    
                                                                     
                                                
                                                   
                                                          
                                              
                                                   
                                     
                          
                    
                              
                                                                        
                                 
                                                                          
                                                                     
                                    
                                              
                                                    
           
                                                                                 
                                                                 
                            
                                                                     
                                                                             
                           
                                                                              
                                                          
                                                     
                                                              
                                       
              
                                         
                             
                                           
                                                   
                                   
              
                                     
         
                       
                           
                                                                    
                               
                                                                       
           
                                     
                                                         
                     
                                       
                           
                               
                                              
                        
                           
                                                                    
                               
                                                                    
                               
                                                                       
           
                                                           
                                                                    
                     
                                        
                           
                                 
                                                    
                                          
                            
                                                                      
                               
                                                                       
                                
                                                                      
                                                               
                                                          
              
                                         
                             
                                           
                                                                   
                       
                   
                                           
                                                
                                           
                                                                      
                                                                       
           
                                            
                                                        
                                                       
                                        
                                                                  
              
                                          
                             
                                 
                                                
                                          
                       
                   
                                                             
                                                             
                                                                             
                                       
                                                   
                                                           
           
                                                          
                                                                           
                  
                                                                         
                    
                                                                            
                                                            
                                                             
                                                  
                                                           
                                                         
                          
                                                             
                                                                      
                                       
           
                                                            
                
                                                                      
                                            
                                      
                           
                                                                          
                                                              
                                  
                                             
                            
                                                         
                                             
                                          
                           
                                                                     
           
                   
                                                          
                                       
                 
                                                                         
                   
                      
                       
                                                           
                                                   
                                                              
                               
                                                               
                                         
                                         
                                                                   
                                                                     
                                                              
                                                                      
                                                           
                                                                    
                                            
                                                                            
                                                            
                                          
                                         
                                                         
                                 
                                      
                               
           
                                                 
                                                         
                
                                                            
                                             
                                                        
                                 
                                            
                                             
                                     
                                                              
                              
                 
                                          
                  
                                                                
                                                                       
                                                                              
                                                
                         
                     
                                                                           
              
                                            
                                      
                                        
                               
                                                                     
                       
                                           
                              
                                                
                              
                         
                      
                                                                           
                   
                                   
                        
                                         
                                                       
                                 
                                                                     
                    
                          
                                                                 
                                                                      
                                                                                
                         
              
                                                              
                                           


                                    
                                                                         
                                                                    
                                                                      
                    

             
                                                                              

                                                              
                  

                                                               
                                                            
                                                                        
                                                                     
                                                                        
                                                                       
                                                                         
                                                        

                                                                      
                                                     
                                                                         
                                                                    
                                                         
                                                
                                                   
                                                          
                                              
                                                   
                                     
                                   
                                                            
                              
                                           
                                     
                                                    
                                                                   
                                           
                                                                    
                           
                                                                          
                                        
                                                  
                                                         
           
                                               
                                                              
                                                                                
                                                          
                                                                
                                                                                
                                                         
                                                                
                                                                                
                                                                             
                                         
                                                                               
                                   

                                    
                                                                       
                                                                       
                                                                      

                                                                  

                                                                        
                                                                       
                                                                       
                                                              
                                                                     

                                                                    
                                                                     
                                                            
                                                                   
                                                                     
                                                                
                                                                       
                                                                   
                                               
                                                                
                                     

                                                                
                                                           
                                                                       
                                                                   
                                
                                                                       
                                                                        
                                                                  
                                              
                                        
                                                  
                                                
                                                                   
                      
                                                  
                                                                
                                      
           
                                              
                                                   
                                           
                                                  
                    
                                     
                                                
                                       
                               
                                                               
                                 
                                                       
                                                                     
                                                               
                                                                     
                       
                                           
                                                            
                                                      
                      
                                        
                                                                        
                             
                                                 
                                                                             
                                            
                                                
                                                
                                           
                                         
                                                           
                                               
                    
                                               
                                                   
                                                        
                                                                 
                                                            
                                                                     
                                                          
                                                                 
         
                                                                                 
                                             
                                                                 
                                 
                                                             
                                     
                                                                              
            
                                                                 
                                                          
                                                             
                                                                       
                                                                           
                                                  
      

end MoltResearch
