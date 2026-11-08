module

public import LeanLab.PNTPort.BV.Decomp
public import LeanLab.PNTPort.BV.PolyaVinogradov

/-!
# Type I bounds for the Vaughan sums S₁, S₂, S₃

Lab proof, AI wrote this file, known mathematics, no cited input.

For a primitive character `χ` modulo `q > 1`, `x ≥ 2` and `u, v ≥ 1`,

  `‖S₁‖ + ‖S₂‖ + ‖S₃‖ ≤ (log 4 + 4) u + 3 (u v + v) log x · √q (1 + log q)`.

Route: `S₁` by Chebyshev's bound `ψ(u) ≤ (log 4 + 4) u`; `S₂` and `S₃` by rearranging the
Dirichlet convolution into `∑_t c_t χ(t) ∑_{r ≤ N/t} a_r χ(r)` and applying Pólya–Vinogradov,
with Abel summation for the `log` weights in `S₃`. In fact `‖S₂‖ ≤ u v log x · PV` and
`‖S₃‖ ≤ 2 v log x · PV`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Rearranging a sum over `n ≤ N` and factorisations `n = t r`. -/
lemma sum_Icc_divisorsAntidiagonal {M : Type*} [AddCommMonoid M] (f : ℕ × ℕ → M) (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, f p =
      ∑ t ∈ Icc 1 N, ∑ r ∈ Icc 1 (N / t), f (t, r) := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.2.1, x.2.2⟩) (fun y _ => ⟨y.1 * y.2, (y.1, y.2)⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, a, b⟩ hx
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨h1, h2⟩, hab, hn⟩ := hx
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hab; omega)
    have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hab; omega)
    refine ⟨⟨ha, ?_⟩, hb, ?_⟩
    · nlinarith
    · rw [Nat.le_div_iff_mul_le ha]; nlinarith
  · rintro ⟨t, r⟩ hy
    simp only [mem_sigma, mem_Icc, Nat.mem_divisorsAntidiagonal] at hy ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
    rw [Nat.le_div_iff_mul_le (by omega)] at h4
    refine ⟨⟨?_, ?_⟩, trivial, ?_⟩
    · nlinarith
    · nlinarith
    · positivity
  · rintro ⟨n, a, b⟩ hx
    simp only [mem_sigma, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨_, hab, _⟩ := hx
    subst hab
    rfl
  · rintro ⟨t, r⟩ _
    rfl
  · rintro ⟨n, a, b⟩ _
    rfl

                                                        
                                                                                
                                                                                   
                                         
                                                              
                                                                                                
                                    
                                  
                                     
                                                                                   

lemma sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (Y : ℕ) :
    ∑ h ∈ Icc 1 Y, f h = ∑ h ∈ range Y, f (h + 1) := by
  induction Y with
  | zero => simp
  | succ Y ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- Abel summation identity. -/
lemma abel_range (a : ℕ → ℝ) (c : ℕ → ℂ) (Y : ℕ) :
    ∑ h ∈ range Y, (a (h + 1) : ℂ) * c (h + 1) =
      (a Y : ℂ) * (∑ j ∈ range Y, c (j + 1)) -
        ∑ h ∈ range Y, ((a (h + 1) - a h : ℝ) : ℂ) * (∑ j ∈ range h, c (j + 1)) := by
  induction Y with
  | zero => simp
  | succ Y ih =>
    rw [sum_range_succ, ih, sum_range_succ, sum_range_succ (fun h => ((a (h + 1) - a h : ℝ) : ℂ) *
      (∑ j ∈ range h, c (j + 1)))]
    push_cast
    ring

lemma log_nat_mono (h : ℕ) : Real.log (h : ℝ) ≤ Real.log ((h + 1 : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  · exact Real.log_le_log (by exact_mod_cast hh) (by push_cast; linarith)

                                                       
                                                                  
                                                                 
                                                                                 
                                                                                  
                                                                     
                                                     
                                                               
                                                                        
                                                                              
                  
        
                                                                               
                                                                                   
                                                                     
                                       
                                                                   
                               
                                                                    
                                                      
                                                                   
                                                  
                                                                  
                                                    
                                
                                                                     
                                                          
            

                                                 
                                                         
                   
                                 
                                                                
                  
                                               
             
                        

                                                                  
                                       
                                           
                                  
                                                   

                                                                         
                                           
           
                                                                       
                                                                 
                                                                
                                                 
                                                                
                                                         
                                          
                         
                                                                                
                  
                                               
             
                             
                                             
           
                                                            

                                                                               
                                                         
                                                                                    
                                         
               
                                                                            
                                                 
                                                      
                                                         
                                                                    
                                                                            
              
                            
                       
                                                
                                                                                                        
                                                               
                                           
                     
                                                            
                                                                 
                                               
                                       
                            
                                                                                         
                                                                                
                          
                                         
                                                         
                          
                                                              
             
                 
           
                                       
                                         
                                                                 
                 
                                                                               
                                                                                          
                                                                     
                                                                      
                                        
                                                       
                                                
               
                      
                                                      

                                                                               
                                                       
                                                                              
                                         
               
                                                                            
                                                 
                                                      
           
                                                                                   
                                   
                                                                                                      
           
                   
                                                                                       
                                                           
                                                                      
                  
                                        
               
          
                                                                   
                                                      
                                                                                 
                                                                
                      
                                                                       
                                                        
                                                                          
                                                        
                                                      
                                  
                              
        

                                                              
                                                                                
                                                                                   
                                            
                                                                     
                                              
                             
                                                             
                                                           
                                                 
                                                           
                                                            
                               
                   
                                             
                                                                                  


end LeanLab.PNTPort.BV
