module

public import Mathlib
public import LeanLab.HeathBrown1985.MainTermLocal
public import LeanLab.HeathBrown1985.Theorem1Chain

/-!
P0096 Heath-Brown 1985, page 57, the main term: `MainTerm4` from 2.4, hence from the
Siegel-Walfisz theorem 1.1, and Theorem 1 from the bound for Σ₃ and Siegel-Walfisz.
For one `m`, 4.1 is `x Σ_{q ≤ Q} g_m(q) + O(x Q⁻¹)`, the tail of the singular series is
`O(x Q⁻¹ L d(m)²)` (2.3 in the form of `tail_gcd_le`), and the case `t = 2` of 2.2 sums
`d(m)²` over `m ≤ 3x`, giving `x² L⁴ Q⁻¹` in all.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

                                                                                       
                                  
                                           
                                                            
                                                                              
                                   
                                                                                              
                                                                  
                                                      
                                                                                     
                                                                                  
                                                              
                                                                                    
               
                                                          
                                                     
                                               
                                                    
                                 
                           
                                            
                                                               
                                                                           
            
                                 
                                       
               
               
                                       
                                    
                                                                         
                                       
        
                                             
                
                                           
                                                       
                        
                                      
                                                                            
                                         
                                                
                                                                                               
                                                                                  
                                    
                        

                                                      
                                                
                                                                              
                                 
                   
                                                         
                                                           
                                                 
                                
                                                                        
                                 
                                                                            
                                       
                             
                                                     
                                               
                                            
            
                                                                                              
                                                                                       
                                            
                                         
                                                                                                        
                                           

                                                       
                                                                    
                                                    
                                                                                              
                                                                                     
                            
                     
                      
                                              
                                                       
                                 
                                 
                           
                                                   
                                                                                      
                               
                                                      
                                                                                                  
                                      
                                           
                                                          
                                                           
            
                                                                     
                                                          
                                                                                
                                                               
                                                      
                                                          
                                                             
                                                                 
                      
                                                    
                                                                                  
         
                                                  
                                                         
                                                           
                                                          
                                                           
                                                                                              
                                                                       
                                             
                             

                                           
                                                                                          
                  
                                                                              
                                                                              
                     
                
               
                      
                                              
                                                       
                                 
                                 
                                 
                                                          
                                                 
                                               
                            
                                  
            
                                       
                                                                          
                                                                
                                                                                   
                                                                       
            
                                                     
                                                           
                                                                                   
             
                                                          
                                                                                      
                                          
                                            
             
                                               
                                                                   
                    

                                                                   
                                                    
                                                            
                                                                              
                                               
                                                                         
                                                                                 
                                                                           
                                                                                               
                                        
                                                      
                                    
                                    
                                                          
                     
                
                                 
                                 
                                                
                                 
                             
               
                                         
             
                                                             
                                                                                            
                                                                           
              
                                                                               
                                                            
                                                                                               
                                                  
                                                          
                                                             
            
                                   
                                                          
                                       
                                                
                                         
                                       
                                                
                                                                  
                                                 
                                                                               
              
                                                                      
                                                                     
              
                    

                                           
theorem abs_singular_le (m : ℕ) (hm : 1 ≤ m) :
    |singular m| ≤ 1 + 24 * (m.divisors.card : ℝ) ^ 2 := by
  have h := abs_singular_sub_le m 1 hm le_rfl
  have e : ∑ q ∈ Icc 1 1, gm m q = 1 := by simp [gm_one]
  rw [e] at h
  simp only [Nat.cast_one, Real.log_one, div_one] at h
  have := abs_sub_abs_le_abs_sub (singular m) 1
  rw [abs_one] at this
  nlinarith

/-- The crude bound for one `m`. -/
theorem per_m_crude (B x : ℝ) (hx : 2 ≤ x) (m : ℕ) (hm : m ∈ mRange x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ (Real.log x ^ B) n * Λ (m - n) - x * singular m| ≤
      x * (Real.log x ^ B) ^ 3 * Real.log (3 * x) + x * (1 + 216 * x ^ 2) := by
  simp only [mRange, mem_filter, mem_Icc] at hm
  obtain ⟨⟨hm1, hm3⟩, _⟩ := hm
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set Q := Real.log x ^ B
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hL0 _
  have hmR : (m : ℝ) ≤ 3 * x := le_trans (by exact_mod_cast hm3) (Nat.floor_le (by linarith))
  have hl3 : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
  have hS : |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n)| ≤ x * Q ^ 3 * Real.log (3 * x) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hpt : ∀ n ∈ Icc 1 ⌊x⌋₊, |LambdaQ Q n * Λ (m - n)| ≤ Q ^ 3 * Real.log (3 * x) := by
      intro n _
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_mul (abs_LambdaQ_le_cube Q hQ0 n)
        (vonMangoldt_le_log_of_le _ _ (by linarith)
          (le_trans (by exact_mod_cast Nat.sub_le m n) hmR))
        ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    refine (sum_le_sum hpt).trans ?_
    rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le hx0.le)
      (by positivity)) hl3
  have hsing := abs_singular_le m hm1
  have hd : (m.divisors.card : ℝ) ≤ 3 * x :=
    le_trans (by exact_mod_cast Nat.card_divisors_le_self m) hmR
  have hd0 : (0 : ℝ) ≤ m.divisors.card := by positivity
  have hsing' : |singular m| ≤ 1 + 216 * x ^ 2 := by nlinarith
  calc _ ≤ |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n)| + |x * singular m| := abs_sub _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_pos hx0]
        have := mul_le_mul_of_nonneg_left hsing' hx0.le
        linarith

                                        
                                                                     
                                      
                                                                                 
                                                                           
                       
                      
                                              
                                                                   
                                   
                                                                           
                         
                                                                 
                                                   
              
                                                       
                                                                  
                                 
                     
                                                       
                                 
                                               
                                                                 
                                                    
                                                                                
                                
              
                                             
                                                                                                 
                                                                    
                                                                         
                                                                                              
                                                                                
                       
                                                                   
                                                          
               
                            
                                   
                              
                                       
                                                   
                                                              
                    
                                                            
                                                                       
                                                               
                                        
                                                              
                                                      
                                                         
                                                                                
                                             
                                             
                                               
                                                                          
                                          
                    

                                                                        
                                                               
            
                                                  
                                                
                                                            
                          
                                      
                                                
                                    
                                 
                                                         
                                                              
                                      
              
                                 
                                   
                                   
                           
                                                                                      
                                             
                                                      
                         
                                     
                                                                              
                                    
                                                                           
                                                              
            
               
                                       
                                                         
                                                                 
                                                                        
                                                                      
                                                          
                                   
                                                         
                                                                 
                                                                        
                                                                      
                                                           

                                                                                      
                                                                       
                                         

                                                                                             
                                                                                 
                                                     

end LeanLab.HeathBrown1985
