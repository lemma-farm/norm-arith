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

/-- One `m`: `|Σ_{n ≤ x} Λ_Q(n) Λ(m - n) - x 𝔖(m)| ≤ δ + Q + 4x (6 + 2 log F) d(m)²/F`,
`F = ⌊Q⌋`, `δ` the local error. -/
theorem per_m_bound (A K4 : ℝ) (hA : 0 < A)
    (hK4 : ∀ x : ℝ, 2 ≤ x → ∀ k l : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
      |psi x k l - (if Nat.Coprime l k then x / (Nat.totient k : ℝ) else 0)| ≤
        K4 * x * Real.log x ^ (-A))
    (x : ℝ) (hx : 3 ≤ x) (Q : ℝ) (hQ1 : 1 ≤ Q) (hQx : Q ≤ x - 1) (m : ℕ) (hm : m ∈ mRange x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n) - x * singular m| ≤
      2 * (|K4| * (3 * x) * (Real.log x / 2) ^ (-A)) *
        (Q * ((1 + Real.log x) * (Real.exp 1 * (1 + Real.log x / Real.log 2)))) + Q +
      x * (4 * ((6 + 2 * Real.log ⌊Q⌋₊) * (m.divisors.card : ℝ) ^ 2 / ⌊Q⌋₊)) := by
  have hloc := local_expansion A K4 hA hK4 x hx Q hQ1 hQx m hm
  have hm1 : 1 ≤ m := by simp only [mRange, mem_filter, mem_Icc] at hm; exact hm.1.1
  set F := ⌊Q⌋₊
  have hF1 : 1 ≤ F := Nat.le_floor (by exact_mod_cast hQ1)
  have hF : (F : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have htail := abs_singular_sub_le m F hm1 hF1
  set S := ∑ n ∈ Icc 1 ⌊x⌋₊, LambdaQ Q n * Λ (m - n)
  set Mf := ∑ q ∈ Icc 1 F, gm m q
  have hMf : |Mf| ≤ Q := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum (fun q _ => abs_gm_le_one m q)).trans ?_
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, Nat.add_sub_cancel]
    exact hF
  have hx0 : 0 < x := by linarith
  have hN1 : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [Nat.lt_floor_add_one x]
    · linarith [Nat.floor_le hx0.le]
  have e : S - x * singular m = (S - ⌊x⌋₊ * Mf) + ((⌊x⌋₊ : ℝ) - x) * Mf +
      x * -(singular m - Mf) := by ring
  rw [e]
  have h2 : |((⌊x⌋₊ : ℝ) - x) * Mf| ≤ Q := by
    rw [abs_mul]
    calc |(⌊x⌋₊ : ℝ) - x| * |Mf| ≤ 1 * Q :=
          mul_le_mul hN1 hMf (abs_nonneg _) zero_le_one
      _ = Q := one_mul Q
  have h3 : |x * -(singular m - Mf)| ≤
      x * (4 * ((6 + 2 * Real.log F) * (m.divisors.card : ℝ) ^ 2 / F)) := by
    rw [abs_mul, abs_neg, abs_of_pos hx0]
    exact mul_le_mul_of_nonneg_left htail hx0.le
  calc _ ≤ |S - ⌊x⌋₊ * Mf + ((⌊x⌋₊ : ℝ) - x) * Mf| + |x * -(singular m - Mf)| := abs_add_le _ _
    _ ≤ |S - ⌊x⌋₊ * Mf| + |((⌊x⌋₊ : ℝ) - x) * Mf| + |x * -(singular m - Mf)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

                                                      
                                                
                                                                              
                                 
                   
                                                         
                                                           
                                                 
                                
                                                                        
                                 
                                                                            
                                       
                             
                                                     
                                               
                                            
            
                                                                                              
                                                                                       
                                            
                                         
                                                                                                        
                                           

                                                       
                                                                    
                                                    
                                                                                              
                                                                                     
                            
                     
                      
                                              
                                                       
                                 
                                 
                           
                                                   
                                                                                      
                               
                                                      
                                                                                                  
                                      
                                           
                                                          
                                                           
            
                                                                     
                                                          
                                                                                
                                                               
                                                      
                                                          
                                                             
                                                                 
                      
                                                    
                                                                                  
         
                                                  
                                                         
                                                           
                                                          
                                                           
                                                                                              
                                                                       
                                             
                             

                                           
                                                                                          
                  
                                                                              
                                                                              
                     
                
               
                      
                                              
                                                       
                                 
                                 
                                 
                                                          
                                                 
                                               
                            
                                  
            
                                       
                                                                          
                                                                
                                                                                   
                                                                       
            
                                                     
                                                           
                                                                                   
             
                                                          
                                                                                      
                                          
                                            
             
                                               
                                                                   
                    

                                                                   
                                                    
                                                            
                                                                              
                                               
                                                                         
                                                                                 
                                                                           
                                                                                               
                                        
                                                      
                                    
                                    
                                                          
                     
                
                                 
                                 
                                                
                                 
                             
               
                                         
             
                                                             
                                                                                            
                                                                           
              
                                                                               
                                                            
                                                                                               
                                                  
                                                          
                                                             
            
                                   
                                                          
                                       
                                                
                                         
                                       
                                                
                                                                  
                                                 
                                                                               
              
                                                                      
                                                                     
              
                    

                                           
                                              
                                                           
                                             
                                                        
             
                                                      
                                               
                      
           

                                   
                                                                        
                                                                                 
                                                                               
                                               
                              
                                 
                                                            
                         
                                            
                                                                                             
                                                                  
                                                                                            
                                            
                                                                                           
               
                                                                       
                                                    
                                                   
                                                            
                                                             
                                    
                                                                               
                                                                                      
                          
                                     
                                            
                                                                
                                                       
                                                              
                                                                                        
               
                                    
                                                       
                

                                        
                                                                     
                                      
                                                                                 
                                                                           
                       
                      
                                              
                                                                   
                                   
                                                                           
                         
                                                                 
                                                   
              
                                                       
                                                                  
                                 
                     
                                                       
                                 
                                               
                                                                 
                                                    
                                                                                
                                
              
                                             
                                                                                                 
                                                                    
                                                                         
                                                                                              
                                                                                
                       
                                                                   
                                                          
               
                            
                                   
                              
                                       
                                                   
                                                              
                    
                                                            
                                                                       
                                                               
                                        
                                                              
                                                      
                                                         
                                                                                
                                             
                                             
                                               
                                                                          
                                          
                    

                                                                        
                                                               
            
                                                  
                                                
                                                            
                          
                                      
                                                
                                    
                                 
                                                         
                                                              
                                      
              
                                 
                                   
                                   
                           
                                                                                      
                                             
                                                      
                         
                                     
                                                                              
                                    
                                                                           
                                                              
            
               
                                       
                                                         
                                                                 
                                                                        
                                                                      
                                                          
                                   
                                                         
                                                                 
                                                                        
                                                                      
                                                           

                                                                                      
                                                                       
                                         

                                                                                             
                                                                                 
                                                     

end LeanLab.HeathBrown1985
