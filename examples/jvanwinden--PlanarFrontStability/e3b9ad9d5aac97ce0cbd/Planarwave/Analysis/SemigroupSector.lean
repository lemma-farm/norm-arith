/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module

public import Planarwave.Analysis.SemigroupHolomorphic
public import Planarwave.Analysis.ComplexTimeSector
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

/-!
# Extending a holomorphic semigroup to a full time sector

Time subdivision gives local extensions on increasingly long truncated sectors.
Their real restrictions are the original semigroup, so the identity principle makes
them agree on overlaps. This supplies the full-sector continuation needed in the
analytic-semigroup part of the paper's Section 2.
-/

open Filter Set Topology Planarwave

namespace C0Semigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

                                                                      
                               
                  
                                                             
                                                              

                                                                                    
                                                                                    
                                                                 
                                              
                                                         
                                                   
                                                                    
                                             
                                                       
                                                             
                                          
           
                                                                                  
                                                                                   
                                                                     
                                                      
                                                                       
                                                                        
                                                        
              
                                                             
                                                                   
                                                  
                                                                                             
                                                          
                                         
                                                               
                                        
                                                                                      
                                                             
                                                                             
                                                                      
                     
                                                                  
                                                                          
                
                  
                                                                 
                                                         
              
                                        
                                                        
                                                         
                                                              
                                                    
                                                                                    
                                                                            
                                                      
                                           
                                        
                                                           
                              
                                                                         
                                 
                                                         
                               
                                                     
                            
              
                               
                                  
                                                    
                         
              
                                                               
                                          
              
                                                        
                                                                     
                       
                               

                                                                             
                                                                 
                                              
                                                  
                                                 
                                                                 
                                                     
                      
           
        
                                                       
                                                                                     
              
                                                                                          
                                                                     
                                                                                              
              
                                                                                                     
                                                                                                         
                                                                 
            
                            
                                                                         
                                             

                                                                                
                                                                                       
                                                            
                                              
                                                  
                                                 
                                                                             
                                      
                                                                               
              
                                                       
                                                               
                                                                                     
              
                                                                                     
                                                                                                         
                                                                 
            
                            
                                                                                   

                                                                               
                                                                              
                                                                                        
                                                                  
                                              
                                                  
                                                                 
                                                       
                                                                              
                                                                                 
              
                                                                                        
                                                                                  
              
                                                                                 
                                                                                                         
                                                                 
            
                            
                    
                        

omit [CompleteSpace E] in
/-- A bound on the initial time neighborhood becomes an exponential bound on the
whole sector. The constants depend only on the initial bound, not on time. -/
theorem norm_holomorphicSectorExtension_le {η M : ℝ} (hM : 0 ≤ M)
    {g G : ℂ → (E →L[ℂ] E)}
    (hbound : ∀ z ∈ positiveTimeNeighborhood η, ‖g z‖ ≤ M)
    (hdivide : ∀ z ∈ complexTimeSector η, ∀ n : ℕ, 0 < n → z.re < n →
      G z = (g (z / (n : ℂ))) ^ n)
    {z : ℂ} (hz : z ∈ complexTimeSector η) :
    ‖G z‖ ≤ Real.exp M * Real.exp (M * z.re) := by
  let n : ℕ := ⌊z.re⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hzn : z.re < n := by simpa only [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one z.re
  have hnle : (n : ℝ) ≤ z.re + 1 := by
    dsimp only [n]
    push_cast
    linarith [Nat.floor_le hz.1.le]
  have hzdiv : z / (n : ℂ) ∈ positiveTimeNeighborhood η := by
    apply mem_positiveTimeNeighborhood_of_sector
      (by simpa only [Complex.ofReal_natCast] using div_real_mem_complexTimeSector hz hnreal)
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_re]
    exact ((div_lt_one hnreal).mpr hzn).le
  rw [hdivide z hz n hn hzn]
  calc
    ‖g (z / (n : ℂ)) ^ n‖ ≤ ‖g (z / (n : ℂ))‖ ^ n := norm_pow_le' _ hn
    _ ≤ M ^ n := pow_le_pow_left₀ (norm_nonneg _) (hbound _ hzdiv) n
    _ ≤ (Real.exp M) ^ n := pow_le_pow_left₀ hM (by linarith [Real.add_one_le_exp M]) n
    _ = Real.exp (M * n) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (M * (z.re + 1)) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnle hM)
    _ = Real.exp M * Real.exp (M * z.re) := by rw [mul_add, Real.exp_add, mul_one, mul_comm]

omit [CompleteSpace E] in
                                                                              
                                                  
                                                       
                           
                                                           
                                                                                            
                                                                  
                                                                    
                                                          
                                                                                   
                                                                
                                             
                                    
                                                        
                                                              
                                                          
                                    
                                                            
                                                               

end

end C0Semigroup
