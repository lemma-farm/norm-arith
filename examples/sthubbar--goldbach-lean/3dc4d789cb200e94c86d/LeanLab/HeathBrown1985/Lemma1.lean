module

public import Mathlib
public import LeanLab.HeathBrown1985.Bound25

/-!
P0096 Heath-Brown 1985, Lemma 1, 2.6 and 2.7, deduced from 2.4 as on pages 48 to 50.
2.4 is the named input `Bound2_4`; 2.1 is replaced by `k/φ(k) ≤ e(1 + ω(k))` and
`σ(q)/q ≤ 1 + log q`, both proved.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/

@[expose] public section

noncomputable section
namespace LeanLab.HeathBrown1985

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

attribute [local instance] Classical.propDecidable

/-! ### Counting `n ≤ N`, `n ≡ l (k)`, `d ∣ n` -/

                                     
                                                                 
                                
                                                                                          
                                                                                            
                                                                                        

                                                                              
                                                  
                                                                  
                                          
                          
                                              
                          
                                    
                  
                                        
                                    
                                    
                          
                           
                                                                                      
                                                           
                
                                            
                                                       
                                              
                                            
                                             
             
                               
                                  
                                                              
                                                                      
                                       
                                  
                         
                                               
                      
                                                                                                    
           
                  

                                                                 
                                  
                                                             

                                                                                       
            
                                        
                     
         
                                                               
                                                                                    
                                                                                         

                                                                                 
                           
                                                             
                      
                                       
                                          
                                                                         
                                                      
                                                                 
           
                                                    
                 
                                                            
                                     
                                          
                 
                                                                         
                                                                 
                         
                       
                                                                                    
                                                                 
                                                 
                                           
                                                 
                                                                                   
                                                    
                                           
                          
              
                                                          
                                                    
                                                                     
                                                            
                                              
                                                                                 
                                                       
                                              
                                  
                                               
            
                                                                              
                                                                          
                                                       
                                    
                                                                                         
                                       

                                                   

                                                 
                                            
                                                                                           

                                             
                                                                       
                 

                                                               
                                                      
                                                    
                                                                                     
                                                               
                                                                                    
                                                        
                                                                        
         
                                                                 
                                                                                                     
                                                                                          
                                                                                
                                                                                

                                                 
                                                                    

                                                      
                                                             
             
                                                                  

                                                                                            
                                  
                                                                                                   
                                                                 
                                                        
                 

                                                                 
                                                   
                                                       

                                                                       
theorem sum_sqfree_divisors_prod (k : ℕ) (hk : k ≠ 0) (c : ℕ → ℝ) :
    ∑ q ∈ k.divisors.filter Squarefree, ∏ p ∈ q.primeFactors, c p =
      ∏ p ∈ k.primeFactors, (1 + c p) := by
  rw [Nat.sum_divisors_filter_squarefree hk, prod_one_add]
  have e : (UniqueFactorizationMonoid.normalizedFactors k).toFinset = k.primeFactors := by
    rw [Nat.factors_eq]; rfl
  rw [e]
  apply sum_congr rfl
  intro t ht
  rw [mem_powerset] at ht
  have hprime : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
  have : t.val.prod = ∏ p ∈ t, p := by rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  rw [this, Nat.primeFactors_prod hprime]

/-- `q/φ(q) = Π_{p ∣ q} p/(p - 1)`. -/
theorem div_totient_eq_prod (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) / (Nat.totient q : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hP : ∀ p ∈ q.primeFactors, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have keyR : (Nat.totient q : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ) =
      (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors q)
    push_cast at this
    rw [this]; congr 1; apply prod_congr rfl; intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).one_le
    push_cast [this]; ring
  have hpos : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) :=
    prod_pos (fun p hp => by linarith [hP p hp])
  rw [prod_div_distrib, div_eq_div_iff hφ.ne' hpos.ne']
  linarith [keyR]

/-- `φ(q) = Π_{p ∣ q} (p - 1)` for squarefree `q`. -/
theorem totient_eq_prod_of_squarefree (q : ℕ) (hq : Squarefree q) :
    (Nat.totient q : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq.ne_zero
  have h1 := div_totient_eq_prod q hq1
  have hP : ∀ p ∈ q.primeFactors, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hpos : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) :=
    prod_pos (fun p hp => by linarith [hP p hp])
  have hqP : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) (Nat.prod_primeFactors_of_squarefree hq)
    push_cast at this; exact this.symm
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [prod_div_distrib, ← hqP, div_eq_div_iff hφ.ne' hpos.ne'] at h1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  nlinarith

                                   
                                                            

                                          
                                                      
                                                                        
                    
                                                                    
                                                         
               
                         
             
                                                                
                                                            
                                            
                       
                                                                       

                                                                                        
                                              
                                            
                              
             
                                                 
                                                                                           
                             
                       
             
                                                                            

                                         
                                                                          
                                                                        
                                            
                                                  
                                                        
              
                                                
                                              
                                                         
                                             
               
                                     
                    
                      
                      
                        
                   
                                 
                                    
               
             
                                              
                                  
                                        
                                                                           
                                            
                                
              
                              
                        
                                                                  
                               
                                      

                                                                        
                                                                                           
                                                  
                                                               
                                                           
                                                          
                                                                                    
                                      
                                                                                                  
                                                            
                                                              
              
                                                
                                                         
                                             
               
                                            
                    
                                                                            
                                                                                
                                                              
                                                          
                                          
                                                                    
                                    
                                                         
                                                                              
                                                                 
                                                                                 
                                  
                                                                                    
                  
                                                                           
                                                                     
                               
                                                                                             
                         
                             
                                                           
                                                                                                
                                                                                            
                                                               
                
                                 
                                                                                  
                                   
                  
                                                                                          
                                              
                                                              
                                                                
                                 
                               
                                                                                
                                                             
                                                                
                                                                
                                 
                               
                                                                                
                                                             
                                            

                                     
                                                                                      
                                                                     
                                           
                                                 
                                                              
                                                     
                                 
                                                                     
              
                                                  
                                                                 
                                                  
                                                   
                                 
                                                                                        
                            
                                          
                                                                           
                                       
                                    
                                    
                                      
                                                       
                              
                                        
                                                                  
                                     
                                                                                   
                                                        
                                                                                         
                                                           
                            
                                                                
                 
                                                         
                                            
                                                                  
                     
                            
                                           
                                                                        
                                      
                      
                    
                                                  

                                                                                           
                                               
                                                                        
                                                                      
                                                                        
                                                
               
                                                                                       
                                          
                                                                                
                                               
                   
           
                                                               
                 
                                                                     
                                  
                                                                     
                    
                  
               
                                                                         

                              
theorem sigma_le (q : ℕ) (hq : 1 ≤ q) :
    ∑ d ∈ q.divisors, (d : ℝ) ≤ q * (1 + Real.log q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have e : ∑ d ∈ q.divisors, (d : ℝ) = ∑ d ∈ q.divisors, ((q / d : ℕ) : ℝ) := by
    rw [Nat.sum_div_divisors q (fun d => (d : ℝ))]
  rw [e]
  calc ∑ d ∈ q.divisors, ((q / d : ℕ) : ℝ) = ∑ d ∈ q.divisors, (q : ℝ) * (d : ℝ)⁻¹ := by
        apply sum_congr rfl; intro d hd
        rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by exact_mod_cast
          (Nat.pos_of_mem_divisors hd).ne')]
        ring
    _ = q * ∑ d ∈ q.divisors, (d : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ q * ∑ d ∈ Icc 1 q, (d : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hqR.le
        apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
        intro d hd
        simp only [mem_Icc]
        exact ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
    _ ≤ q * (1 + Real.log q) := mul_le_mul_of_nonneg_left (sum_inv_Icc_le_log q) hqR.le

/-! ### Lemma 1 from 2.4 -/

                          
                                   
                                                                                

                                                                                
                            
             
                  
                                           
                                    

                                              
                                                                                       
                                                                     
                      
               
                                 
                               
                         
                                                               
                                                     
                                                                  
              
                                                   
                                                  
                       
                                         
                                                                                   
                                  
                                                          
                                            

                                                               
                                                       
                                                          
                                                               
                                                                  
                                                   
                                
             
                                                            
                                 
                                                
                                                 
                                                
                                  
             
                  
                    
        

                                                                         
                                                              
                                                               
                                                                                   
                                          
              
                              
                               
                                                                                       
                                   
                                                                                        
                                                      
                                                                     
                                                                             
                                               
                                                                     
                                         
                                            
                                              
                                                  
                                       
                                                                                        
                                            
                                          
                                                                    
                                                                                         
                                
                                 
                                                                                                   
                                                                    
                                                         
                                                                          

                                         
                                                                                              

                                                                                        
                                                           
                                                                                       
                         
                                                                                          
                                
                                                                                   
                     
                      
                                              
                                                        
                                 
                                 
                                                
                                 
                                    
                           
                                             
                                                          
                                                                                
                                                               
                                   
                                              
                              
               
                                              
                                                                           
                                    
                                                                   
                                                        
                                        
                                                                                            
             
                     
                                                                                           
                      
          
            
                                             
                                                         
                                                                                
                             
                                             
                                      
                                       
                                                         
                                                                                                 
                                   
                                               
                                                              
                                                                               
                             
                                                                  
                                                   
                                                                
                                                     
                                                                           
                                                                                        
                                                                            
                                           
                                                          
                                                           
            
                                                                            
                        
                                                                             
                                                
                                                                          
                
                      
                                                  
                                                                         
                                                            
                                                                                        
                                                         
                                                                                                   
                
                            
                                                             
                                                      
                                                                                             
                                                                              
                                                                                            
                 
                                                                         
                                                          
                                                
                                                                                                  
                 

                                
                                 
                                                       
                                          
                                                         
               

                                                                                    
                      
                                                                             
                                                                            
                               

                                  
                                                    
            
                             
                                                         
                                           
                                
                                 
                                                         
                                                                                
                                                              
                                                                 
                                                                                  
                           
        
                                                                                   
                                            
                                                      
                                                                                     
                                          
                      
                                                                             
                                                                                         
                           
                                                                                 
                                                                                      
               
                                 
                 

                                                                                            
                                 
                                                          
                                                   

end LeanLab.HeathBrown1985
