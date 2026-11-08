import DeterminantCountWeld

/-!
# Unconditional foundation for the Shiu determinant-fiber input

The analytic theorem still missing from this file is recorded as the proposition
`DyadicTauSquareShiuTarget`; it is not postulated as an axiom.  Its interval is
written by its upper endpoint `x` and length `y`, so the reduced interval
`(N / d, (2 * N) / d]` is represented literally, without pretending that
integer division commutes with doubling.
-/

namespace ShiuFoundation

open ArithmeticFunction MixedMellinCert DeterminantCountWeld
open scoped ArithmeticFunction.zeta

                                                                           
                                                                    
                                             
                                    
                             
                                                

                                                                         
                                                                        
                                                                      
                                                                 
                                                            

                                                                           
                                                                             
                                  
                                       
                  
                                
                                
                
                     
                           
                                 
               
                   
                             
                                                           
                                 
                                                   

                                                               
theorem tauAF_isMultiplicative (r : ℕ) : (tauAF r).IsMultiplicative := by
  induction r with
  | zero => simpa [tauAF] using
      (ArithmeticFunction.isMultiplicative_one :
        (1 : ArithmeticFunction ℕ).IsMultiplicative)
  | succ r ih =>
      rw [tauAF, pow_succ']
      exact ArithmeticFunction.isMultiplicative_zeta.mul ih

                                                                     
                                                                    

                                                  
theorem tauAF_prime_pow_eq_multichoose (r e p : ℕ) (hp : p.Prime) :
    tauAF r (p ^ e) = r.multichoose e := by
  induction r generalizing e with
  | zero =>
      cases e with
      | zero => simp [tauAF]
      | succ e =>
          have hpow : p ^ (e + 1) ≠ 1 :=
            (Nat.one_lt_pow (Nat.succ_ne_zero e) hp.one_lt).ne'
          simp [tauAF, ArithmeticFunction.one_apply, hpow, hp.ne_one,
            Nat.multichoose_zero_succ]
  | succ r ih =>
      rw [show r + 1 = Nat.succ r by omega, tauAF_succ_apply]
      rw [Nat.divisors_prime_pow hp, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, ih]
      rw [Nat.sum_range_multichoose]
      simpa [Nat.multichoose_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.choose_symm_add (a := e) (b := r)).symm

                                                                          
                                       
                                                 
              
                
             
                                    
           

                                                                
                                            
                                                                   
                                   
           
                  
                    
                 
                      
                        
                     
                                                                    
                                              
                 
                      
                    
                     
                                                    
                                                               
                                                             
              
                                                                       
                                                         
                                                                  
                                                
                                                               
                                                                     
                    
                                           
                                                                         
                                                         

                                                                       
                                                                              
theorem multichoose_le_pow (r e : ℕ) : r.multichoose e ≤ r ^ e := by
  induction r generalizing e with
  | zero =>
      cases e <;> simp [Nat.multichoose_zero_succ]
  | succ r ihr =>
      induction e with
      | zero => simp
      | succ e ihe =>
          rw [Nat.multichoose_succ_succ, pow_succ]
          calc
            r.multichoose (e + 1) + (r + 1).multichoose e ≤
                r ^ (e + 1) + (r + 1) ^ e := Nat.add_le_add (ihr (e + 1)) ihe
            _ ≤ r * (r + 1) ^ e + (r + 1) ^ e := by
              gcongr
              calc
                r ^ (e + 1) = r ^ e * r := pow_succ r e
                _ ≤ (r + 1) ^ e * r :=
                  Nat.mul_le_mul_right r (Nat.pow_le_pow_left (Nat.le_succ r) e)
                _ = r * (r + 1) ^ e := by ac_rfl
            _ = (r + 1) ^ (e + 1) := by rw [pow_succ]; ring

/-- Prime-power growth for the literal square weight passed to Shiu. -/
theorem tauAF_square_prime_pow_le (k e p : ℕ) (hp : p.Prime) :
    tauAF k (p ^ e) ^ 2 ≤ (k * k) ^ e := by
  rw [tauAF_prime_pow_eq_multichoose k e p hp, mul_pow]
  simpa [pow_two] using Nat.mul_le_mul (multichoose_le_pow k e)
    (multichoose_le_pow k e)

                                                                         
                                               
                                                  
                                                            

                                                                
theorem tauAF_eq_factorization_prod (r n : ℕ) (hn : n ≠ 0) :
    tauAF r n = n.factorization.prod (fun _ e ↦ r.multichoose e) := by
  rw [(tauAF_isMultiplicative r).multiplicative_factorization (tauAF r) hn]
  apply Finsupp.prod_congr
  intro p hp
  exact tauAF_prime_pow_eq_multichoose r _ p
    (Nat.prime_of_mem_primeFactors (by simpa using hp))

                                                                     
                                
                                                            
                                              
                                          
                                                
           
                                
                                                                  
                            
                                                               
                            
                                                                
                            
                              
                            
            
                               
                                            

                                                                                 
                                             
                                                 
                                   
        
                                   
        
                                                                    
                                                                           
                                
                                                                     

                                                         
                                                                
                                                 
                                             
                                                                       

                                                                            
                                                                           
                                                                
                                                                                 
                                                                                
                                                   
                                                       
                                                          

                                                           
                                                
                                              

                                                                       
                                                            
                                                                         
                                              
                                                
                                          
                                            
             
                                                                
              
                                   

                                                                           
                        
                                                      
                              
                                       
                                                                        
                                               
                                   
                                             

                                                                         
         
                                                                   
                                                 
                                                
                       
                       
                         
                                      
                                      
                                   
                                   
                                                  
                                                      
       
                                                                         
                                  
                
                                
                                  
                 
                                
                                                      
                                                         
                                                      
                                                         
                                                                
                                                                
                                                                                
                                                                        
                                                                           
                                                                                
                                                                        
                                           
                                                          
                                                             
                                             
                                             
                                                      
                                          
        
                                           
                                                          
                                                   
                               
                                                                     
            
                         
                                             
                                                                         
                          
                                          
        
                                                             
                             
                
                                                       
                                                          
                                         
                             
                                                   
            
                                                                      
                          

                                                                         
                                            
                                                                   
                                                 
                                                
                       
                       
                         
                                      
                                      
                                   
                                   
                                                  
                                                      
                                                                 
                                                            
                                
                                
                                                      
                                                   
                                                            
                                                        
                                                        

                                                                        
                                                                           
                                                                    
                                                            
                                                             
                                  
                                      
                         
                                     
                                                  

                                                                        
                                           
                                                                     
                                           
                         
                         
                                      
                                      
                                   
                                    
                                           
                         
                         
                                      
                                      
                                   
                                    
                                                    
                                                
                                                                
                                                                
                                                    
                                                
                                                                
                                                                    
                                                                       
              
                                            
                                                  
                            
              
                                            
                                                  
                            

end ShiuFoundation
