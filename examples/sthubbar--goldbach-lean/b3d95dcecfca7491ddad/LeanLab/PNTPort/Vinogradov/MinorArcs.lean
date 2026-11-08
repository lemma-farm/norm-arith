module

public import LeanLab.PNTPort.Vinogradov.Final
                                        

/-!
# Minor arcs: the sup bound and the unconditional minor arc exceptional count

Lab proof, unit U-5251. AI wrote this file. Known mathematics, no cited input: the minor arc
half of the Estermann, Chudakov, van der Corput theorem, Montgomery-Vaughan 1975 style.

* `MinorAt P Q α`: no `a/q` with `q ≤ P` has `|α - a/q| ≤ 1/(q(Q + 1))`.
* `minor_sup`: for `1 ≤ P`, `1 ≤ Q ≤ N` and `α` minor,
  `‖S(α)‖ ≤ 300 (N/√P + N^{4/5} + √(NQ)) (1 + log N)⁴`, from Dirichlet's theorem and
  `vinogradov_minor`.
* `dft_PhiL_norm`: on `ZMod M`, `M > N`, the DFT of `n ↦ Λ(n) 1_{1 ≤ n ≤ N}` has modulus
  `‖S(k/M)‖`.
* `minor_exceptional`: with `m` the minor frequencies `k`, `k/M` minor, and `T ≥ 0`,
  `#{n mod M : ‖∑_{k ∈ m} S(k)² e(nk/M)‖ ≥ T} · T² ≤ M² B² ∑_{n ≤ N} Λ(n)²`, `B` the sup bound.
  The minor arc part of the binary count `∑_{a + b = n} Λ(a)Λ(b)` is small for all but few `n`;
  the major arcs still need Siegel-Walfisz. Binary Goldbach is OPEN.
-/

@[expose] public section


namespace LeanLab.PNTPort.Vinogradov

open Complex Finset Real ZMod
open LeanLab.PNTPort.LargeSieve

/-- `α` is on the minor arcs: no fraction `a/q` with `q ≤ P` is within `1/(q(Q+1))`. -/
def MinorAt (P Q : ℕ) (α : ℝ) : Prop :=
  ∀ (a : ℤ) (q : ℕ), 1 ≤ q → q ≤ P → 1 / ((q : ℝ) * (Q + 1)) < |α - a / q|

                                           
                                                      
                                                            
                                                 
                                                                                          
                                  
                                                            
                                                
                                                 
                       
                         
                            
                                   
             
                                                                                              
           
                                    
                                                                
                     
                                                                                        
                                                                                          
                        
                                            
                                       
                                                  
                                 
         
                                                                                
                                                    
                                                                        
                                      
            
                                                   
                                                        
                                               
                                                            
                                                           
                                     
                            
                                                  
                                                    
                                                                                                  
                     
                                                                   
                                                       
                                               
                                                  

                                            
                                                                             
                         
                                                                                           
                                
                                                             
                        
                 
                                                     
                                                 
                                                
                      
                                
                                                 
              
           
                                                                                                 
                                                                    
                                          
                                                 
                                       
                                                 
                                                         
                                                       
                                              
                                                      
                                                       
                           
                                                                               
          

                                                                      
          
              
                                    
                                                   

                                                             
                               

                                                   
                                                
                                                                                          

                                                        
                                                    
                                                                          
                                                
                               
                                            
              
                                                 
                  

                                                             
                                                    
                                                                          
                                                
                               
                                            
              
                                                 
                  

                                                                  
                                                                             
                                               
                                                             
                                                  
                                                 
          
         
           
      

                                                                  
                                                 
                
                                                                                         
                                                                          
                                        
                               
        
          
                                                                     
                                                            
                               
                       
                                    
                                   

                                                                       
                                                    
                                        

                                                        
                                                                                     
                                                     
                                                                                
                  
        
                                                                     
                                                            
                       
                                    
           
                                                    
        

                 
                                     
                                                                      
                                                               

                                                          
                                                                                          
                                        
                          
                                                                                             
                                                                               
                                                          
                                                                 
                                                                   
                                                           
                                                                                             
                                                                                           
              
                                                 
                                                               
                                        
                                                          
                                                                                   
                                                                                        
             
                                                     
                                                                
                              
                                                           
                                                                       
                                                                     
                                                         
                                                             
                                                                                       
                                                                                                 
                            
                    

                                                                                          
                                                                                  
example (Q : ℕ) (hQ : 2 ≤ Q) : MinorAt 1 Q (1 / 2) := by
  intro a q hq1 hqP
  have hq : q = 1 := by omega
  subst hq
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have h1 : (1 : ℝ) / 2 ≤ |1 / 2 - (a : ℝ) / ((1 : ℕ) : ℝ)| := by
    simp only [Nat.cast_one, div_one]
    rcases le_or_gt a 0 with h | h
    · have : (a : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
    · have : (1 : ℝ) ≤ a := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
  have h2 : (1 : ℝ) / (((1 : ℕ) : ℝ) * (Q + 1)) < 1 / 2 := by
    simp only [Nat.cast_one, one_mul]
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

end LeanLab.PNTPort.Vinogradov

