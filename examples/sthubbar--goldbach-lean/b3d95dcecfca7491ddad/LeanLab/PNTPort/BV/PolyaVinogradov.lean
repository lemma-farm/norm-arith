module

public import LeanLab.PNTPort.LargeSieve.Multiplicative

/-!
# The Polya-Vinogradov inequality

Lab proof. AI wrote this file. Known mathematics, the Polya-Vinogradov inequality of 1918,
no cited input. Uses Mathlib's Gauss sums for primitive Dirichlet characters.

For a primitive Dirichlet character `χ` modulo `q > 1` and any interval `M < n ≤ M + N`,

  `‖∑_{M<n≤M+N} χ(n)‖ ≤ √q (1 + log q)`.

Route: `χ⁻¹(n) τ(χ) = ∑_x χ(x) ψ(n x)`, so `√q ‖∑ χ⁻¹(n)‖ ≤ ∑_{0<c<q} ‖∑_n e(n c / q)‖`,
each geometric sum is at most `1/(2‖c/q‖) ≤ (q/c + q/(q-c))/2`, and the harmonic bound
`H_{q-1} ≤ 1 + log q` finishes.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Complex Finset Real LeanLab.PNTPort.LargeSieve

lemma sum_Ioc_eq_sum_range {R : Type*} [AddCommMonoid R] (f : ℤ → R) (M : ℤ) (N : ℕ) :
    ∑ n ∈ Ioc M (M + N), f n = ∑ k ∈ range N, f (M + 1 + k) := by
  refine sum_nbij' (fun n => (n - M - 1).toNat) (fun k => M + 1 + k) ?_ ?_ ?_ ?_ ?_ <;>
    intro n hn <;> simp only [mem_Ioc, mem_range] at hn ⊢
  · omega
  · omega
  · omega
  · omega
  · congr 1; omega

/-- Geometric sum over an interval. -/
lemma norm_sum_Ioc_e_le (M : ℤ) (N : ℕ) {θ : ℝ} (h : 0 < dist0 θ) :
    ‖∑ n ∈ Ioc M (M + N), e (n * θ)‖ ≤ 1 / (2 * dist0 θ) := by
  rw [sum_Ioc_eq_sum_range (fun n : ℤ => e (n * θ))]
  have : ∀ k ∈ range N, e (((M + 1 + k : ℤ) : ℝ) * θ) = e ((M + 1 : ℤ) * θ) * e (k * θ) := by
    intro k _
    rw [← e_add]; congr 1; push_cast; ring
  rw [sum_congr rfl this, ← mul_sum, norm_mul, norm_e, one_mul]
  exact norm_geom_le N h

                                                         
                                                             
                                                                                 
                                 
                        
                                              
                                      
                                                       
                                  
                                                  
                                           
                                                           
                                          
                                   
                                                         
                                                            
                                                                 
            
                                                  
                                                 
                                       
                       
                                                  
                                                           
                                   
                                                               
                                                            
                                                         
                                                     
            

                                                     
                                            
                                                                      
                                
                                                                                     
                                          
                                      
                       
                                                          
                                                  
                                                                     
                                       
                        
           
                                                                                  
                   
                                         
                                            
                                                         
                         
                                  
                         
                                   
                                             
           

                                                                             
                                         
                                                                                     
                                          
                                                                                       
                             
                                               
                       
                        
                                  
                                     
                              
                                       
                                                                              
                                
                                                              
                                                   
                                                                           
             
                                                            
         
                
                
                 
                                      
                          
                                   
                                                                          
                                                             
                                                       
              
                        
                                              
                                    
                                  
                         
                                                 
                                                                                    
                                                                     
             
             
                                                
                                                     
                                                              
                                                        
                                                                   
                                     
                                           
                                    
                 
                                                                
                                           
                                                                                         
                                             
                                   
                                                                                            
                                                                                                 
                                                                                    
                                     
                                    

                                        
                                                                                         
                                  
                                                                      
                                      
                                                                                    
                                                                                     
                                                         
           
           
           
           
          
                    

end LeanLab.PNTPort.BV
