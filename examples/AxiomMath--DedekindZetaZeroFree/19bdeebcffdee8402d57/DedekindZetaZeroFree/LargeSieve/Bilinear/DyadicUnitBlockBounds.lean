module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DyadicNormBlocks
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

                                                                  
                           
                                                                
                                                              
                                                                          
                                                                                
                    
                                                                                         
               

private theorem squarefree_top_ideal : Squarefree (⊤ : Ideal (𝓞 F)) := by
  have h : (⊤ : Ideal (𝓞 F)) = 1 := Ideal.one_eq_top.symm
  rw [h]
  exact squarefree_one

                                                
                                                                                  
                             
                                         
                                          
                                               
                           
                                                              
                                  
             
                                                          
        
                                     

private theorem unit_column_bound (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (S : Finset (Ideal (𝓞 F)))
    (lam : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ S, ‖∑ _b ∈ ({⊤} : Finset (Ideal (𝓞 F))), lam _b * (Q.χ _b) a‖ ^ 2) ≤
      (S.card : ℝ) * ‖lam ⊤‖ ^ 2 := by
  have hbound : ∀ a ∈ S,
      ‖∑ _b ∈ ({⊤} : Finset (Ideal (𝓞 F))), lam _b * (Q.χ _b) a‖ ^ 2 ≤ ‖lam ⊤‖ ^ 2 := by
    intro a _
    rw [Finset.sum_singleton, norm_mul, mul_pow]
    have h1 : ‖(Q.χ ⊤) a‖ ^ 2 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (quadraticFamily_norm_le_one Q squarefree_top_ideal (by simp) a)
    calc ‖lam ⊤‖ ^ 2 * ‖(Q.χ ⊤) a‖ ^ 2 ≤ ‖lam ⊤‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = ‖lam ⊤‖ ^ 2 := mul_one _
  calc (∑ a ∈ S, ‖∑ _b ∈ ({⊤} : Finset (Ideal (𝓞 F))), lam _b * (Q.χ _b) a‖ ^ 2)
      ≤ ∑ _a ∈ S, ‖lam ⊤‖ ^ 2 := Finset.sum_le_sum hbound
    _ = (S.card : ℝ) * ‖lam ⊤‖ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

                                                                          
                                                                                                          
             
                                                                       
              
        
                                                                                  
             
            
                                             
                                             
                                                                               
              
                                                    
                                                                                    
                                   
                
                                                  
                                         
                  
                                                  
                                                                                                               
                                        

                                                                           
                                            
                                                               
                                            
                                                 
                                 
                                 
                                            
                                                              
                                             
                                      
                                         
                                                                 
                                                 
                                           
                                            
                                                                      
                                             
                                                    
                                                                           
                                                          

                                                                             
                                                         
                                                                                     
                                            
                                 
                                 
                                             
                                                         
                                       
                                                              
                                       
                                                                                  
                                       
                                        

                                                                                      
                                                         
                                                                   
                                                                   
           
             
                                    
                                                                                       

                                            
                                         
                           
          

                            
                                        
                                                                         
                                                                  
                              
                                                                                 
                                                                 
                              
                                                          
                                 
                                              
                                       
                                    
                                                                
                                                             
                                         
                                                       
               
                     
                       
     
                                                                     
                                                            
                                                       
     
                                               
                                                                      
                                                  
                                                             
                                                        
                                                                   
                                                               
                                                                                
                                                              
                                                             
                                                                               
                       
     
                                               
                                              
                                                             
                                                        
                                                                   
                                                               
                                                                                   
                                                              
                                                             
                                                   
     
                                                                 
                                                         
                                                 
                                                         
                                                                 
                                                          
                                                 
                                                    

end DedekindZetaZeroFree.LargeSieve.Sieve
