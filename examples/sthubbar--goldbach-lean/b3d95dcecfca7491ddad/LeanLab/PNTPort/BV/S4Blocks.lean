module

public import LeanLab.PNTPort.BV.TypeI

/-!
lab proof, AI wrote this file, known mathematics, no cited input

`S4_eq_blocks`: the Vaughan Type II sum `S₄` as a sum of dyadic blocks
`∑_{M < t ≤ 2M} ∑_{v < r ≤ v + N/M} [t r ≤ x] Λ(t) g_v(r) χ(t r)`, `M = u 2^j`.
-/

@[expose] public section


namespace LeanLab.PNTPort.BV

open Finset ArithmeticFunction

variable {q : ℕ}

                                 
                                                                                   
                                                                                             
        

                        
                                                                              
                                                          

                                                                                      
                                                
            
                       
          
         
                         
       

                                                                             
                                                                              
               
           
                                                                                             
                                                               
                                                          
                       
                                     
                                      
                    
                                                        
                                                         
           
                                                                         
                 
                             
                                                     
                                                         
             
                             
                                                          
                                  
                                                                                               
                                                   
                                                      
                                                                             
                     
                                        
                               
               
                                     
            
                                                  
                                                          
                                                                             
                     
                                        
                
                                                                            
                      
                    
                     
             
              

lemma sum_Ioc_dyadic {M : Type*} [AddCommMonoid M] (f : ℕ → M) (u J : ℕ) :
    ∑ t ∈ Ioc u (u * 2 ^ J), f t = ∑ j ∈ range J, ∑ t ∈ Ioc (u * 2 ^ j) (u * 2 ^ j + u * 2 ^ j), f t := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ← ih, show u * 2 ^ (J + 1) = u * 2 ^ J + u * 2 ^ J by ring]
    rw [sum_Ioc_consecutive _ (by nlinarith [Nat.one_le_two_pow (n := J)]) (by omega)]

                                                  
                                                                              
                                                          
                                                                                
               
                           
                                                                     
                      
      
                 
                                                 
                     
              
                                                           
                        
                                                     
                   
         
                     
                                    
            
                                     
                    
                                     
                                              
      
                                                     
               
                                               
                      
                
              
                
                                                                                          
                                                                                       
                 
       

end LeanLab.PNTPort.BV
