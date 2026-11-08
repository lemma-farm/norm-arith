module

public import CookMagyar.SingularSeries
public import CookMagyar.PrimePowerTail

@[expose] public section

/-!
# Prime local-factor decomposition

This file records the exact reindexing needed to combine the prime-modulus
estimate with the higher-prime-power tail.  The summability hypothesis is
explicit: later arithmetic modules must discharge it rather than hiding it in
an Euler-product assumption.
-/

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

open scoped BigOperators

theorem primeLocalFactor_eq_prime_add_higherTail
    {p n T : ℕ}
    (hsum : Summable (fun k : ℕ ↦
      singularSeriesTerm n T (p ^ (k + 1)))) :
    primeLocalFactor p n T =
      1 + singularSeriesTerm n T p +
        ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2)) := by
  let f : ℕ → ℂ := fun k ↦ singularSeriesTerm n T (p ^ (k + 1))
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hshift : (∑' k : ℕ, f (k + 1)) =
      ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2)) := by
    apply tsum_congr
    intro k
    simp [f, Nat.add_comm, Nat.add_left_comm]
  have hfirst : (∑ i ∈ Finset.range 1, f i) = f 0 := by
    simp [f]
  unfold primeLocalFactor
  rw [show (∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 1))) = ∑' k : ℕ, f k by rfl]
  rw [← hsplit, hfirst, hshift]
  simp [f, Nat.pow_succ]
  ring

theorem primeLocalFactor_eq_prime_add_higherTail_of_large_prime
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    primeLocalFactor p n T =
      1 + singularSeriesTerm n T p +
        ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2)) := by
  have htailNorm :=
    CookMagyarPrimePower.summable_norm_singularSeriesTerm_higherPrimePower
      (T := T) hp hp5 hn
  have htail : Summable (fun k : ℕ ↦
      singularSeriesTerm n T (p ^ (k + 2))) := by
    apply Summable.of_norm
    exact htailNorm
  apply primeLocalFactor_eq_prime_add_higherTail
  apply (summable_nat_add_iff 1).mp
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem norm_primeLocalFactor_sub_one_le_large_prime
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    ‖primeLocalFactor p n T - 1‖ ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 +
        ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
          (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2) /
            (1 - ((p : ℝ)⁻¹) ^ (n - 2)) := by
  have hsplit := primeLocalFactor_eq_prime_add_higherTail_of_large_prime
    (p := p) (n := n) (T := T) hp hp5 hn
  have htailNorm :=
    CookMagyarPrimePower.summable_norm_singularSeriesTerm_higherPrimePower
      (T := T) hp hp5 hn
  have hn32 : 32 ≤ n := by omega
  have hprime := norm_singularSeriesTerm_prime_le_inv_pow hp hp5 hn32 T
  have htail :=
    CookMagyarPrimePower.tsum_norm_singularSeriesTerm_higherPrimePower_le
      (T := T) hp hp5 hn
  rw [hsplit]
  calc
    ‖1 + singularSeriesTerm n T p +
        ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2)) - 1‖ =
        ‖singularSeriesTerm n T p +
          ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2))‖ := by
            congr 1
            ring
    _ ≤ ‖singularSeriesTerm n T p‖ +
          ‖∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2))‖ := norm_add_le _ _
    _ ≤ ‖singularSeriesTerm n T p‖ +
          ∑' k : ℕ, ‖singularSeriesTerm n T (p ^ (k + 2))‖ := by
            gcongr
            exact norm_tsum_le_tsum_norm htailNorm
    _ ≤ (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 +
        ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
          (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2) /
            (1 - ((p : ℝ)⁻¹) ^ (n - 2)) := by
            exact add_le_add hprime htail

                                                            
                                                                       
                                       
                                                      
                                                 
                                                 
                                             
                                                            
                                        
                                                                 
                            
                             

                                                   
               
                                                    
                                         
                                                              
                                                                      
              
                                         
          

                                                                  
                                                                     
                                          
                                  
                                                      
                                                      
                                                      
                                                            
                                        
                                    
                                                                      
                                               
                                      
                                  
                                                       
                                                  
                              
             
                                       
                                                                               
                                       
                                                                  
                                           
                                                     

                                      
                                           
                                       
                                         
                         
                                                           
                                
                                                               
                                           
                                    
                                                          
                                                           
      
                                                          
                                 
                            

                                          
                                           
                           
                                                   
                                         
                         
                                                           
                                
                                                                 
                         
                                                     
                                               
                      
                                                       

                                             
                                           
                                                  
                                              
                                                    
                                                                      
                                                          
        

                                              
                                           
                                                  
                                              
                                                    
                                                      
                                                           
                                   
                                                        
                                          
                                                                     
                     
             
      
                                                  
                                                
                                                    
                                                                        
                                                      
                                  
                                                  
                                                      
                                                            
            
                                                      
                                                           

                                          
                           
                                                 
                                         
                              
                                                
                                            
                                          
                  
                                                   
                                   
                                                     
                                           
                                      
                
                                                         
                                     
                    
          
                 
                                                   
                                     
                    
          
        
                                
                                                          
                                 
                                         
                                                     
                                                
                                                       
                            
                
                
      
                                           
                                              
                                         
                                                                   
                         
                        

                                               
                                           
                                                  
                                              
                         
                                                              
                                                     
                                                                    
                      
      
                                                  
                                                
                                                    
                                                          
                                                      
                                                           
                                                

                                                          
                                                                       
                                  
                                                      
                           
                                                                          
                                        
                                           
                                                              
                                           
                                                     

                                                 
                                                                       
                                  
                                                
                           
                                                                  
                                        
                                   
                                                        
                                          
                                           
                                 
                          
               
                                                    
                                                                 
               
                                                      
                                                                
                                                                      
        
                                                      
                                                                  
                                        
                                                               
                                               
      
                                  
                                                        
                                
                                                            
                                                   
                                                  
                                

                                                        
                                                                     
                                                        
                          
                                         
                                                         
                                        
                                                  
                                                
                           
                                                                           
                                                                           

                                                   
                                                                     
                                                                       
                                         
                                            
                                                        
                         
                                                          
                             
                  
                    
                                                
             
                                                                         

                                      
                          
                                                   
                                               
                
             
                                                  
                                                        
                                                           
                                                         
           

                                                   
                            
                             
                                                              
                                      
            

                                                                     
                                                                       
                                  
                                                      
                                                      
                                                      
                                                                            
                                           

end CookMagyarFiniteFourier
end SystolicGrowth
