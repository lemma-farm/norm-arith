module
public import Z3Net.Defs
public import Mathlib
@[expose] public section

/-!
# Net property: generic lemmas

* base-`q` digit sums: the integer `∑_j f_j q^(m-1-j)` divided by `q^e` determines the first
  `m - e` digits;
* a Niederreiter-type lemma (`lem:nie`): if every box matrix acts injectively on `(ℤ/qℤ)^m`,
  the digital point set is a `(0,m,3)`-net (counting argument: injective map between finite sets
  of the same cardinality `q^m`);
* box matrices: row description, compatibility with `Matrix.map` and right multiplication;
* lower-triangular matrices with unit diagonal preserve "the first `d` entries vanish".
-/

namespace Z3Net.Proofs

open Matrix Finset

/-! ## Base-`q` digit sums -/

/-- The digit sum `∑_j f_j q^(m-1-j)` (digit `0` most significant). -/
def digSum (q m : ℕ) (f : Fin m → ℕ) : ℕ := ∑ j : Fin m, f j * q ^ (m - 1 - (j : ℕ))

lemma digSum_succ (q m : ℕ) (f : Fin (m + 1) → ℕ) :
    digSum q (m + 1) f = q * digSum q m (fun j => f j.castSucc) + f (Fin.last m) := by
  unfold digSum
  rw [Fin.sum_univ_castSucc, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj := j.isLt
    simp only [Fin.val_castSucc]
    have : m + 1 - 1 - (j : ℕ) = (m - 1 - j) + 1 := by omega
    rw [this, pow_succ]; ring
  · simp

lemma digSum_lt (q : ℕ) : ∀ (m : ℕ) (f : Fin m → ℕ), (∀ j, f j < q) → digSum q m f < q ^ m := by
  intro m
  induction m with
  | zero => intro f _; simp [digSum]
  | succ m ih =>
    intro f hf
    rw [digSum_succ, pow_succ]
    have h1 := ih (fun j => f j.castSucc) (fun j => hf _)
    have h2 := hf (Fin.last m)
    calc q * digSum q m (fun j => f j.castSucc) + f (Fin.last m)
        < q * digSum q m (fun j => f j.castSucc) + q := by omega
      _ = q * (digSum q m (fun j => f j.castSucc) + 1) := by ring
      _ ≤ q * q ^ m := Nat.mul_le_mul_left _ h1
      _ = q ^ m * q := by ring

                                                                                         
                                                                       
                                                  
         
                  
                                              
                
                             
                                       
                                               
                                               
                              
                               
                                                       
                                                            
                                                       
                                                             
                
             
                                             
                                                      
                                                      
                                                                     
                                                   
                                                                     
                                                    
                           
                                                              
                                                                                                  
                                             
                        
                 
               
                                            
                                                                                              
                                                              
                                                                                                  
                                         
                        
                  

                      

                                                                                              
                                                 
                            
                                        
                                                                           
                                                           
                  
                                
                   

                                                                                      
                                                                   
                                                                                     
                     
                                                                                    
             
                  
               
                                    
                          
                                               
                
                                    
                                                                              
                                                                              
                                                            
                                                         
                           
                                  
                                    
                                                                                    
                                                                                    
                                                                      
                                                                     
                           
                                  
           
            
                         
                        
                    
                                  
                                  

                                                             
                                                                                     
                                                                                          
                                                 
          
                                         
                      
                  
                                
                                

                                                                                 
                                                            
                                                                    
         
                                  
                   

                                                          
                                                                                           
                                                            
         
                                  
                   

                                                                     
                                                                                         
               
                                          
                                                                    
            

                                                              
                                                                  
                                     
               
                                                       
                           

                                     

                                                                                                
                             
                                                    
                                                 
                                                                                            
                                     
                 
                                                     
                                                                        
                                                                                         
                  
                                                                         
             
                                                                                    
                                                                                    
                                      
                                                             
                                                               
                                        
                 
                
                                       
                
                                                                                           
                            
                                           
                                      
                                                                                              
                                
                                   
                                                                                               
                                                                              
                          
                                 
                                                                                                  
                                                 
                                              
                                            
                        
           
            
                        

                                   

                                                                                                 
                                
                                                                                   
                                                                                           
                                                             
                                            
                                                                         
                            
         
                                                
             
                   
                        
                                                           
                                               
                   
                                              
                                                         
                                               
                                   
          

end Z3Net.Proofs
