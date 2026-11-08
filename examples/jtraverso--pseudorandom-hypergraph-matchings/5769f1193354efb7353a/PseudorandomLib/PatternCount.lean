/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Freedman
public import PseudorandomLib.Cylinder
public import Mathlib
/-! # Weighted counts of `ℓ`-sets with a prescribed colour pattern

The vertex set is `Fin n` with its natural order. Every vertex receives a colour in `Fin q`
uniformly at random (`unif (Fin n) q`). An `ℓ`-set `e = {v₁ < ⋯ < v_ℓ}` has pattern
`α : ℕ → Fin q` if `c(vᵢ) = α (i - 1)` for all `i`, i.e. `c v = α (rk e v)` where `rk e v` is
the number of elements of `e` below `v`.

`cnt ℓ w α c = ∑_{|e| = ℓ} w e · [e has pattern α]` is the random variable `ω(E_α)` of
Theorem 3.1. `Xp ℓ w α t` is its exposure martingale, where the colours of `0, …, t - 1`
have been revealed.
-/

@[expose] public section

namespace Pseudorandom

namespace Patt

open Finset

variable {n q : ℕ}

/-- The rank of `v` in `e`: the number of elements of `e` below `v`. -/
def rk (e : Finset (Fin n)) (v : Fin n) : ℕ := (e.filter (· < v)).card

/-- `e` has colour pattern `α` under the colouring `c`. -/
def Pat (α : ℕ → Fin q) (c : Fin n → Fin q) (e : Finset (Fin n)) : Prop :=
  ∀ v ∈ e, c v = α (rk e v)

                 
                                                        
                                                                                            
        
                                                             

open Classical in
/-- The exposure martingale of `cnt`: colours of the vertices `< t` are revealed. -/
noncomputable def Xp (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) (t : ℕ)
    (c : Fin n → Fin q) : ℝ :=
  ∑ e ∈ powersetCard ℓ univ, w e * ((1 / (q : ℝ)) ^ (e.filter (fun v : Fin n => t ≤ (v : ℕ))).card *
    if ∀ v ∈ e, (v : ℕ) < t → c v = α (rk e v) then 1 else 0)

                                                                             
                                
              
           
                                    
         
               
             
                                                      
                                                    

                                                                                      
                                                                           
           
                                     
                             
                                                                                                   
                 
      

                                                                                   
                                    
               
                                    
                                                       
                                                        
                                          
         
               
             
                                  
                                

                                                                               
                                                          
           
                                          
                                                
           
                  
                   
               
                                    
                      
                                         
                                                               
                                                                          
           
                                        
                 
                        
                          
                       
                                                                                     
                              
                                      
                              
                                                                       
                                                                          
                                                
                                                                                               
                                                                          
             
                 
               
                                       
                                   
                                                                          
                                    
                                            
                               
                          
                                                      
                                      
                                                                                 
                   
              
                                                         
                                                                                           
                                                                     
                             
                                             
                                                
                             
                                                                                             
                         
                                                                   
                                        
                                                                   
                                                           
                                        
                                                                                             
           
                                                                                               
                                                       
             
                 
                        
                                 
                                                                                  
                        
                                                                
                                      
                                                                                 
                         
                                                                        
              

                                                                              
                                                                                              
                                                                                  
                   
          
         
          
                           

end Patt

end Pseudorandom
