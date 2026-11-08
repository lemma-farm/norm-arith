/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/Resolver/Douglas.lean
-/
/-
# The Douglas factorization with commutation transport (node 1.2.6.4)

For operators `c` and a finite family `x k` on a Hilbert space with
`∑ₖ xₖ* xₖ ≤ c* c`, there are operators `z k` with

* `z k * c = x k`,
* `∑ₖ (z k)* (z k) ≤ 1`,
* `z k` commutes with every operator `R` such that `R`, `R*` commute with `c`
  and `R` commutes with each `x k`.

Construction: on `range c` set `z (c η) := x η` (well defined and
contractive since `‖x η‖ ≤ ‖c η‖`), extend to the closure `K` of `range c`
by continuity, and compose with the orthogonal projection onto `K`. The
commutation transport is what puts `z k` into the block von Neumann algebra
of `VN/BlockOperators.lean` (entries commuting with the right action), so
no strong-operator limits are needed.

With equality `∑ₖ xₖ* xₖ = c* c`, `c* (1 − ∑ₖ zₖ* zₖ) c = 0`, which gives the
manuscript's singular-safe POVMs `𝖠ᵃ = ∑_{k ∈ a} zₖ* zₖ + [a = a₀](1 − Z)`
(04_resolver_corner.tex, eqs alice-corner-povm / bob-corner-povm), with
`c* 𝖠ᵃ c = ∑_{k ∈ a} xₖ* xₖ`. Nothing here is a manuscript statement.
-/
module
public import Mathlib

-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true

@[expose] public section


namespace CommutingRepetition

namespace Resolver

namespace Douglas

open scoped BigOperators InnerProductSpace

set_option linter.unusedSectionVars false

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-! ## Inner-product facts -/

theorem mulA (f g : 𝓗 →L[ℂ] 𝓗) (ξ : 𝓗) : (f * g) ξ = f (g ξ) := rfl

theorem oneA (ξ : 𝓗) : (1 : 𝓗 →L[ℂ] 𝓗) ξ = ξ := rfl

                                                   
                                                
                                                                                                   
                           
                                   

                                                                     
                                                                 
                                                
                                                                                     
                          

                                                                        
                             
                                                      
                                  

                                          
                                                                                     
                       
                                                           
                                                                                             
                                                                                           

variable {κ : Type*} [Fintype κ]

                                                                
                                                      
                                      
                                                           
                                                                                          
                         
                                     
          

                                                        
                                                                                          
                      
                                                                                        

                          

variable (c : 𝓗 →L[ℂ] 𝓗)

/-- The closure of the range of `c`. -/
noncomputable def K : Submodule ℂ 𝓗 := (LinearMap.range (c : 𝓗 →ₗ[ℂ] 𝓗)).topologicalClosure

                                                                                               

instance : (K c).HasOrthogonalProjection := by
  unfold K; infer_instance

                                                                                                    

                                   
                                                                           
                                                                           
        

                                                                                                  

                                                   
                                                                                                      
                                                                                              
         
               
                               
               
              
                                                 
        
       
                                                      
                                                                          
                                                      
            

                                                              
                                                                              

                                               
                                                                                                         

                                                                           
                                          

                                                     

variable {R : 𝓗 →L[ℂ] 𝓗}

                                                                                  
                                            
                                                                   
                                                                                   
                     
                      
                          
                         
                                                                          
                                                     
                                     

                                                                                  
                        
                                                 
                                                                          
                                                                                        
                     
                           
                           
                         
                                                                          
                                                     
                                     

                                                                                    
                      
                                       
            
                                                                                      
                                         


section Factor

variable {c}
variable {x : κ → 𝓗 →L[ℂ] 𝓗} (hx : ∑ k, star (x k) * x k ≤ star c * c)
include hx

                                                                          
                                                             
                                                     
                                               

                                       
                                                                            
                        
                                     
                               
                      
                              
                                              
                                
                                    
                       
                              
                                                        
                                                        
                                                                                     
                                   

                                                                                                    

                                                                                                            
               
                                

                                           
                                                                          

                                                                                                    
                                                                                  

                                              
                                                                                    

                                                                                     
          
                                     
         
                                                                                  

                                                              
                                         
                                                                                                            
                                

                       
                                                
       
                        

                                                                                 
          
                                                                                                      

                                              
                                                                             
                                                          
                                                 
                                 
                                                                                  
                                                         

                                                                      
                                                                      
                                          
                                                      
                                                            
                                            

                       
                                                                       
                   
                                          
                                                    
           
                                             
                            
                                                                              
                     
                                           
                                                                
                                                                                
             
                                             
                                 
                      
                                    

                               

                                                                                     
                                                                          
           
                                                            
           
                                                            
                                                   
                            
                                                                         
             
                                                       
                                                                      
       
                  
                                                                                  
                                                                                  
                                                                                                
                                                            
                         
                                                      
                                                                    
                         
                                                                                        
                                  
                  

end Factor

/-! ## The singular-safe POVM -/

section POVM

variable {A' : Type*} [Fintype A'] [DecidableEq A'] (lab : κ → A') (a₀ : A')
variable {c : 𝓗 →L[ℂ] 𝓗} {x : κ → 𝓗 →L[ℂ] 𝓗} (hxe : ∑ k, star (x k) * x k = star c * c)
include hxe

                        
                                                                      

                                                              

                                                                         

                                                                  
          
                                            
                                           
                                   
              

                                                                       
                                                              

                                                                                 
                                                  
                                              
                                                                
                                     

                                                          
             
                                                        
             
                                  
                  
             
                                
                  

                                                   
             
                                              
                                                                             
                              
      

                                        
                                                                                         
             
                                                       
                                                                    
             
                                          
          
                   
                                           
           
                                     
                
        

end POVM

end Douglas

end Resolver

end CommutingRepetition

end
