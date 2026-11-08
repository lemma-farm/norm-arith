/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.Toeplitz.FockSpace
import GroupApproximation.Toeplitz.Sections
import Mathlib.Topology.ContinuousMap.Defs

/-!
# The Fock module of a set of sections

For a set `E` of bounded sections `X → ℓ²(ι)`, `fockModule E` is the closed linear span of the
sections `ζ₁ ⊗ ⋯ ⊗ ζ_m ⊗ f` with `ζ_i ∈ E` and `f ∈ C(X)`, realised fibrewise in the Fock space
`ℓ²(List ι)`.  This is the module `F(E)` of Blanchard, arXiv:1507.02535v1, Definition 5.1 (p. 7),
in the form used by `Palomar/BlanchardToeplitzChallenge.lean`.

The creation operator `creationSec ζ` preserves `fockModule E` when `ζ ∈ E`
(`creationSec_mem_fockModule`).  The annihilation operator `annihilationSec ζ` preserves it when
`x ↦ ⟪ζ x, ζ' x⟫` is continuous for every `ζ' ∈ E` (`annihilationSec_mem_fockModule`).  Their
restrictions to `fockModule E` are adjoint at every point (`isSectionAdjoint_creationEnd`).
-/

namespace GroupApproximation.Toeplitz

noncomputable section

open scoped ENNReal InnerProductSpace

variable {X : Type*} {ι : Type*}

                                                                          
                                                                                        
                                 
                                                                                     
                                                            
                                                                             

                                                                                                   
                               
                            
                                                                               
         

                                                                                                   
                                       
                                                                             
                                                                               
         

                                                                             
                                                                                    
                                        
                                                                 

                                                                                 
                                                                    
                                                       
                                                                                      

                                                                       
def IsSectionAdjoint {M : Submodule ℂ (Sections X (Fock ι))} (T S : Module.End ℂ M) : Prop :=
  ∀ ξ η : M, ∀ x, ⟪((T ξ : M) : Sections X (Fock ι)) x, (η : Sections X (Fock ι)) x⟫_ℂ =
    ⟪(ξ : Sections X (Fock ι)) x, ((S η : M) : Sections X (Fock ι)) x⟫_ℂ

/-- The creation operator `ω ↦ ζ ⊗ ω` on sections. -/
def creationSec (ζ : Sections X (Fib ι)) : Sections X (Fock ι) →L[ℂ] Sections X (Fock ι) :=
  fibrewise (fun x => creation (ζ x)) (norm_nonneg ζ) fun x =>
    (norm_creation_le _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero ζ x)

                                                                                      
                                                   

                                                                                   
def annihilationSec (ζ : Sections X (Fib ι)) : Sections X (Fock ι) →L[ℂ] Sections X (Fock ι) :=
  fibrewise (fun x => annihilation (ζ x)) (norm_nonneg ζ) fun x =>
    (norm_annihilation_le _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero ζ x)

                                                                                          
                                                           

                                                                 
                                   
                                                                                                     
                                                                                     

                                                                                  
                                                                       
                                                                                                  
                                                                            
         
                  
           
              
                                                  
                                                                                               
                                                                                                   
                           
                
              
                                                               
                                                                                       
                
            
                                                                                                    
                 
                 
                                                                                         
                         
          

                                                                           
                                                                                
                                                             
                                                 
                                                          

                                                                       
                                                                          
                                                         
                                                          
                                         
                                                                                     

                                                                    
                                                                                     
                                                                 
                                                
                                    
                                   
                                                       
                                                   

                                                                                           
                                                                                           
                                                                                              
                                    
                                                                  
                                                      
                                

                                                                           
                                                           
                                                           
                                                             
                                                          
                                         
                
             
                                       
                                
               
                                                                   
                                        
                                                
                                                              

                                                                    
                                                                                
                                                           
                                  

                                                                        
                                                                                    
                                                               
                                      

                                                                                          
                                                         
                                                        
                                                         

                                                                                              
                                                             
                                                            
                                                             

                                                                            
                                                                
                                             
                                                                                  
                                               
                                                 

end

end GroupApproximation.Toeplitz
