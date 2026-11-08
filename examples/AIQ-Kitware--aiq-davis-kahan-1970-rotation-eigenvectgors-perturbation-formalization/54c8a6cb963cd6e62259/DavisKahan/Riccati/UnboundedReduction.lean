/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Riccati.UnboundedCore

/-!
# Strong unbounded Riccati graph reduction

This leaf proves the domain-controlled equivalence between invariance of a
bounded angular graph under the block core and the strong Riccati
equation.  Operator-domain membership, graph membership, and coordinate action
are kept as separate lemmas so later existence and diagonalization arguments
can reuse the same core calculation.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A direct-sum vector belongs to the unbounded block graph exactly when its
second coordinate is the angular operator applied to its first coordinate. -/
theorem toLp_mem_unboundedBlockGraph_iff
    (X : E0 →L[𝕜] E1) (u : E0) (v : E1) :
    WithLp.toLp 2 (u, v) ∈ unboundedBlockGraph X ↔ v = X u := by
  constructor
  · intro hmem
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
    change WithLp.toLp 2 (w, X w) = WithLp.toLp 2 (u, v) at hw
    have hp : (w, X w) = (u, v) :=
      (WithLp.linearEquiv 2 𝕜 (E0 × E1)).symm.injective hw
    have hfst : w = u := congrArg Prod.fst hp
    have hsnd : X w = v := congrArg Prod.snd hp
    calc
      v = X w := hsnd.symm
      _ = X u := congrArg X hfst
  · intro hv
    refine LinearMap.mem_range.mpr ⟨u, ?_⟩
    change WithLp.toLp 2 (u, X u) = WithLp.toLp 2 (u, v)
    rw [hv]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Coordinate characterization of membership in an unbounded block graph. -/
theorem mem_unboundedBlockGraph_iff
    (X : E0 →L[𝕜] E1) (z : WithLp 2 (E0 × E1)) :
    z ∈ unboundedBlockGraph X ↔ WithLp.snd z = X (WithLp.fst z) := by
  change WithLp.toLp 2 (WithLp.fst z, WithLp.snd z) ∈
      unboundedBlockGraph X ↔ WithLp.snd z = X (WithLp.fst z)
  exact toLp_mem_unboundedBlockGraph_iff X (WithLp.fst z) (WithLp.snd z)

                                                                           
                                                                     
                                                 
                                                           
                                                          
                                                                
                                           
                                          
                               

                                                              
                                                 
                                                           
                                                          
                       
                                                  
                                                                      
                                 
                                                                     
                                                                        

                                                                              
                                                                                
                                            
                                                          
                                                           
                                                          
                       
                                              
                                                     
                                         
     

                                                                 
                                                          
                                                           
                                                          
                       
                                              
                                                     
                                                        
     

                                                                          
                                         
                                                           
                       
                             
                                           
                          
                                                      
                                                 
             
                       
                     
           
                
                     
        
                                                  
                                      
                                                                     
                                                       
            
                                                         
               
                                                           
                         
                     
           
                       
                      
        
                                 
                                                                  
                                                        
                                                       
            
                                 

                                                                         
                                                                     
                                                           
                                                           
                       
                                  
                                                                         
                                  
                                   
                                        
             
                       
                     
           
                                                                  
                                                            
                                                           
                                                       
                                                
                         
                     
              
                                            
                                             
                                           
                           
                                                       
                                                                         
                                                                       
                   
                                                                  
                                    
                       
                
                        
                   

end DavisKahanExt
end TauCeti
