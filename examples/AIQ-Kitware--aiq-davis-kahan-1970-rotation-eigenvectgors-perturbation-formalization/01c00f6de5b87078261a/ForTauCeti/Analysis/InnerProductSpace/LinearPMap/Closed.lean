/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Domain-aware infrastructure for partial linear maps

Reusable algebra for unbounded operators represented canonically by Mathlib's
`LinearPMap`: domain transport, extension, symmetry, graph norms, relative
bounds, and elementary real resolvent predicates.

The declarations deliberately take raw partial maps.  Closedness, dense domain,
and self-adjointness are separate hypotheses supplied by the theorem that needs
them; they are not bundled into a parallel operator structure.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/SpectralTheory/ClosedOperator/Basic.lean`.
* Extraction class: **representation migration**.  The original declarations
  were methods of a bundled `ClosedOperator` record -- a `LinearPMap` with
  dense domain and closed graph as fields, since deleted downstream; this
  module restates their reusable content directly over Mathlib `LinearPMap`.
* Spectra influence: none.  This module imports only Mathlib.
-/

public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace
open Filter Topology

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

                                                                     
                                                                                 
                                                         
                                   
                      
                                                                              
                                         
                                                          
         
                                                                        
               
                          
                                 
                    
                                                           
                                             
             

                                                             
def SameDomain (A B : E →ₗ.[𝕜] E) : Prop :=
  A.domain = B.domain

                                                    
                                                                          
                                                    
@[symm] theorem SameDomain.symm {A B : E →ₗ.[𝕜] E}
    (h : SameDomain A B) : SameDomain B A :=
  Eq.symm h

/-- Equality of partial-map domains is transitive. -/
@[trans] theorem SameDomain.trans {A B C : E →ₗ.[𝕜] E}
    (hAB : SameDomain A B) (hBC : SameDomain B C) : SameDomain A C :=
  Eq.trans hAB hBC

-- `@[expose]` is deliberate: this is a `Prop`-valued abbreviation for a ∀-statement and
-- consumers *apply* it (`h x : X x ∈ A.domain`), which is unfolding by definition. The
-- `api-design` carve-out for a consumer that must unfold, not blanket exposure.
/-- A bounded map sends the domain of `B` into the domain of `A`. -/
@[expose]
def MapsDomainTo (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (X : F →L[𝕜] E) : Prop :=
  ∀ x : B.domain, X (x : F) ∈ A.domain

                                                                   
                                          
                                                       
         
                                                                                   
           
                           
                  

                                                   
theorem MapsDomainTo.comp
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {C : G →ₗ.[𝕜] G}
    {X : F →L[𝕜] E} {Y : G →L[𝕜] F}
    (hX : MapsDomainTo A B X) (hY : MapsDomainTo B C Y) :
    MapsDomainTo A C (X ∘L Y) := by
  intro z
  exact hX ⟨Y (z : G), hY z⟩

-- `@[expose]` for the same reason as `MapsDomainTo` above: consumers *apply* the
-- statement (`h x hx : A x ∈ U`), which is unfolding by definition.
/-- A subspace is invariant under a partial linear map on its domain. -/
@[expose]
def InvariantSubspace
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  ∀ x : A.domain, (x : E) ∈ U → A x ∈ U

/-- A subspace reduces a partial linear map when both orthogonal projections
preserve its domain and both summands are invariant. -/
def ReducesSubspace
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : Prop :=
  (∀ x : A.domain, U.starProjection (x : E) ∈ A.domain) ∧
  (∀ x : A.domain, Uᗮ.starProjection (x : E) ∈ A.domain) ∧
  InvariantSubspace A U ∧ InvariantSubspace A Uᗮ

                                                                            
                                                                              
                                                 
                                     
                                                                    
                                                              
                                                               
                                                                
                                           

namespace ReducesSubspace

                                                                                
                             
                                                                    
                                              
                                          
       

                                                                                
                                       
                                                                    
                                              
                                           
         

                                                                
                 
                                                                    
                                                        
         

                                                                     
                            
                                                                    
                                                         
         

                                                                           
                  
                                                                    
                                                          
                                                
                               
           
                                                      
                               
              
                                                
                          

end ReducesSubspace

                                                      
                             
                                                              
                                     
                                
                                          
                                            

                                                                              
                                                                                
                                     
                                                 
                                                  
                                                             
         

                                                                           
                                      
                                        
                                                     
                                                         

                                                                              
                                                                     
                                                      
                                        
                                         
                                                                 
                                                        
                                                                 
                                
                                                                    
                                  
                                               
            
                                                  
                                                               
                                                             
                    
                     
                                 
                                                             
                                                
                                                          
                             
                     
                     
                                                    
                                                             
                                                            
                              

                                                                                
                                                                           
                                                                
                                                
                                                                    
                                                                      
                                                         
                                                           
                                                                         
                                                    
                                                                    
                                                 
                                    
                                                                  
                                 

                                                                         
                                                                           
       
                                                      
                                                                    
                                                 
                                                      
                                                  
                                       
                                                                           
                                                                             
                                     
                                                                    
                                                   
                                         
                                                

                                                                            
                                          
                                                                    
                                  
                                                                                  
                                                                               
                                                                               
                                                                              
                                          
                                                                    
                                          
                                                                             

                                                                              
                                                                           
                                                                              
                                                                               
                                                                 
                                     
                                                                    
                                                                    
                                  
                                                                               
                              
                                                                            
            
                                 
                                                                    
                                                                  
                                                               
                                                       
       
                                    
                                                      
                      
           
                                                           
                           
                                                              
                                                  
           
                                                
                                                                          
                                                     
                                                         
                                                                          
                                             
                                 
                                                 

                                                                     
                                                                        
                                                                   
                                       
                                                                    
                                
                                                                    
                                                                        
                                                         
                                              
                                                               
                                     
                                                      
                                                 
                                                                      
                                                         
                                          
                                                                  
         
               
                     
                                                           
                    
                                                            
                                                        
                                                           
                                                                   
                                 
                       
                                                                                       
               
                                                                     
                                                                   
                         
                      
                            
                           

                                                                          
                                                     
                                                  
                                                                    
                                       
                                          
                                                       
                                      
                                        
                                      
             
            
                                                                                  
                                                 
                                     
                                                                     
                                                  
                                     
                                                       
                          
                                                                   
                                               
                                          
                                                               
                      
                                    
                                          
                                                               
                                                  
              
                          
                                                                
                          
                                                                           
                                      
                         
                                                                           
                                              
                                                                
                                       
                                                  
          
                                          
                                                                
                                      
                                          
                                                   
                                          
                     
                                                
                                                 
                      
               
            
                                                                            
                                                      
                                                                             
                                                                    
                                  
                                                                   
                                               
                               
                                                                             
                                                                          
                

                                                                  
                                       
                                                                    
                                
                           
                                            
                                                  
                                                   
                                                         
           
                                                     
                                              

                                                                                
                                                                    
                      
                                          

                                                  
def Extends (A B : E →ₗ.[𝕜] E) : Prop :=
  ∃ hdom : A.domain ≤ B.domain,
    ∀ x : A.domain, B ⟨(x : E), hdom x.property⟩ = A x

                                               
                                                                 
                     
         
     

                                                      
                                                   
                                                               
                                  
                                  
                                  
         
      
                                             
                                         
                                         
                       

                                                                             
                      
                                                                      
                              

                                                                              
                                                                               
                                      
                                              
                                              
         

                                                                            
                            
                                      
                                           
                                    
                    
                     
                                   
                     
                     
                              

                                                                              
                                                    
                                            
                                    
                              
                                                                          
                                                                     
               
                                                        
                                 
                                                                       

                                                                            
                                                                    
                                       
                                    
                              
                             
                                                          
                                                                             
                                                                             
                                                                              
                              
                                

                                                                              
                               
                                      
                                                       
                                                                                 
                      
                                    
                                     
                                               
                      
                                                       
                                                           
                                                           
                                     
         
               
              
                                           
                         
                     
              

                                                                    
              
                            
                                    
                                                                    
                                                        
                                      
                                                       
                                                 
                                                      
                                  
                                                                  
         
               
                     
                                                 
                    
           
                                                   
                                     
                                                                                          
                                                                                      
                                                                                     
                                         
                    
                                                         
                                                     
                                               
                                                                                         
                 
                               
                   
                        
                                                 
                                                        
                         
                       
                                 
                       
                                                                                        
                                                                              
                                                                                       
                                                  
                                                
                                                                                         
                                            
                                                               
                           

                                                                               
                                               
                                            

                                                                           
                                                
                                        
                                  
                                                
                                          
                                          
                                                 
                                                       
                    
                                         
                    
                                                

                                                                         
                        
                                  
                                    
                                                      
                                                              
                                        
                                                                    
               
             
                               
                        
                             
                                                                        
                                      
                                 
           
        
                                                                         
                                      
                                 
           
        
                                        
                                          
                                                 
                    
                                
                                                           
                                                                                         
                 
                                            
                                                        
                           
           
                                                                                      
                                                                            
                                                                                     
                                                
                                                        
                                                                                      
                                                                            
                                                                                     
                                                
                                                               
                                                                                     
                                                                           
                                     
           
                                                                                      
                                                                            
                                                                                     
                                                
                                                                     
                                                                                      
                                                                            
                                                                                     
                                                
                                                                            
                                
           
                     
        

                                                                       
                           
noncomputable def directSumDomain
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    Submodule 𝕜 (WithLp 2 (E × F)) :=
  (A.domain.prod B.domain).comap
    (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

/-- A vector lies in the direct-sum domain exactly when each coordinate lies in
the corresponding domain.  The `WithLp 2` wrapper carries the Hilbert norm and
changes nothing about membership. -/
@[simp] theorem mem_directSumDomain_iff
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (z : WithLp 2 (E × F)) :
    z ∈ directSumDomain A B ↔
      WithLp.fst z ∈ A.domain ∧ WithLp.snd z ∈ B.domain :=
  Iff.rfl

/-- First coordinate of a direct-sum domain vector. -/
def directSumDomainFst (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (z : directSumDomain A B) : A.domain :=
  ⟨WithLp.fst (z : WithLp 2 (E × F)),
    (mem_directSumDomain_iff A B z).mp z.property |>.1⟩

/-- Second coordinate of a direct-sum domain vector. -/
def directSumDomainSnd (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (z : directSumDomain A B) : B.domain :=
  ⟨WithLp.snd (z : WithLp 2 (E × F)),
    (mem_directSumDomain_iff A B z).mp z.property |>.2⟩

/-- First-coordinate extraction as a linear map on a direct-sum domain. -/
def directSumDomainFstLinearMap (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    directSumDomain A B →ₗ[𝕜] A.domain where
  toFun := directSumDomainFst A B
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Second-coordinate extraction as a linear map on a direct-sum domain. -/
def directSumDomainSndLinearMap (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    directSumDomain A B →ₗ[𝕜] B.domain where
  toFun := directSumDomainSnd A B
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Componentwise partial-map action on a direct-sum domain. -/
noncomputable def directSumLinearMap
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    directSumDomain A B →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap.comp
    ((A.toFun.comp
      (directSumDomainFstLinearMap A B)).prod
     (B.toFun.comp
      (directSumDomainSndLinearMap A B)))

/-- The direct sum of two partial maps.  Density and closedness remain
separate properties. -/
noncomputable def directSum
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    WithLp 2 (E × F) →ₗ.[𝕜] WithLp 2 (E × F) where
  domain := directSumDomain A B
  toFun := directSumLinearMap A B

                                                                            
                                
                                       
                                                         
                                                            
                       
                                     
                                                                     
                                                                 
                       
                                                                             
                     
                                            
                                                      
                                                                             
                                                                    
                               
                                           
                                                     
         
               
              
                                    
                         
               
              

                                                             
                             
                                     
                                                                  
                                                                    
                                                         
                                                      
                                                      
                                     
                                      
                                       
                                                 
                         
                                                        
                                                                    
                                                       
                                                  
                                                                   
                                                          
         
               
                     
                                                        
                                                   
                               
                                                                 
                                                             
                                                                 
                                                             
                                             
                                           
                                               
                                                                     
                                                                     
                                 
                                                      
                    
                                                            
                             
                                                            
                              
                                

                                                                
                                          
                                                       

                                                             

                                                                                  
                                                                                 
                     
                                          
                   
                                                                 
     

                                                                   

                                                                          
                                                            
                                                                       
                                                       
                                                                    
                                                    
           
                   

                                                                               
                     
                                         
                                                                    
                                       
                                                                    
                                   
                                                             
                                       
                                                                                  
                               
                                           
                                        
         
                                                                                    
                                              
                                                     
                                                          
           
       
                     
                                        
                              
                                                      
                                                            
                                                              
                       
                                     
               
                        
                                                                 
                                              
                                      
                                                                         
                                                  
                                                  
                  
                                      
            
                                           
                                                 
                               
                                                                  
                                                       
                                                                  
                                                      

                                                       
                                                                  
                                       

                                     
                                                          
                        
                    

                                                                    
                                                      
                                                       
                  
                                    

                                                        
                                                               
                                   
                
                                                              

                                                               
                                                                 
                               
                
                                                                  

                                                                       
                                                                        
                                                                                 
                                                                                   
                                                                                     
                                                                                 
@[expose]
noncomputable def addBounded (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    E →ₗ.[𝕜] E where
  domain := A.domain
  toFun := A.toFun + V.toLinearMap.domRestrict A.domain

                                                                          
                                                                        
                                                                        
             
                                                                    
                                                                  
                                             
                                                                 
                                                      
                                                                  
                                                                      

                                                                                 
                                                                               
                                                                                 
                          
                                                                        
                                                                                    
                                             
                                             
      

                                                                  
                                                                
                  
                    
                                                    
             

                                                                             
                                                      
                                                                    
                                                    
                    
                                                    
                                                          
             

                                                                       
                                                           
                              
                                             
                                       
                                               
                         

                                                                           
                      
def RelativelyBounded (A : E →ₗ.[𝕜] E)
    (V : A.domain →ₗ[𝕜] E) (a b : ℝ) : Prop :=
  ∀ x, ‖V x‖ ≤ a * ‖(x : E)‖ + b * ‖A x‖

namespace RelativelyBounded

/-- The zero perturbation has zero relative bound. -/
theorem zero (A : E →ₗ.[𝕜] E) :
    RelativelyBounded A (0 : A.domain →ₗ[𝕜] E) 0 0 := by
  intro x
  simp

                                                                        
                             
                                          
                                    
                                     
                                     
         
                                  
                                                           
                                                         

                                                           
                            
                                          
                                    
                                      
                                                     
         
      
                                                  
                                     
                                      
                              
                                                        

                                                       
                             
                                    
                                              
                                                         
         
                                      
      
                                                      
                                                      
                                                            

                                                 
                            
                                    
                                      
                                      
                              

                                                              
                            
                                          
                                    
                                      
                                                     
                                            

                                                                             
              
theorem domRestrict (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    RelativelyBounded A (V.toLinearMap.domRestrict A.domain) ‖V‖ 0 := by
  intro x
  simpa using V.le_opNorm (x : E)

end RelativelyBounded

/-- Real resolvent set of a partial linear map.  A parameter belongs to the set
when the shifted map has a bounded two-sided inverse with explicit domain
transport for the right-inverse leg. -/
def realResolventSet (A : E →ₗ.[𝕜] E) : Set ℝ :=
  {lam : ℝ | ∃ R : E →L[𝕜] E,
      (∀ x : A.domain, R (A x - (lam : 𝕜) • (x : E)) = (x : E)) ∧
      (∀ y : E, ∃ h : R y ∈ A.domain,
        A ⟨R y, h⟩ - (lam : 𝕜) • R y = y)}

                                                                  

                                                                                      
                                                                                    
                                                             
                              
                      
                                                                   
                                       
                                              
         

                                                                     
def realSpectrum (A : E →ₗ.[𝕜] E) : Set ℝ :=
  (realResolventSet A)ᶜ

                                                                               
                                                                 
                                                      
         

                                                                                      
                                                                                  

                                                                                   
                                                                                      
                                                                                      
                                                                                         
                   
                                                                                 
                                                           
                              
            
                              
                                                                 
                                        
                     

                                                                               
          
def SpectralSetsSeparated (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (s t : Set ℝ) (d : ℝ) : Prop :=
  ∀ a ∈ realSpectrum A, a ∈ s →
    ∀ b ∈ realSpectrum B, b ∈ t → d ≤ |a - b|

/-- Spectral-set separation is symmetric in the two maps. -/
theorem SpectralSetsSeparated.symm
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s t : Set ℝ} {d : ℝ}
    (h : SpectralSetsSeparated A B s t d) :
    SpectralSetsSeparated B A t s d := by
  intro b hb ht a ha hs
  simpa [abs_sub_comm] using h a ha hs b hb ht

                                                                    
                                      
                                     
                           
                                                         
                                         
                       
                                     

                                                                     
                                       
                                     
                               
                                         
                                 
                                           
                           
                                       

end LinearPMap
end TauCeti

end
