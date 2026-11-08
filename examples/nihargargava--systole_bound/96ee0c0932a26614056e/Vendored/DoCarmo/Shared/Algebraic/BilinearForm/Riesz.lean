module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/shared/Shared/Algebraic/BilinearForm/Riesz.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes and upstream package-option restoration.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Vendored.DoCarmo.Shared.Algebraic.BilinearForm.Basic
public import Mathlib

@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000


/-!
# Riesz extraction — algebraic core

Field-generic Riesz isomorphism for symmetric positive-definite
bilinear forms on finite-dimensional vector spaces. Given a
positive-definite `B : Form 𝕜 V`, every linear functional
`φ : V →ₗ[𝕜] 𝕜` has a unique vector representative `v` such that
`B v w = φ w` for all `w`.

This is the algebraic substrate of the Riemannian module's
`metricRiesz` operation: when 𝕜 = ℝ and the bilinear form is the
metric tensor, we recover the standard Riemannian Riesz duality
between vectors and 1-forms.

## Reusability

Riesz extraction is not Riemannian-specific. The same construction
applies to:
- Hermitian forms on ℂ-vector spaces (with conjugate)
- Quadratic forms in algebraic optimization
- Inner-product-style dualities in any positive-definite setting

**Ground truth**: standard fact in linear algebra; on a finite-dim
vector space, a positive-definite bilinear form gives a vector-space
isomorphism with the dual space.
-/

namespace BilinearForm

section Riesz

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

                                                                    
                                                                                
                                                    

                                               
       
                                               
                                     

                               
                                                                                
                                                                            
                                                                             
                                                
                                                                 
                                                     
                                         
                 
                                                   
                 
                                                   

                                                                    
                                                           
                                       
               
               
                                                
                                                
                            
                                                         
                                           
                                                    
                                                
          

                                                                    
                                                                              
                                                                    
                                                  
                                            
                           
       
                                

variable [FiniteDimensional 𝕜 V]

                                                                     
                                                               
                                                                
                          
                                               

                                                                       
                                                        
                          
                         

                               
                                                                   
                                                    
                             
                                   
                                                                          

                                                                          
                                                             
                                                  
                        
                           
       
                        
                                 

end Riesz

end BilinearForm

