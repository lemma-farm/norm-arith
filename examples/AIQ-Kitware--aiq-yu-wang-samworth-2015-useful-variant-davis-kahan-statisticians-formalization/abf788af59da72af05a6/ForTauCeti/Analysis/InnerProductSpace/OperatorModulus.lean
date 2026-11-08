/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# The modulus of a Hilbert-space operator

For a bounded operator `T : E →L[𝕜] F` between Hilbert spaces over `𝕜 : RCLike`, its
**modulus** `|T| = (T⋆ T)^(1/2)` is the positive square root, through the
continuous functional calculus, of the Gram operator `T⋆ T` acting on the
*source* space `E`.

The definition is stated for a general (rectangular) `T`: the source space
alone determines the construction, and the endomorphism case `F = E` is a
specialization rather than a separate definition (`modulus_eq_sqrt_star_mul_self`,
`modulus_mul_self_eq_star_mul_self`).

## The scalar field, and why there are typeclass hypotheses

`CFC.sqrt` is a statement about the *algebra* `E →L[𝕜] E`, not about the scalar
field of the Hilbert space, so nothing in this file is intrinsically complex.
What *is* complex-only is the supply of instances: Mathlib derives
`ContinuousFunctionalCalculus ℝ A IsSelfAdjoint` from
`ContinuousFunctionalCalculus ℂ A IsStarNormal` by spectrum restriction
(`IsSelfAdjoint.instContinuousFunctionalCalculus`), and registers
`CStarAlgebra (E →L[ℂ] E)` only over `ℂ`. Mathlib says so itself: its
`ContinuousLinearMap.instStarOrderedRingRCLike` is deliberately a lemma and not
an instance, "because this takes `ContinuousFunctionalCalculus ℝ (H →L[𝕜] H)
IsSelfAdjoint` as an argument, and for the moment we only have this for
`𝕜 := ℂ`".

This module therefore carries that instance — together with the `ℝ`-algebra
structure on `E →L[𝕜] E`, which Mathlib's
`Mathlib/Analysis/InnerProductSpace/StarOrder.lean` also assumes rather than
derives — as a hypothesis. Every hypothesis is discharged automatically at
`𝕜 = ℂ`, so the complex API is unchanged and no consumer has to supply
anything.

**Its finite-dimensional counterpart.** `TauCeti.abs` in
`ForTauCeti/Analysis/InnerProductSpace/PolarDecomposition.lean` is the square,
`RCLike`-generic, finite-dimensional modulus, built from the spectral square root
rather than from the continuous functional calculus. The two agree wherever both
apply, by `TauCeti.abs_toContinuousLinearMap_eq_cfcAbs`. Neither subsumes the
other: this one is rectangular and infinite-dimensional, that one needs no
functional-calculus instance.

## Main results

* `ContinuousLinearMap.modulus_mul_self`: the defining identity
  `|T| * |T| = T⋆ T`;
* `ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq`: `|T|` is the
  *unique* nonnegative square root of the Gram operator;
* `ContinuousLinearMap.norm_modulus_apply`: the pointwise isometry
  `‖|T| x‖ = ‖T x‖`, from which `ContinuousLinearMap.norm_modulus`
  (`‖|T|‖ = ‖T‖`) and the one-sided composition laws
  `ContinuousLinearMap.norm_modulus_comp` (`‖|T| ∘L D‖ = ‖T ∘L D‖`) and
  `ContinuousLinearMap.norm_comp_modulus` (`‖D ∘L |T|‖ = ‖D ∘L T⋆‖`) follow;
* `ContinuousLinearMap.modulus_apply_eq_zero_iff`: `|T| x = 0 ↔ T x = 0`;
* `ContinuousLinearMap.modulus_commute_modulus`: moduli of operators with
  commuting Gram operators commute.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original modules: `DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean`
  (`rectangularOperatorModulus` and its API, Jon Crall / OpenAI GPT-5.6 Thinking)
  and `ForMathlib/Analysis/InnerProductSpace/OperatorAbsoluteValue.lean`
  (`operatorAbs` and its API, Jon Crall / Claude Fable 5), both at Davis--Kahan
  commit `fc38eb4`; Apache 2.0.
* Extraction class: **unified and generalized**.  Per the signature-polish
  backlog, the two parallel APIs —
  one rectangular, one square — are replaced by this single rectangular
  definition with dot notation on `ContinuousLinearMap`.  The square-only
  composition laws `norm_operatorAbs_mul` / `norm_mul_operatorAbs` are
  generalized to rectangular operators here, and reproved from the pointwise
  isometry instead of the C⋆-identity; the uniqueness and commutation results
  are likewise generalized.
* Spectra influence: **none** — this module imports only Mathlib.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

universe u v w

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

                                                                         
                                                      
                                                                        
                                                                

                                                             
                                                                             
                                                                
                                                                                 
                                           
             
                                                                               
                                                                                    

                                          

                                                                               
                                                                               
                                                                        
                                                                          
                                                                             
                                                                                
                                                                          
                                                                

                                                                                      
                                                                               
              

variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

                                                                          
                                                                   
                                                             
                                                        
                           

                                                                                
                                                                             
                                                                       
                                                       

                                                                      
                       
                                                                                    

                                                            
       
                                                                    
                               
         
       
                                                                
            

                                                  
                                                         
                   

                                   
                                                                          
                             

                                                                 
       
                                                                             
                        
                                       

                                                
                                          
                                             
                                                     

                                                                   
            
                                                                           
                                                                
                             

                                                               
                                                                            
                                                             
       
                                                                                
                                                                       
                                           
                                                                         
                                                                    
                                                   
                                                               
                                                       
                                                
                                                                         
                         
                                      
                                                                           

                                                         

                                                                          
                                                                        
       
                                                           
                                   
                                                                    

                                                                  
       
                                                           
                                                        

                         
                                                                            
                                          
                                                           
                                  
                                                                       

                                                                              

                                                                             
                                                                         
                                                              
                                                           
                                             
                       
                                                                                   
                                                                         
                                                         
                                                                                   
                                                                 

                                                                             
                                                                              
         
                                                               
                                                     
                                     
                                                                   
                           
                                                                              
                                 
               

                             

                                                                             
                                                                          
                                                                                

                                                                       
                                                       
                                              
                                                
                                                           
                                         
                    

end ContinuousLinearMap

end
