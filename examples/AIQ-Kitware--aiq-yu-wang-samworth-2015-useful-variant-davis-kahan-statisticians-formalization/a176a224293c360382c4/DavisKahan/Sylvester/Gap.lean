/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.ClosedSylvesterEquation
import Mathlib
/-!
# Form-bounded gap configurations for the unbounded Sylvester equation

The interval/exterior configuration says one block has spectrum inside a compact
interval while the other stays a fixed distance away from it.  The predicate is
symmetric in the two blocks: either orientation is allowed.

`FormBoundedSylvesterGap` collects every gap configuration the `sin Θ` endpoint
needs.  Its two ordered constructors let both diagonal blocks be genuinely
unbounded; only the interval/exterior constructor requires a bounded spectral
block.

## Two spellings of the same configurations

This module states the ordered configurations as **operator-form bounds** —
`TauCeti.LinearPMap.SemiboundedBelow`/`TauCeti.LinearPMap.SemiboundedAbove` — and the interval/exterior configuration
over `LinearPMap.realSpectrum`.  `SpectralIntervalExteriorGap` and
`SpectralSylvesterGap` (`SinTheta/Unbounded/IntervalExterior.lean`,
`Sylvester/Unbounded/AllGap.lean`) instead state all three configurations as
**spectral containments** in `Set.Ici`/`Set.Iic`, which is the form Davis--Kahan
1970 uses.

For self-adjoint blocks the two describe the same configurations — a form bound
`⟪Ax, x⟫ ≥ c‖x‖²` and a spectral containment `spectrum A ⊆ Set.Ici c` are the
spectral theorem apart — but they are different propositions, and **only one
direction is proved here**:

* `formBoundedSylvesterGap_of_spectral` gives `SpectralSylvesterGap → `
  `FormBoundedSylvesterGap` in **every** configuration, the ordered branches by
  `semiboundedBelow_of_spectrum_subset_Ici` and its mirror
  (`SpectralTheory/OrderedHalfLine.lean`), the interval branch by
  `realSpectrum_eq_spectraSpectrum`;
* the converse holds for the **interval/exterior branch only**
  (`SpectralSylvesterGap.intervalExterior_of_formBounded`).  Recovering a
  spectral containment from a form bound is the half of the spectral theorem
  this tree does not have.

**So the form-bounded predicate is the weaker hypothesis, and a theorem stated
over it is the stronger theorem** — which is exactly how the endpoints are
arranged: `davisKahan1970_sylvester_complex` takes this predicate, and
`davisKahan1970_sylvester_of_spectrumGap` is available at the spectral one.

Neither predicate carries an unqualified name.  They are equivalent mathematics
stated two ways, so a bare `SylvesterGap` would leave a reader asking which one
it is; each name says how its ordered configurations are given.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

                                                              
                                                                                
                                                                               
               

                                                                                
                                                                             
                              

                                                                       
                                                                              
                                                                              
                              
                                   
                                                           
                                                    
                                                                      
                                                    
                                                                    

                                                                          
                                                                        
                                                                                
                                                                         
               

                                                                     
                                                                           
                                                                            
                                                                                
                                               
                                 
                                                          
                    
               
                   
                                                        
                       
             
                                                          
                                                    
                       
             
                                                    
                                                          

end ExactSinTheta
end DavisKahan
end TauCeti