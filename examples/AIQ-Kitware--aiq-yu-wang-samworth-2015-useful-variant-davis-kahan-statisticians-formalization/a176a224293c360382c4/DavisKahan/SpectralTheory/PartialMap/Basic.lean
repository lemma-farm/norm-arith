/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import DavisKahan.BoundedOperator.Compat
import DavisKahan.SpectralTheory.AbstractSpectrum
import Mathlib
/-!
# The bundled closed-operator record is gone

`TauCeti.DavisKahanExt.ClosedOperator` was a `LinearPMap` together with dense
domain and closed graph as *fields*.  The canonical carrier is Mathlib's
`LinearPMap`, with those two as properties, and this module held the wrapper.
The `PartialMap` in this module's path is a directory name, not a second
carrier: it is where the Davis--Kahan additions to `LinearPMap` live.

Everything it declared has moved:

* the record, its `toLinearPMap` view and the coercion — deleted; a partial map
  is the operator, and density and closedness travel as hypotheses;
* `SameDomain`, `MapsDomainTo`, `BoundedExtension`, `Extends`, `IsSymmetric`,
  `IsSelfAdjoint`, `graphNorm`, `RelativelyBounded`, `realResolventSet`,
  `realSpectrum`, `SpectralSetsSeparated` — every one of these was an `abbrev`
  forwarding to the identically named `TauCeti.LinearPMap` declaration at
  `A.toLinearPMap`, so consumers name the canonical one;
* `ofBounded A` — the everywhere-defined view of a bounded operator, which is
  `A.toLinearMap.toPMap ⊤`, the spelling `ForTauCeti` already used;
* `addBounded` — now `TauCeti.LinearPMap.addBounded`, next to the `perturb` and
  `boundedPerturbation` it is built from.

The file survives as an import boundary -- it is named by a dozen modules and
supplies the `ForTauCeti` partial-map layer together with the Davis--Kahan
bounded-operator compatibility layer they also need -- and carries the two
Davis--Kahan facts about partial maps that had nowhere else to go.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

                                                                         
                                                             
                                                                            
                                                                             
                                            
                                                                                  
                                             
                                             
                                                                

                                                                     
                                                                                 
                                                         
                                   
                                                              
                      
                                                                              
                                         
                                                          
         
                                                                        
               
                          
                                 
                    
                                                           
                                             
             


end DavisKahanExt
end TauCeti
