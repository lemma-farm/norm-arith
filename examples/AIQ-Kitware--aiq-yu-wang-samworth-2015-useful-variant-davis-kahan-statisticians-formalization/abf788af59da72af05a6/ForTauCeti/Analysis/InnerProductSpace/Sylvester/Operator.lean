/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound
public import Mathlib
/-! # The bounded Sylvester operator

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `df036cd`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).

Moved from
`ForTauCeti/Analysis/InnerProductSpace/SylvesterOperator.lean` to
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Operator.lean`.  The `Sylvester/`
directory already held `Basic`, `Interval`, `SpectralDistance` and `Internal/`, while
six siblings of the same family used a flat `Sylvester*` prefix in the directory above;
one family now has one convention.  Path change and import repoint only — no statement,
signature, proof, attribute, declaration name or namespace changed.
-/

public section


/-! The Sylvester operator is a statement about composition, so it is declared
over normed spaces rather than inner product spaces: nothing here, and nothing
proved about it downstream, uses an inner product.  Consumers that do work in a
Hilbert space are unaffected, since `InnerProductSpace.toNormedSpace` supplies
the instance. -/

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousLinearMap

/-- The Sylvester operator `X ↦ A X - X B`. -/
@[expose]
def sylvesterOperator (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (X : E →L[𝕜] F) : E →L[𝕜] F :=
  A ∘L X - X ∘L B

                                                                               

                                                                              
                                                                           
                                                                              
                                                                             
                     
         
                                                                      
                                    
                                          

                                                                       
       
                                                                                  
                                                 
       

                                                                                
                                 
                                                                
                                                        
     

end ContinuousLinearMap

