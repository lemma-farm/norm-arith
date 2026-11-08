/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Quadratic-form bounds on subspaces

Scalar-generic lower and upper bounds for the real part of the quadratic form
of a bounded operator, restricted to a subspace.  These predicates are useful
well beyond Davis--Kahan perturbation theory.

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
-/

public section


open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace TauCeti

/-! The Mathlib type namespace is mirrored *inside* `TauCeti`, matching the destination
library (Tau Ceti, e.g. `Analysis/Fredholm/Basic.lean` and
`LinearAlgebra/TotallyReal.lean`).  Root `ContinuousLinearMap` is deliberately not extended:
this repository cannot upstream to Mathlib, so a name taken there is a bet that can never be
settled by coordination.  Consumers get `A.LowerFormBoundOn U c` from `open TauCeti` --
being inside `namespace TauCeti` is *not* sufficient, as dot notation resolves through
`open`, not through the enclosing namespace. -/
namespace ContinuousLinearMap

open TauCeti

/-- Lower quadratic-form bound on a subspace. -/
@[expose]
def LowerFormBoundOn (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (c : ℝ) : Prop :=
  ∀ x ∈ U, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜

/-- Upper quadratic-form bound on a subspace. -/
@[expose]
def UpperFormBoundOn (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (c : ℝ) : Prop :=
  ∀ x ∈ U, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2

/-! ### Basic theory

The two ways a form bound weakens -- in the constant and in the subspace -- and the
identification of the degenerate case with Mathlib's `IsPositive`.  A consumer holding a
bound on `U` at constant `c` and needing one on a subspace of `U`, or at a worse constant,
should not have to reprove it from the definition. -/

                                                            
                                                                                  
                                                                           
                                                                            

                                                          
                                                                                     
                                                                           
                         

                                                             
                                                                                  
                                                                           
                                                                            

                                                           
                                                                                     
                                                                           
                         

                                                                                         
                                                                                        
                                        
                                                                             
                             
                                                                         

                                                                                         
                                                                                           
                                                      
                                                                                 
                                                  
                    
                                                                             

end ContinuousLinearMap

end TauCeti

