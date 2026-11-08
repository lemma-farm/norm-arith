/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.v1a3be1e8e419.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
set_option autoImplicit false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Sylvester equations for partial linear maps

The domain-aware equation `A X - X B = C`, semibounds, and bounded-everywhere
inverse data stated directly for Mathlib `LinearPMap` operators.  Analytic
properties such as closedness, dense domain, and self-adjointness remain
separate hypotheses for the theorems that require them.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/Sylvester/ClosedSylvesterEquation.lean`.
* Extraction class: **representation migration and generalization** from the
  bundled DKPS `PartialMap` to raw Mathlib `LinearPMap`.
* Spectra influence: none.  This module depends only on Mathlib and the
  dependency-clean `LinearPMap` domain API.
-/
public section
namespace TauCeti
namespace LinearPMap
open scoped InnerProductSpace
universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
structure SylvesterEquation
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (X C : F →L[𝕜] E) : Prop where
  mapsTo_domain : MapsDomainTo A B X
  equation : ∀ x : B.domain,
    A ⟨X (x : F), mapsTo_domain x⟩ - X (B x) = C (x : F)
namespace SylvesterEquation
theorem zero (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    SylvesterEquation A B 0 0 := by
  refine ⟨?_, ?_⟩
  · intro x
    simp
  · intro x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A (0 : A.domain) - 0 = (0 : E)
    simp
end SylvesterEquation
structure HasBoundedEverywhereInverse (A : E →ₗ.[𝕜] E) where
  inv : E →L[𝕜] E
  inv_mapsTo_domain : ∀ y, inv y ∈ A.domain
  apply_inv : ∀ y, A ⟨inv y, inv_mapsTo_domain y⟩ = y
  inv_apply : ∀ x : A.domain, inv (A x) = (x : E)
namespace HasBoundedEverywhereInverse
/-- A partial map with an everywhere-defined two-sided inverse is injective. -/
theorem injective {A : E →ₗ.[𝕜] E}
    (hA : HasBoundedEverywhereInverse A) :
    Function.Injective A := by
  intro x y hxy
  apply Subtype.ext
  calc
    (x : E) = hA.inv (A x) := (hA.inv_apply x).symm
    _ = hA.inv (A y) := congrArg hA.inv hxy
    _ = (y : E) := hA.inv_apply y
end HasBoundedEverywhereInverse
end LinearPMap
end TauCeti
end
