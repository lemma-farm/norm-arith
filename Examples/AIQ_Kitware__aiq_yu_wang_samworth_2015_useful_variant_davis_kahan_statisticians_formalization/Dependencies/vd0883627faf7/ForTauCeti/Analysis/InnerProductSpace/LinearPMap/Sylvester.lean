/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module
public import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import Mathlib
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
theorem add {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X Y C D : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C)
    (hY : SylvesterEquation A B Y D) :
    SylvesterEquation A B (X + Y) (C + D) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.add_mem (hX.mapsTo_domain x) (hY.mapsTo_domain x)
  · intro x
    have hxX : X (x : F) ∈ A.domain := hX.mapsTo_domain x
    have hxY : Y (x : F) ∈ A.domain := hY.mapsTo_domain x
    let uX : A.domain := ⟨X (x : F), hxX⟩
    let uY : A.domain := ⟨Y (x : F), hxY⟩
    have hEqX : A uX - X (B x) = C (x : F) := by
      simpa [uX] using hX.equation x
    have hEqY : A uY - Y (B x) = D (x : F) := by
      simpa [uY] using hY.equation x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A (uX + uY) - (X (B x) + Y (B x)) =
      C (x : F) + D (x : F)
    calc
      A (uX + uY) - (X (B x) + Y (B x)) =
          (A uX - X (B x)) + (A uY - Y (B x)) := by
            rw [_root_.LinearPMap.map_add A uX uY]
            abel
      _ = C (x : F) + D (x : F) := by rw [hEqX, hEqY]
/-- Domain-aware Sylvester equations are preserved by negation. -/
theorem neg {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X C : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C) :
    SylvesterEquation A B (-X) (-C) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.neg_mem (hX.mapsTo_domain x)
  · intro x
    have hxX : X (x : F) ∈ A.domain := hX.mapsTo_domain x
    let uX : A.domain := ⟨X (x : F), hxX⟩
    have hEqX : A uX - X (B x) = C (x : F) := by
      simpa [uX] using hX.equation x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A (-uX) - (-X (B x)) = -C (x : F)
    calc
      A (-uX) - (-X (B x)) = -(A uX - X (B x)) := by
        rw [_root_.LinearPMap.map_neg A uX]
        abel
      _ = -C (x : F) := by rw [hEqX]
/-- Domain-aware Sylvester equations subtract. -/
theorem sub {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X Y C D : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C)
    (hY : SylvesterEquation A B Y D) :
    SylvesterEquation A B (X - Y) (C - D) := by
  simpa [sub_eq_add_neg] using hX.add hY.neg
/-- Domain-aware Sylvester equations commute with scalar multiplication. -/
theorem smul {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X C : F →L[𝕜] E}
    (hX : SylvesterEquation A B X C) (c : 𝕜) :
    SylvesterEquation A B (c • X) (c • C) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact A.domain.smul_mem c (hX.mapsTo_domain x)
  · intro x
    have hxX : X (x : F) ∈ A.domain := hX.mapsTo_domain x
    let uX : A.domain := ⟨X (x : F), hxX⟩
    have hEqX : A uX - X (B x) = C (x : F) := by
      simpa [uX] using hX.equation x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A (c • uX) - c • X (B x) = c • C (x : F)
    calc
      A (c • uX) - c • X (B x) = c • (A uX - X (B x)) := by
        rw [_root_.LinearPMap.map_smul A c uX, smul_sub]
      _ = c • C (x : F) := by rw [hEqX]
end SylvesterEquation
structure HasBoundedEverywhereInverse (A : E →ₗ.[𝕜] E) where
  inv : E →L[𝕜] E
  inv_mapsTo_domain : ∀ y, inv y ∈ A.domain
  apply_inv : ∀ y, A ⟨inv y, inv_mapsTo_domain y⟩ = y
  inv_apply : ∀ x : A.domain, inv (A x) = (x : E)
namespace HasBoundedEverywhereInverse
theorem surjective {A : E →ₗ.[𝕜] E}
    (hA : HasBoundedEverywhereInverse A) :
    Function.Surjective A := by
  intro y
  exact ⟨⟨hA.inv y, hA.inv_mapsTo_domain y⟩, hA.apply_inv y⟩
end HasBoundedEverywhereInverse
end LinearPMap
end TauCeti
end
