module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.PiL2

-- ==== Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Examples.Example_8259dc9cf19ec6b7fafd_CenteredScatter ====
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High, Claude Fable 5
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Finite means and centered scatter operators

For a finite family `z : Fin n → E` in an inner-product space, the centered scatter operator
is `∑ i, (zᵢ - mean z) ⊗ (zᵢ - mean z)`.  The primary theorem is the exact add-one update

`S(Fin.snoc z y) = S(z) + n/(n+1) • ((y - mean z) ⊗ (y - mean z))`,

from which Löwner monotonicity and quadratic-form growth are short corollaries.

## Main results

* `TauCeti.centeredScatter_append`: the exact operator-level add-one identity;
* `TauCeti.centeredScatter_le_append`: appending a point grows the scatter in Löwner order;
* `TauCeti.re_inner_centeredScatter_append`: the quadratic-form version of the update;
* `TauCeti.re_inner_centeredScatter_self`: the scatter quadratic form is the sum of
  squared centered inner products.

## Implementation notes

`centeredScatter` is a `ContinuousLinearMap`. Its summands `rankOne 𝕜 a a` are continuous
already, so taking the bundled linear map would discard continuity for nothing; the
`IsPositive` and Löwner-order API used below exists at both levels and needs no
completeness assumption.

`finiteMean` is *not* an instance of an existing Mathlib average.

* `Finset.expect`, the canonical finite average, requires `Module ℚ≥0 E`. That instance does
  not resolve for a general `𝕜`-inner-product space: `NormedSpace ℝ E` is reachable only
  through `InnerProductSpace.rclikeToReal` / `NormedSpace.restrictScalars`, which are
  deliberately definitions rather than instances.
* `Finset.centroid` does typecheck here, but `Finset.affineCombination` is defined against
  `Classical.arbitrary`, so the centroid of the empty family is nonconstructive junk.
  `finiteMean` instead returns `0` there, by Mathlib's total-inverse convention, and
  `finiteMean_append` is deliberately stated to hold *at* `n = 0`.

See backlog §8.1.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/InnerProductSpace/CenteredScatter.lean`
  at Davis--Kahan commit `fc38eb4`.
* Original declarations: `centeredScatter`, `finiteMean`, `appendFin` and the
  add-one / Löwner / quadratic-form API (namespace renamed here
  `ForMathlib` → `TauCeti`).
* Original authors / copyright: Jon Crall, GPT-5.6 High, Claude Fable 5;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system, then polished
  against the reuse rubric (backlog §8.1): `appendFin` was deleted in favour of
  `Fin.snoc`, and `centeredScatter` moved from `E →ₗ[𝕜] E` to `E →L[𝕜] E`.
* Spectra influence: **none** (imports only Mathlib).

Moved from
`ForTauCeti/Analysis/InnerProductSpace/CenteredScatter.lean` to
`ForTauCeti/Probability/Moments/CenteredScatter.lean`, beside `SampleMean`,
`SampleSecondMoment`, `Variance` and `MatrixConcentration`.  Finite means and
centered scatter operators are the content of roadmap topic T20, where this
module was already assigned; only its path disagreed.  Path change and
repointing of one import in `DkpsQuench2026/Spectral/GramSpectrum.lean` — no
statement, signature, proof, attribute, declaration name or namespace changed.
-/
public section
namespace TauCeti
open Module InnerProductSpace
open scoped BigOperators
variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
/-- Arithmetic mean of a `Fin n` family. At `n = 0`, Mathlib's total inverse convention makes
this zero. -/
noncomputable def finiteMean {n : ℕ} (z : Fin n → E) : E :=
  ((n : 𝕜)⁻¹) • ∑ i, z i
/-- Unnormalized centered scatter operator `∑ i, (zᵢ - mean z) ⊗ (zᵢ - mean z)`.

The rank-one convention is chosen so its quadratic form is
`∑ i, ‖⟪zᵢ - mean z, x⟫‖²`. -/
noncomputable def centeredScatter {n : ℕ} (z : Fin n → E) : E →L[𝕜] E :=
  ∑ i, rankOne 𝕜 (z i - finiteMean 𝕜 z) (z i - finiteMean 𝕜 z)


set_option linter.unusedVariables false in
/-- Appending a point can only increase the centered scatter in Löwner order. -/
theorem centeredScatter_le_append {n : ℕ} (z : Fin n → E) (y : E) 
    (h_TauCeti_centeredScatter_append : ∀ (𝕜 : Type u_1) {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]
      [inst_2 : InnerProductSpace 𝕜 E] {n : ℕ} (z : Fin n → E) (y : E),
      TauCeti.centeredScatter 𝕜 (Fin.snoc z y) =
        TauCeti.centeredScatter 𝕜 z +
          ((↑n : 𝕜) / ((↑n : 𝕜) + 1)) •
            ((InnerProductSpace.rankOne 𝕜 : E → E →L⋆[𝕜] E →L[𝕜] E) (y - TauCeti.finiteMean 𝕜 z) :
                E → E →L[𝕜] E)
              (y - TauCeti.finiteMean 𝕜 z))
    :
    centeredScatter 𝕜 z ≤ centeredScatter 𝕜 (Fin.snoc z y) := by
  rw [ContinuousLinearMap.le_def, h_TauCeti_centeredScatter_append, add_sub_cancel_left]
  set δ := y - finiteMean 𝕜 z with hδ
  have hcoef : (starRingEnd 𝕜) ((n : 𝕜) / ((n : 𝕜) + 1)) = (n : 𝕜) / ((n : 𝕜) + 1) := by
    simp
  have hre : ∀ u : E, RCLike.re (inner 𝕜
      ((((n : 𝕜) / ((n : 𝕜) + 1)) • rankOne 𝕜 δ δ) u) u) =
      ((n : ℝ) / ((n : ℝ) + 1)) * ‖inner 𝕜 δ u‖ ^ 2 := by
    intro u
    rw [smul_apply, inner_smul_left, hcoef,
      rankOne_apply, inner_smul_left, RCLike.conj_mul]
    have hcast : ((n : 𝕜) / ((n : 𝕜) + 1)) = (((n : ℝ) / ((n : ℝ) + 1) : ℝ) : 𝕜) := by
      push_cast
      rfl
    rw [hcast, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  constructor
  · intro u v
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_coe,
      inner_smul_left, inner_smul_right, hcoef, rankOne_apply]
    rw [inner_conj_symm]
    ring
  · intro u
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, hre u]
    positivity
end TauCeti
