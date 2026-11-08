/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.v1a3be1e8e419.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Foundational definitions for strong unbounded Riccati theory

This module contains the shared block data, graph, and domain definitions used
by the proof leaves.  It intentionally contains no spectral-selection or
diagonalization theorem, so downstream leaves can import it without creating a
cycle through the public API.

The diagonal blocks are Mathlib `LinearPMap`s: density, closedness, and
self-adjointness are recorded as fields of the data rather than bundled into a
local operator type.  Unitary transport of a partial map is the canonical
`TauCeti.LinearPMap.UnitaryEquivalent`, and needs no local restatement.
-/
namespace TauCeti
namespace DavisKahanExt
open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]
/-- Unbounded diagonal block data with bounded off-diagonal coupling, in the
canonical partial-map representation.  Density, closedness, and
self-adjointness are explicit properties rather than fields of an operator
bundle. -/
structure UnboundedBlockData where
  A0 : E0 →ₗ.[𝕜] E0
  A1 : E1 →ₗ.[𝕜] E1
  B01 : E1 →L[𝕜] E0
  B10 : E0 →L[𝕜] E1
  dense0 : Dense (A0.domain : Set E0)
  dense1 : Dense (A1.domain : Set E1)
  closed0 : A0.IsClosed
  closed1 : A1.IsClosed
  selfAdjoint0 : _root_.IsSelfAdjoint A0
  selfAdjoint1 : _root_.IsSelfAdjoint A1
  offDiagonalAdjoint : ∀ x y, ⟪B01 y, x⟫_𝕜 = ⟪y, B10 x⟫_𝕜
namespace UnboundedBlockData
end UnboundedBlockData
/-- A bounded angular operator preserves the unbounded diagonal domains. -/
def PreservesRiccatiDomains
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∀ x : H.A0.domain, X (x : E0) ∈ H.A1.domain
noncomputable def unboundedBlockGraph (X : E0 →L[𝕜] E1) :
    Submodule 𝕜 (WithLp 2 (E0 × E1)) :=
  LinearMap.range ((WithLp.linearEquiv 2 𝕜 (E0 × E1)).symm.toLinearMap ∘ₗ
    LinearMap.id.prod X.toLinearMap)
end DavisKahanExt
end TauCeti
