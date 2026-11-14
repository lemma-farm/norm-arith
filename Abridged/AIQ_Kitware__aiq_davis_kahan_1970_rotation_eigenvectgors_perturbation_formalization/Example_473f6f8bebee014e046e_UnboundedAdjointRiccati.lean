module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.v2fbc028a34ac.DavisKahan.Riccati.UnboundedBasic ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
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

end DavisKahanExt
end TauCeti

end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Examples.Example_473f6f8bebee014e046e_UnboundedAdjointRiccati ====
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# The complementary graph of a reducing Riccati selection

`ContractiveReducingGraphSelection.reduces` asserts that the angular graph
*reduces* the block core, which is strictly more than invariance: the orthogonal
complement is invariant too.  That second half has not been exploited anywhere,
and it is what supplies the adjoint-side domain compatibility

```
z ∈ dom A₁  →  X* z ∈ dom A₀
```

together with the adjoint Riccati equation.  Both are needed by the sharp
unbounded `tan 2Theta` argument, where the commutator `A₀X*X - X*XA₀` must be
shown bounded; the sharp tan(2Theta) note in Git history (ticket T1.1).

The file mirrors `UnboundedReduction`: first a coordinate characterization of
membership in the complement, then the domain-vector constructor, then the
equation itself.

The key geometric fact is that the orthogonal complement of the graph of `X` is
the graph of `-X*` **taken in the other order**:

```
(u, v) ⟂ {(w, X w)}  ↔  ∀ w, ⟪u, w⟫ + ⟪v, X w⟫ = 0  ↔  u = -X* v
```
-/
namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- The angular operator maps the second diagonal domain into the first.

This is the adjoint-side counterpart of `PreservesRiccatiDomains`, and it has
exactly the same status: a genuine hypothesis, not a consequence of reduction.
`ContractiveReducingGraphSelection` already records the forward version as a
separate field for this reason ("domain preservation is a separate field
because it is not a consequence of the ambient graph equality alone"), and the
adjoint side is no better.

Concretely, reduction *does* give something, just not enough. Writing
`R₀ := (I + X†X)⁻¹`, the projection-preserves-domain half of `ReducesSubspace`
applied to `(u, 0)` and to `(0, z)` yields

```
R₀ preserves dom A₀,      and      R₀ X† z ∈ dom A₀  for z ∈ dom A₁.
```

Recovering `X† z = (I + X†X)(R₀ X† z)` from the second then needs `X†X` to
preserve `dom A₀` — which is `gram_mem_domain`, itself a consequence of the
very statement being derived. The loop does not close, and the symmetric
attempt through `R₁ := (I + XX†)⁻¹` fails the same way: `R₁` preserves
`dom A₁`, but showing it *surjects* onto `dom A₁` again needs `X† z ∈ dom A₀`.

So this is carried as an explicit hypothesis throughout. It is not a hidden
seam: it is the adjoint twin of a hypothesis the repository already assumes. -/
def PreservesAdjointRiccatiDomains
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∀ z : H.A1.domain, (ContinuousLinearMap.adjoint X) (z : E1) ∈ H.A0.domain

/-- The commutator of the first diagonal block with the Gram operator `X†X`.

Both Riccati equations conspire so that this commutator, which a priori pairs an
unbounded operator with a bounded one, is itself **bounded**: writing `K = B₀₁X`
and `T = X†X` it is `(I + T)K - K†(I + T)`, so `‖G‖ ≤ 2(‖B₀₁‖ + ‖B₁₀‖)`. -/
noncomputable def riccatiGramCommutator
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : E0 →L[𝕜] E0 :=
  H.B01 ∘L X + ((ContinuousLinearMap.adjoint X) ∘L X) ∘L (H.B01 ∘L X) -
    ((ContinuousLinearMap.adjoint X) ∘L H.B10) -
      ((ContinuousLinearMap.adjoint X) ∘L H.B10) ∘L
        ((ContinuousLinearMap.adjoint X) ∘L X)

/-- The Gram operator `X†X` of a reducing Riccati selection, bundled. -/
noncomputable def riccatiGram (X : E0 →L[𝕜] E1) : E0 →L[𝕜] E0 :=
  (ContinuousLinearMap.adjoint X) ∘L X
section Powers
variable (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
variable {X : E0 →L[𝕜] E1} 
variable (hadj : PreservesAdjointRiccatiDomains H X)

/-- A contractive Gram operator stays contractive on every power. -/
theorem norm_riccatiGram_pow_apply_le
    {Y : E0 →L[𝕜] E1} (hY : ‖riccatiGram Y‖ ≤ 1) (n : ℕ) (y : E0) :
    ‖((riccatiGram Y) ^ n) y‖ ≤ ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : ((riccatiGram Y) ^ (n + 1)) y =
          riccatiGram Y (((riccatiGram Y) ^ n) y) := by
        rw [pow_succ']; rfl
      rw [hstep]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      calc ‖riccatiGram Y‖ * ‖((riccatiGram Y) ^ n) y‖
          ≤ 1 * ‖((riccatiGram Y) ^ n) y‖ :=
            mul_le_mul_of_nonneg_right hY (norm_nonneg _)
        _ ≤ ‖y‖ := by simpa using ih

end Powers
section Powers'
variable (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
variable {X : E0 →L[𝕜] E1} 
variable (hadj : PreservesAdjointRiccatiDomains H X)

end Powers'

end DavisKahanExt
end TauCeti
