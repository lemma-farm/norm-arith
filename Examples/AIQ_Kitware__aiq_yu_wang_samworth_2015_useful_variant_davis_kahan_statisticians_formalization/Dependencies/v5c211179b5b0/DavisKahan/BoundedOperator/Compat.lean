/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.v5c211179b5b0.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.v5c211179b5b0.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# The bounded Davis--Kahan vocabulary

The paper library's names for the bounded operator geometry it uses: `projection`
for an orthogonal projector, `Reduces` for a reducing subspace, `subspaceGap` for
the projection gap, and so on.  **Every declaration here is a forwarding name.**
Nothing is proved in this file; each line points at the general statement in
`ForTauCeti`, in Mathlib, or in one of `ForTauCeti`'s own generic modules.

## Why this file exists, and why it is here rather than in `ForTauCeti`

It was `ForTauCeti/Analysis/InnerProductSpace/BoundedOperator/Basic.lean` until
2026-07-30, when lane `RUB-NS-PAPER` measured what that module contained: all
twenty-one of its declarations were one-line forwards, and they opened the
namespace `TauCeti.DavisKahan` — a paper's name — inside the *generic* library.

Both halves of that are wrong for `ForTauCeti`, and they are wrong in opposite
directions, which is why the fix is a move and not a rename:

* A compatibility alias is not generic mathematics.  `ForTauCeti` is staged for
  Tau Ceti, and Tau Ceti has no use for a second spelling of `starProjection`.
* The mathematics the aliases pointed at **is** generic, and it stayed behind: it
  now lives in `Submodule` and `ContinuousLinearMap`, next to the objects it is
  about.

So the vocabulary comes back to the paper library that wanted it, keeping its
namespace and every name, and the two real theorems of the former
`BoundedOperator/{Projector,SinTheta}.lean` — the dimension-free directed `sin Θ`
bound and the sharp factor-one projector bound — stay in `ForTauCeti` under
`Submodule` and are re-exported below.  No consumer in `DavisKahan/**` changes.

**Do not add mathematics to this file.**  A new bounded-operator result belongs
in `ForTauCeti` under the namespace of the object it is about; if the paper
library wants a shorter name for it, add one `export` line here.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/BoundedOperator/Basic.lean`, moved into
  `ForTauCeti` by lane Y3(b3) on 2026-07-29 and returned here by lane
  `RUB-NS-PAPER` on 2026-07-30.
* Extraction class: **not for extraction** — this is paper-library vocabulary.
-/
namespace TauCeti
namespace DavisKahan
open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
/-! ### Names that differ from the canonical one -/
export _root_.ContinuousLinearMap (Reduces)
export _root_.Submodule
  (reflectionOperator diagonalPart offDiagonalPart IsOffDiagonal
   reflectionOperator_comm_of_reduces
   reflectionOperator_involutive norm_reflectionOperator_le_one
   reflectionOperator_norm_map reflectionOperator_surjective reflectionOperator_apply
   projectionGap_comm starProjection_orthogonal_apply
   two_smul_diagonalPart_eq_add_reflectionConjugate
   two_smul_offDiagonalPart_eq_sub_reflectionConjugate
   norm_starProjection_sub_eq_max directedProjectionGap_le_projectionGap
   projectionGap_eq_max_directedProjectionGap sinTheta_directed_coercive
   sinTheta_directed_of_formBounds opNorm_starProjection_sub_le_of_coercive
   opNorm_starProjection_sub_le_of_formBounds)
export _root_.ContinuousLinearMap (norm_add_eq_max_of_block)
end DavisKahan
end TauCeti
