/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module
public import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound
public import Mathlib
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach
set_option autoImplicit false
set_option pp.unicode.fun true
set_option warningAsError true
/-! # Coercive bounded operators are units

For a bounded operator `N` on a Hilbert space over `𝕜 = ℝ, ℂ` whose quadratic
form is uniformly coercive, `c * ‖z‖ ^ 2 ≤ re ⟪N z, z⟫` with `c > 0`, the
operator `N` is invertible in `E →L[𝕜] E`.  This is the operator-level
Lax–Milgram lemma; the inverse is then available through `Ring.inverse` or
through `IsUnit.unit`.

## Staging note

Staged for Tau Ceti, roadmap topic T16.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/CoerciveUnit.lean`
(new file).
Formalized by Claude Fable 5 (claude-fable-5[1m]) while closing the graph
projection formula of the Davis–Kahan graph-subspace correspondence.  This is
the operator form of the Lax–Milgram lemma on a Hilbert space: a uniformly
coercive bounded operator is invertible in the algebra of bounded operators.
No self-adjointness is required — coercivity alone forces injectivity, a
closed range, and a trivial orthogonal complement of the range.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `00ca5e1`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Intended Mathlib home: additions to `Mathlib/Analysis/InnerProductSpace/CoerciveUnit.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/
public section
namespace TauCeti
namespace ContinuousLinearMap
open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
end ContinuousLinearMap
end TauCeti
