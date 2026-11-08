/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module
public import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.ForTauCeti.Analysis.InnerProductSpace.Complexification.Basic
public import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
public import Mathlib
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
set_option autoImplicit false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Real descent for bounded functional calculus

This module exposes the canonical conjugation action on operators over a real
Hilbert-space complexification.  A conjugation-fixed complex operator descends
to a bounded real operator, and real continuous functional calculus preserves
the fixed-point subalgebra.  These are the reusable seams needed for real
infinite-dimensional polar factorization.

## Main definitions and results

* `TauCeti.RealComplexification.canonicalConjugation`: the canonical conjugation of a real
  complexification, an antilinear isometric involution;
* `TauCeti.RealComplexification.conjugateOperator`: the induced involution on bounded complex
  operators, together with its ring, norm and adjoint laws;
* `TauCeti.RealComplexification.conjugateOperator_cfc_eq`: continuous functional calculus
  commutes with the conjugation, so the fixed-point subalgebra is preserved;
  `conjugateOperator_cfc` is the same statement with the continuity side condition
  removed, and `conjugateOperator_modulus` extends it to the operator modulus;
* `TauCeti.RealComplexification.fixed_operator_maps_real_to_real`: a conjugation-fixed operator
  descends to the real subspace;
* `TauCeti.RealComplexification.complexify_adjoint` and `complexify_gram`: complexification
  intertwines adjoints and Gram operators.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/SpectralTheory/Complexification/FunctionalCalculus.lean`.
* Extraction class: **moved**, not restated.  Its only non-Mathlib import is
  `Complexification/Basic.lean`, which is already in `ForTauCeti`, so it depended on nothing
  in the paper library.
* The enclosing namespace was `TauCeti.DavisKahan.Experimental.ExactSinTheta.`
  `RealComplexificationFunctionalCalculus`: two paper names, a staging word, and a repetition
  of the parent.  It is now simply `TauCeti.RealComplexification`, the namespace of the
  `complexify` it is about — which is where `complexify_adjoint` and `complexify_gram` belonged
  all along.  The `scoped instance` moved with it, so consumers now write
  `open scoped TauCeti.RealComplexification`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none**.
-/
public section
open scoped InnerProductSpace ComplexConjugate Topology
namespace TauCeti
namespace RealComplexification
open Module (finrank)
open Filter
noncomputable section
universe v vF w
variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
/-- Scalar restriction of the complex operator algebra to the reals.

**`scoped`, deliberately, and not `local` or global.**  Global is the ℝ-algebra diamond that
Mathlib declines to install for `Algebra.complexToReal`, so that door stays shut.  `local` was
what this was until 2026-07-30, and it forced three other modules to reinstall a *second*
declaration of the same instance; lemmas stated against one copy then had to be proved defeq
against the other, which is what timed out `isDefEq` when `Threshold.lean` first tried to import
this module's lemmas.  A scope gives every consumer the *same* declaration, so there is nothing
to prove.  Open it with `open scoped RealComplexification`. -/
noncomputable scoped instance complexOperatorRealAlgebra :
    Algebra ℝ (RealComplexification E →L[ℂ] RealComplexification E) :=
  Algebra.complexToReal
/-- Real continuous functional calculus on the complexified operator algebra.  `scoped` for the
same reason as `complexOperatorRealAlgebra` above. -/
noncomputable scoped instance realContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ
      (RealComplexification E →L[ℂ] RealComplexification E) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
end
end RealComplexification
end TauCeti
