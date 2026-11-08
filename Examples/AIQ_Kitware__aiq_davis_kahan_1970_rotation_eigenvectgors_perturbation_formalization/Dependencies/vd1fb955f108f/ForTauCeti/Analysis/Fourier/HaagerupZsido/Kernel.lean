/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.Fourier.ExponentialAbs
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.Fourier.Poisson.CauchyLattice
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.SpecialFunctions.Integral.RationalQuadratic
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.SpecialFunctions.Integral.SineLaplace
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.Fourier.HaagerupZsido.Defs
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.Fourier.HaagerupZsido.Integrability
public import Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.vd1fb955f108f.ForTauCeti.Analysis.Fourier.HaagerupZsido.Fourier
set_option autoImplicit false
set_option linter.deprecated false
set_option linter.deprecated.syntax false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# The Haagerup--Zsidó reciprocal Fourier kernel (aggregate)

This module is a transitional re-export aggregate.  The former single-file
development of the scalar Haagerup--Zsidó reciprocal Fourier kernel was split
into seven topic modules; this file re-exports all of them so that existing
consumers importing `ForTauCeti.Analysis.Fourier.HaagerupZsido.Kernel` continue
to see the entire `TauCeti.HaagerupZsido` API unchanged.

The split modules are:

* `ForTauCeti.Analysis.Fourier.ExponentialAbs` — exponential Fourier transform;
* `ForTauCeti.Analysis.Fourier.Poisson.CauchyLattice` — lattice sums / Poisson;
* `ForTauCeti.Analysis.SpecialFunctions.Integral.RationalQuadratic` —
  rational quadratic integrals;
* `ForTauCeti.Analysis.SpecialFunctions.Integral.SineLaplace` — sine--Laplace
  integrals;
* `ForTauCeti.Analysis.Fourier.HaagerupZsido.Defs` — kernel definitions and
  elementary API;
* `ForTauCeti.Analysis.Fourier.HaagerupZsido.Integrability` — kernel
  integrability and exact `L¹` mass;
* `ForTauCeti.Analysis.Fourier.HaagerupZsido.Fourier` — the exterior Fourier
  identity.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti` at Davis--Kahan
  commit `ad75dd6`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.

Moved from
`ForTauCeti/Analysis/Fourier/HaagerupZsidoKernel.lean` to
`ForTauCeti/Analysis/Fourier/HaagerupZsido/Kernel.lean`.
`Analysis/Fourier/HaagerupZsido/` already held `Defs`, `Fourier` and `Integrability`,
while this module sat beside the directory rather than inside it.  Path change and
repointing of imports only — no statement, signature, proof, attribute, declaration name or
namespace changed.
-/
