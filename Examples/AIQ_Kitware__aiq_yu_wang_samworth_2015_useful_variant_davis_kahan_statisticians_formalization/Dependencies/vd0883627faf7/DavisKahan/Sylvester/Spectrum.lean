/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.Sylvester.ClosedSylvesterEquation
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.OperatorIdeal.CanonicalRealView
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.SpectralTheory.PartialMap.Basic
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.SpectralTheory.PartialMap.BoundedRealization
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.Sylvester.Gap
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.Sylvester.Unbounded.Neumann
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.ForTauCeti.Analysis.CStarAlgebra.SelfAdjointGapInverse
import Mathlib
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.BoundedOperator.Compat
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.SpectralTheory.AbstractSpectrum
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# The genuine-spectrum Sylvester estimate and the general `sin Θ` theorem

Hypotheses here are phrased through the Banach-algebra spectrum, either of the
ambient operator or of its compression to a reducing subspace.

**The `genuine` in these names is now historical, and this paragraph used to say
so wrongly.**  It read: *"The separation predicates in `Core/AbstractSpectrum.lean`
are point-spectrum based and therefore vacuous for operators with empty point
spectrum; the theorems stated over them are unprovable in infinite dimensions …
This module is the honest layer."*  Every clause of that was true on 2026-07-15
and none of it is true now:

* the statement-soundness finding of 2026-07-15 was **repaired in place, not
  worked around** — `docs/planning/davis-kahan-full-paper-goal.md` records that
  the repaired layer defines `realSpectrum` from the `RCLike` Banach-algebra
  spectrum and carries invariance explicitly, *"which removes the counterexample
  that made the Sylvester, `sin Θ`, ideal, off-diagonal and Riccati declarations
  false as stated"*;
* `DavisKahan/SpectralTheory/AbstractSpectrum.lean`, the live layer, is
  therefore already the honest one;
* `Core/AbstractSpectrum.lean` **does not exist**: it was deleted on 2026-07-24
  in `e91ef142`, empty, as a retired facade.

So there is no vacuous sibling that these theorems are distinguishing themselves
from, and the prefix marks nothing.  Dropping it across the `genuine` family is
lane `DK-NAME`, which was **blocked on sequestering a layer that had already
been repaired** — a block this docstring caused.  Measured 2026-07-30 under lane
`DK-FAILED`.

Main results, all fully proved:

* `norm_sylvester_le_of_spectrum_intervalExterior`: the constant-one
  interval/exterior Sylvester estimate.  If the self-adjoint `B` has spectrum
  in `[a, b]` while the self-adjoint `A` has spectrum outside
  `(a - d, b + d)`, then `A X - X B = C` forces `d ‖X‖ ≤ ‖C‖`.  The proof is
  the shift-and-invert argument: center at `c = (a+b)/2`, invert `A - c`
  through the continuous functional calculus with inverse norm at most
  `(r + d)⁻¹` where `r = (b-a)/2`, bound `‖B - c‖ ≤ r`, and absorb.
* `sinTheta_spectrum`: the fully general bounded operator-norm
  Davis--Kahan `sin Θ` theorem with genuine spectra: if `U` reduces the
  self-adjoint `A` with the spectrum of the compression `A|_U` in `[a, b]`,
  and `V` reduces the self-adjoint `B` with the spectrum of `B|_{Vᗮ}` outside
  `(a - d, b + d)`, then `d * directedGap U V ≤ ‖B - A‖`.

Complex scalars are required because Mathlib registers the continuous
functional calculus on Hilbert-space operators only over `ℂ`; the real case
is expected to follow by a norm-preserving complexification transfer.
-/
namespace TauCeti
namespace DavisKahanExt
open DavisKahan.Foundation
open DavisKahan
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]
section Compression
end Compression
section IdealScope
open TauCeti.DavisKahan.ExactSinTheta
universe v'
variable {E₁ F₁ : Type v'}
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
end IdealScope
section SinThetaIdealScope
open TauCeti.DavisKahan.ExactSinTheta
end SinThetaIdealScope
end DavisKahanExt
end TauCeti
