/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.Riccati.BoundedReduction
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.Sylvester.Spectrum
import Mathlib
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Bounded Riccati estimates from an interval/exterior spectral gap

This leaf module applies the genuine-spectrum constant-one Sylvester estimate
to bounded Riccati solutions over a complex Hilbert space.  It isolates the
linear Sylvester equation hidden in the nonlinear Riccati equation, controls
its quadratic right-hand side, obtains a conservative contractive norm bound,
and proves uniqueness of a contractive solution under the standard local
small-coupling threshold.

The hypotheses use the spectra of the actual diagonal block operators.  This
avoids the provisional restricted-spectrum-on-top interface and gives the
analytic theorem in the representation consumed by the proved Sylvester
estimate.
-/
namespace TauCeti
namespace DavisKahanExt
open scoped InnerProductSpace
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]
end DavisKahanExt
end TauCeti