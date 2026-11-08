/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.SpectralTheory.PartialMap.Basic
import Mathlib
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Bounded realizations of closed operators

A closed operator whose domain is the whole space is the restriction of a
bounded operator.  `BoundedRealization` packages that bounded operator together
with the domain identity and the agreement statement.

This file is deliberately independent of the spectral hypotheses that usually
produce such a realization: the structure is pure bookkeeping, so it belongs
with the closed-operator basics rather than with any particular criterion.
-/
namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta
open scoped InnerProductSpace
universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
end ExactSinTheta
end DavisKahan
end TauCeti