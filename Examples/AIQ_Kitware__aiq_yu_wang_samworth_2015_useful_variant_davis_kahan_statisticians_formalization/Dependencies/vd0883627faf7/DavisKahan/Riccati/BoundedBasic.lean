/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.SpectralTheory.GraphSubspace
import Mathlib
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Basic bounded block-operator and Riccati definitions

This module contains the dependency-minimal definitions shared by the bounded
Riccati leaf proofs.  The public facade is
`DavisKahan.InfiniteDimensional.Riccati.Bounded`.
-/
namespace TauCeti
namespace DavisKahanExt
open DavisKahan
open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]
end DavisKahanExt
end TauCeti