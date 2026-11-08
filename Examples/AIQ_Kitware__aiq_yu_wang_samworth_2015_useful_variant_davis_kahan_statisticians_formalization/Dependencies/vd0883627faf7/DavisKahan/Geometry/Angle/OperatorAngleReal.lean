/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.SpectralTheory.Complexification.Subspace
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.Geometry.Angle.OperatorAngleComplex
import Mathlib
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Real operator angles through complexification

The complex operator-angle calculus is complete.  This file specializes it to real Hilbert subspaces by applying that calculus to their
canonical complexifications.  It avoids a second Halmos decomposition and
keeps every norm, gap, acuteness threshold, and projection identity tied to
the original real subspaces.

The operators in this file act on the complexified Hilbert space.  A later,
strictly smaller descent seam may show that the conjugation-invariant
operators preserve the canonical real copy and therefore bundle as real
operators.  All norm-level and projection-geometric content is already exact
here.
-/
namespace TauCeti
namespace DavisKahanExt
open DavisKahan
namespace Real
open scoped InnerProductSpace
noncomputable section
open TauCeti.DavisKahan.Foundation
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
end
end Real
end DavisKahanExt
end TauCeti