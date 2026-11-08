/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.Geometry.Angle.OperatorAngleComplex
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.DavisKahan.Geometry.Angle.OperatorAngleReal
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.vd0883627faf7.ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# The literal operator angle of Davis--Kahan

The accepted sine theorem uses the positive sine operator directly.  The 1970
paper first defines a Hermitian operator angle and then applies scalar
trigonometric functions to it.  This file restores that literal object without
changing the already verified theorem.

For complex Hilbert spaces the canonical angle is
`arcsin |P_U - P_V|` through continuous functional calculus.  Its spectrum is
contained in `[0, pi / 2]`, and applying sine recovers exactly the accepted
sine operator.  For real Hilbert spaces the literal angle is the same object
on the canonical complexification; this is the construction used elsewhere in
the repository for real operator functional calculus.
-/
namespace TauCeti
namespace DavisKahanExt
open DavisKahan
open scoped InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
section Real
open TauCeti.DavisKahan.Foundation
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification
open TauCeti.DavisKahanExt.Real
variable {ER : Type*} [NormedAddCommGroup ER] [InnerProductSpace ℝ ER]
  [CompleteSpace ER]
/-! The real algebra structure and the real continuous functional calculus on the
complexified operator algebra are `scoped instance`s of
`RealComplexification`, opened below.  They used to be reinstalled
here as a second `local instance`, which made them a *different declaration* from the
one the imported lemmas are stated against; see lane `{lane:CPLX-DEDUP-3}`. -/
open scoped TauCeti.RealComplexification
end Real
end
end DavisKahanExt
end TauCeti