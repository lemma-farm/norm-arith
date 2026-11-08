/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.v59ebb0d788c4.DavisKahan.Geometry.Angle.OperatorAngleComplex
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.v59ebb0d788c4.DavisKahan.Geometry.Angle.OperatorAngleReal
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.v59ebb0d788c4.DavisKahan.Geometry.Angle.PaperOperatorAngle
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.v59ebb0d788c4.ForTauCeti.Analysis.InnerProductSpace.Projection.Gap
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.v59ebb0d788c4.DavisKahan.BoundedOperator.Compat
import Mathlib
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Canonical operator-angle compatibility surface

Literal positive angle operators require a complete complex Hilbert space, or
real complexification followed by the established descent bridges.  The former
scalar-generic facade attempted to hide those hypotheses and consequently had
no construction in the pinned foundations.  This module now exposes only the
scalar-generic graph predicates; the actual operators live in the canonical
complex and real-complexified modules imported above.
-/
namespace TauCeti
namespace DavisKahanExt
open DavisKahan
open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
/-- An ambient angular operator maps the selected subspace into its orthogonal
complement and vanishes on that complement. -/
def IsAngularOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : E →L[𝕜] E) : Prop :=
  X ∘L projection U = X ∧ projection U ∘L X = 0
end DavisKahanExt
end TauCeti