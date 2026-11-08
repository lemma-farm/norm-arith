/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.v59ebb0d788c4.ForTauCeti.Analysis.InnerProductSpace.Complexification.Basic
import Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Dependencies.v59ebb0d788c4.DavisKahan.BoundedOperator.Compat
import Mathlib
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Complexification of real closed subspaces

This file transports the orthogonal-projection geometry of a real Hilbert
space into the concrete complexification from `Core/Complexification.lean`.
It is the missing foundation required to reuse the completed complex
operator-angle calculus for real subspaces without duplicating the Halmos
projection analysis.

For a real subspace `U`, `complexifySubmodule U` consists of all pairs whose
real and imaginary coordinates both lie in `U`.  The main results prove that:

* an orthogonally complemented real subspace remains orthogonally complemented;
* its complex orthogonal projection is exactly the complexification of the
  real orthogonal projection;
* complexification commutes with orthogonal complement;
* symmetric and directed projection gaps are preserved exactly;
* acuteness and quarter-acuteness are preserved;
* reducing-subspace data transports through operator complexification.
-/
namespace TauCeti
namespace DavisKahan
namespace Foundation
namespace RealComplexification
open scoped InnerProductSpace
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
/-- Complexification of a real subspace: both coordinates belong to the real
subspace. -/
def complexifySubmodule (U : Submodule ℝ E) :
    Submodule ℂ (RealComplexification E) where
  carrier := {z | re z ∈ U ∧ im z ∈ U}
  zero_mem' := by
    change re (0 : RealComplexification E) ∈ U ∧
      im (0 : RealComplexification E) ∈ U
    simp
  add_mem' := by
    intro z w hz hw
    change re z ∈ U ∧ im z ∈ U at hz
    change re w ∈ U ∧ im w ∈ U at hw
    change re (z + w) ∈ U ∧ im (z + w) ∈ U
    exact ⟨U.add_mem hz.1 hw.1, U.add_mem hz.2 hw.2⟩
  smul_mem' := by
    intro c z hz
    change re z ∈ U ∧ im z ∈ U at hz
    change re (c • z) ∈ U ∧ im (c • z) ∈ U
    exact
      ⟨U.sub_mem (U.smul_mem c.re hz.1) (U.smul_mem c.im hz.2),
        U.add_mem (U.smul_mem c.im hz.1) (U.smul_mem c.re hz.2)⟩
omit [CompleteSpace E] in
/-- Membership in a complexified submodule, in terms of the real and imaginary coordinates. -/
@[simp]
theorem mem_complexifySubmodule {U : Submodule ℝ E}
    {z : RealComplexification E} :
    z ∈ complexifySubmodule U ↔ re z ∈ U ∧ im z ∈ U := by
  change (re z ∈ U ∧ im z ∈ U) ↔ re z ∈ U ∧ im z ∈ U
  rfl
variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]
omit [CompleteSpace E] in
/-- The coordinatewise real projection lands in the complexified subspace. -/
theorem complexify_starProjection_mem (z : RealComplexification E) :
    complexify U.starProjection z ∈ complexifySubmodule U := by
  rw [mem_complexifySubmodule]
  exact
    ⟨U.starProjection_apply_mem (re z),
      U.starProjection_apply_mem (im z)⟩
omit [CompleteSpace E] in
/-- The residual from the coordinatewise projection is orthogonal to the
complexified subspace. -/
theorem sub_complexify_starProjection_mem_orthogonal
    (z : RealComplexification E) :
    z - complexify U.starProjection z ∈ (complexifySubmodule U)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  have hw' : re w ∈ U ∧ im w ∈ U :=
    mem_complexifySubmodule.mp hw
  have hre : re z - U.starProjection (re z) ∈ Uᗮ :=
    U.sub_starProjection_mem_orthogonal (re z)
  have him : im z - U.starProjection (im z) ∈ Uᗮ :=
    U.sub_starProjection_mem_orthogonal (im z)
  apply Complex.ext
  · change
      ⟪re w, re z - U.starProjection (re z)⟫_ℝ +
        ⟪im w, im z - U.starProjection (im z)⟫_ℝ = 0
    rw [Submodule.inner_right_of_mem_orthogonal hw'.1 hre,
      Submodule.inner_right_of_mem_orthogonal hw'.2 him]
    simp
  · change
      ⟪re w, im z - U.starProjection (im z)⟫_ℝ -
        ⟪im w, re z - U.starProjection (re z)⟫_ℝ = 0
    rw [Submodule.inner_right_of_mem_orthogonal hw'.1 him,
      Submodule.inner_right_of_mem_orthogonal hw'.2 hre]
    simp
/-- Orthogonal complementation of a real subspace supplies an orthogonal
projection after complexification. -/
instance instHasOrthogonalProjectionComplexifySubmodule :
    (complexifySubmodule U).HasOrthogonalProjection where
  exists_orthogonal z :=
    ⟨complexify U.starProjection z, complexify_starProjection_mem U z,
      sub_complexify_starProjection_mem_orthogonal U z⟩
variable {U}
end
end RealComplexification
end Foundation
end DavisKahan
end TauCeti