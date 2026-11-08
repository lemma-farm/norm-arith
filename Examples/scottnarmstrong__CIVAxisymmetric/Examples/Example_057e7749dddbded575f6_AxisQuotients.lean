-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Identities.MeridionalSlices
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Identities.RadialQuotientContinuous
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Identities.Axisymmetric
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Analysis.SegmentQuotient
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Zoom.MeridionalSmallnessLemmas
public import Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Zoom.AnisotropicConsequences
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
/-!
# The axis quotient, its integral representation, and the three-term selection

This file publishes the representation of the radial quotient `u_r / r` on the meridional
plane as an average of `∂_r u_r` along the segment from the axis (the paragraph after
`eq:aniso:circulation:pde`), together with the pointwise bounds this representation gives
on that segment, and the reflection-symmetric three-term selection used when
`MeridionalSmallness` fails (the paragraph after `eq:aniso:zoom:selected`).
-/
@[expose] public section
open Set Filter Topology
open CKN.Foundation.Parabolic CKN
set_option autoImplicit false
noncomputable section
namespace CIV
/-! ### Smoothness and differentiability of an axial slice, at a general component -/
private lemma contDiffOn_axial_component (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t) k) (vec3Ball (0 : Vec3) 1) := by
  have hemb : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => ((x, t) : Vec3 × ℝ))
      (vec3Ball (0 : Vec3) 1) := (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmaps : Set.MapsTo (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) (vec3Ball (0 : Vec3) 1)
      unitCylinder := by
    intro x hx
    unfold unitCylinder spaceTimeSet
    exact Set.mk_mem_prod hx ht
  exact contDiffOn_pi.1 (hu.comp hemb hmaps) k
private lemma differentiableAt_axial_component (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k : Fin 3) {p : Vec3} (hp : p ∈ vec3Ball (0 : Vec3) 1) :
    DifferentiableAt ℝ (fun x : Vec3 => u (x, t) k) p := by
  have hcd1 : ContDiffOn ℝ (1 : ℕ∞) (fun x : Vec3 => u (x, t) k) (vec3Ball (0 : Vec3) 1) :=
    (contDiffOn_axial_component u t hu ht k).of_le (by exact_mod_cast le_top)
  exact (hcd1.differentiableOn one_ne_zero).differentiableAt
    ((isOpen_vec3Ball 0 1).mem_nhds hp)
private lemma continuousOn_spatialPartial_axial_component (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k i : Fin 3) :
    ContinuousOn (fun p : Vec3 => spatialPartial (fun w => u w k) i (p, t))
      (vec3Ball (0 : Vec3) 1) := by
  have hcd1 : ContDiffOn ℝ (1 : ℕ∞) (fun x : Vec3 => u (x, t) k) (vec3Ball (0 : Vec3) 1) :=
    (contDiffOn_axial_component u t hu ht k).of_le (by exact_mod_cast le_top)
  exact (hcd1.continuousOn_fderiv_of_isOpen (isOpen_vec3Ball 0 1) le_rfl).clm_apply
    continuousOn_const
private lemma contDiffOn_spatialPartial_axial_component1 (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k i : Fin 3) :
    ContDiffOn ℝ (1 : ℕ∞) (fun p : Vec3 => spatialPartial (fun w => u w k) i (p, t))
      (vec3Ball (0 : Vec3) 1) := by
  have hcd2 : ContDiffOn ℝ (2 : ℕ∞) (fun x : Vec3 => u (x, t) k) (vec3Ball (0 : Vec3) 1) :=
    (contDiffOn_axial_component u t hu ht k).of_le (by exact_mod_cast le_top)
  have hfd : ContDiffOn ℝ (1 : ℕ∞) (fderiv ℝ (fun x : Vec3 => u (x, t) k)) (vec3Ball (0 : Vec3) 1) :=
    hcd2.fderiv_of_isOpen (isOpen_vec3Ball 0 1) (by norm_num)
  exact hfd.clm_apply contDiffOn_const
private lemma differentiableAt_spatialPartial_axial_component (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k i : Fin 3) {p : Vec3} (hp : p ∈ vec3Ball (0 : Vec3) 1) :
    DifferentiableAt ℝ (fun x : Vec3 => spatialPartial (fun w => u w k) i (x, t)) p :=
  ((contDiffOn_spatialPartial_axial_component1 u t hu ht k i).differentiableOn one_ne_zero).differentiableAt
    ((isOpen_vec3Ball 0 1).mem_nhds hp)
/-! ### The meridional segment through the axis -/
private lemma hasDerivAt_meridional_shift (x₃ s : ℝ) :
    HasDerivAt (fun a : ℝ => meridional a x₃) (basisVec 0 : Vec3) s := by
  have heq : (fun a : ℝ => meridional a x₃)
      = fun a : ℝ => a • (basisVec 0 : Vec3) + x₃ • basisVec 2 := by
    funext a; rw [meridional_eq]
  rw [heq]
  simpa using (hasDerivAt_id s).smul_const (basisVec 0 : Vec3) |>.add_const (x₃ • basisVec 2)
/-! ### The integral representation of the radial quotient -/
/-- The manuscript's `u_r/r`, extended across the axis, is the average of the radial
derivative `∂_r u_r` along the segment from the axis to `(x₁, x₃)` (the paragraph after
`eq:aniso:circulation:pde`). Public form of the `radialQuotient_eq_integral`. -/
theorem radialQuotient_eq_integral (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₁ x₃ : ℝ) (hx : x₁ ^ 2 + x₃ ^ 2 < 1) :
    radialQuotient u (meridional x₁ x₃, t) =
      ∫ s in (0:ℝ)..1, spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t) := by
  have hx3 : |x₃| < 1 := (sq_lt_one_iff_abs_lt_one x₃).mp (by nlinarith only [hx, sq_nonneg x₁])
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => u (meridional (s * x₁) x₃, t) 0)
        (x₁ * spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t)) s := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith only [hs.1], hs.2⟩
    have hmem : meridional (s * x₁) x₃ ∈ vec3Ball (0 : Vec3) 1 :=
      meridional_scale_mem_vec3Ball hx hs1
    have hdiff := differentiableAt_axial_component u t hu ht 0 hmem
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_meridional_scale x₁ x₃ s)
    rw [show (fderiv ℝ (fun x : Vec3 => u (x, t) 0) (meridional (s * x₁) x₃))
        (x₁ • basisVec 0) =
        x₁ * spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t) from by
      rw [map_smul, smul_eq_mul]; rfl] at hcomp
    exact hcomp
  have hint : IntervalIntegrable
      (fun s => x₁ * spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t))
      MeasureTheory.volume 0 1 := by
    have hcont := continuousOn_spatialPartial_axial_component u t hu ht 0 0
    have hpath : Continuous (fun s : ℝ => meridional (s * x₁) x₃) := by
      unfold meridional; fun_prop
    have hmaps : Set.MapsTo (fun s : ℝ => meridional (s * x₁) x₃) (Set.uIcc (0:ℝ) 1)
        (vec3Ball (0 : Vec3) 1) := by
      intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      exact meridional_scale_mem_vec3Ball hx (abs_le.mpr ⟨by linarith only [hs.1], hs.2⟩)
    exact (continuous_const.continuousOn.mul
      (hcont.comp' hpath.continuousOn hmaps)).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [one_mul, zero_mul] at hFTC
  rw [meridional_axis_component_zero u t haxi ht x₃ hx3, sub_zero,
    intervalIntegral.integral_const_mul] at hFTC
  simp only [radialQuotient, meridional_apply_zero]
  split_ifs with hx1
  · subst hx1
    simp only [mul_zero]
    rw [intervalIntegral.integral_const]
    simp
  · rw [div_eq_iff hx1, mul_comm]
    exact hFTC.symm
/-! ### Bound 1: the radial quotient on a segment through the axis -/
/-- `|u_r/r| ≤ M` at `(x₁, x₃)` whenever `|∂_r u_r| ≤ M` along the segment
`{(s x₁, x₃) : s ∈ [0, 1]}` from the axis, via the integral representation
`radialQuotient_eq_integral` (the paragraph after `eq:aniso:circulation:pde`). -/
theorem abs_radialQuotient_le_of_segment_bound (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₁ x₃ M : ℝ) (hx : x₁ ^ 2 + x₃ ^ 2 < 1)
    (hM : ∀ s ∈ Set.Icc (0:ℝ) 1,
      |spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t)| ≤ M) :
    |radialQuotient u (meridional x₁ x₃, t)| ≤ M := by
  rw [radialQuotient_eq_integral u t hu haxi ht x₁ x₃ hx]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := M)
    (f := fun s => spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t))
    (fun s hs => by
      rw [uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hs
      simpa [Real.norm_eq_abs] using hM s ⟨hs.1.le, hs.2⟩)
  simpa [Real.norm_eq_abs] using hbound
/-! ### Second partial derivatives along the meridional segment -/
end CIV
