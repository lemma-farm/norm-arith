module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

-- ==== Examples.CoolRmal__falconer_packing.Examples.Example_e4bff8a337870dd387fb_SelectedTubeGeometry ====
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
set_option autoImplicit false
/-!
# Geometric containment for selected tube tests

Rectangles below are specified by their half-widths. The proof allows a change of frame
of order a/b, and keeps the transverse and longitudinal bounds separate.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open Classical
namespace FalconerPacking
/-- A closed rectangle centered at c, with half-widths a and b in the frame O. -/
def frameRectangle
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | |(O (x - c)) 0| ≤ a ∧ |(O (x - c)) 1| ≤ b}


set_option linter.unusedVariables false in
/-- All enlarged children meeting one dual rectangle fit inside a tube centered at any
one of them, even after a frame mismatch of size C₀a/b. -/
theorem mem_frameRectangle_of_common_intersections
    (O V : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {a b t C₀ : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 1 ≤ t) (hC : 0 ≤ C₀)
    (hframe : ∀ y i, |(V y) i - (O y) i| ≤ C₀ * (a / b) * ‖y‖)
    {c q q₀ x z z₀ : EuclideanSpace ℝ (Fin 2)}
    (hx : ‖x - q‖ ≤ t * a) (hzq : ‖z - q‖ ≤ t * a)
    (hz₀q : ‖z₀ - q₀‖ ≤ t * a)
    (hz : z ∈ frameRectangle O c a b) (hz₀ : z₀ ∈ frameRectangle O c a b) 
    (h_FalconerPacking_norm_le_frame_coordinate_sum : ∀ (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 2)),
      ‖x‖ ≤
        |((O : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) x).ofLp 0| +
          |((O : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) x).ofLp 1|)
    (h_FalconerPacking_frameRectangle_sub_bounds : ∀ (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) {c z z₀ : EuclideanSpace ℝ (Fin 2)}
      {a b : ℝ},
      z ∈ FalconerPacking.frameRectangle O c a b →
        z₀ ∈ FalconerPacking.frameRectangle O c a b →
          |((O : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (z - z₀)).ofLp 0| ≤ 2 * a ∧
            |((O : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (z - z₀)).ofLp 1| ≤ 2 * b)
    :
    x ∈ frameRectangle V q₀ ((5 + 7 * C₀) * t * a) ((5 + 7 * C₀) * t * b) := by
  have hb : 0 < b := ha.trans_le hab
  have ht₀ : 0 ≤ t := le_trans (by norm_num) ht
  let e := (x - q) + (q - z) + (z₀ - q₀)
  have he : ‖e‖ ≤ 3 * t * a := by
    have hqz : ‖q - z‖ ≤ t * a := by simpa only [norm_sub_rev] using hzq
    calc
      ‖e‖ ≤ ‖x - q‖ + ‖q - z‖ + ‖z₀ - q₀‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  have hdecomp : x - q₀ = e + (z - z₀) := by dsimp [e]; abel
  obtain ⟨hz₀, hz₁⟩ := h_FalconerPacking_frameRectangle_sub_bounds O hz hz₀
  have hc (i : Fin 2) : |(O e) i| ≤ 3 * t * a := by
    have hi := PiLp.norm_apply_le (O e) i
    simpa only [Real.norm_eq_abs, O.norm_map] using hi.trans (by simpa using he)
  have hcoord₀ : |(O (x - q₀)) 0| ≤ 3 * t * a + 2 * a := by
    rw [hdecomp, map_add]
    exact (abs_add_le _ _).trans (add_le_add (hc 0) hz₀)
  have hcoord₁ : |(O (x - q₀)) 1| ≤ 3 * t * a + 2 * b := by
    rw [hdecomp, map_add]
    exact (abs_add_le _ _).trans (add_le_add (hc 1) hz₁)
  have hnorm : ‖x - q₀‖ ≤ 3 * t * a + 4 * b := by
    have hzNorm := h_FalconerPacking_norm_le_frame_coordinate_sum O (z - z₀)
    rw [hdecomp]
    exact (norm_add_le _ _).trans (by linarith)
  have herror : C₀ * (a / b) * ‖x - q₀‖ ≤ 7 * C₀ * t * a := by
    calc
      _ ≤ C₀ * (a / b) * (3 * t * a + 4 * b) := by gcongr
      _ = 3 * C₀ * t * a * (a / b) + 4 * C₀ * a := by field_simp
      _ ≤ 3 * C₀ * t * a + 4 * C₀ * a := by
        apply add_le_add_left
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          ((div_le_one hb).mpr hab) (show 0 ≤ 3 * C₀ * t * a by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ht (mul_nonneg hC ha.le)]
  have hVcoord (i : Fin 2) : |(V (x - q₀)) i| ≤
      |(O (x - q₀)) i| + 7 * C₀ * t * a := by
    calc
      _ ≤ |(O (x - q₀)) i| + |(V (x - q₀)) i - (O (x - q₀)) i| := by
        simpa only [add_sub_cancel] using abs_add_le ((O (x - q₀)) i)
          ((V (x - q₀)) i - (O (x - q₀)) i)
      _ ≤ _ := add_le_add le_rfl ((hframe _ i).trans herror)
  constructor
  · nlinarith [hVcoord 0, mul_le_mul_of_nonneg_right ht ha.le]
  · have hta : t * a ≤ t * b := mul_le_mul_of_nonneg_left hab ht₀
    have hCa : 7 * C₀ * t * a ≤ 7 * C₀ * t * b := by gcongr
    nlinarith [hVcoord 1, mul_le_mul_of_nonneg_right ht hb.le]
end FalconerPacking
