/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.T12.Exterior
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.T12.InductionDefs
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.T12.Tails
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.ResolventNorm
import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.IDS.Green
import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Green.Iteration
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
namespace FroehlichSpencer.T12
open Multiscale
/--
With `X = max_{b, w ∈ B} ‖G_R(b, w)‖` one gets `X ≤ g + X / 2`, hence `X ≤ 2 g`.
-/
theorem norm_finiteGreen_le_of_twoCut {ν : ℕ} {R Cb B Q : Finset (Site ν)} (hB : B ⊆ Cb)
    (hCb : Cb ⊆ R) (hQ : Q = R \ B) (v : Site ν → ℝ) (E ε : ℝ) (hε : ε ≠ 0) {g η : ℝ}
    (hg0 : 0 ≤ g) (hη0 : 0 ≤ η)
    (hg : ∀ u w : {x // x ∈ Cb}, ‖finiteGreen ν Cb v E ε hε u w‖ ≤ g)
    (hη : ∀ c' q : {x // x ∈ Q}, (c' : Site ν) ∉ Cb → (∃ c ∈ Cb, hoppingKernel ν c c' ≠ 0) →
      (∃ b ∈ B, hoppingKernel ν q b ≠ 0) → ‖finiteGreen ν Q v E ε hε c' q‖ ≤ η)
    (hsmall : (2 * ν * Cb.card) * (2 * ν * B.card) * g * η ≤ 1 / 2)
    (u w : {x // x ∈ R}) (hu : (u : Site ν) ∈ B) (hw : (w : Site ν) ∈ B) :
    ‖finiteGreen ν R v E ε hε u w‖ ≤ 2 * g := by
  classical
  subst hQ
  set z : ℂ := (E : ℂ) + (ε : ℂ) * Complex.I with hz0
  have hz : z.im ≠ 0 := by simpa [hz0] using hε
  set a := hoppingKernel ν with ha
  set V : Site ν → ℝ := fun x => v x + 2 * (ν : ℝ) with hV
  have hsymm : ∀ x y, a y x = star (a x y) := hoppingKernel_symm ν
  have hBR : B ⊆ R := hB.trans hCb
  have hnorm_symm : ∀ x y, ‖a y x‖ = ‖a x y‖ := fun x y => by rw [hsymm x y, norm_star]
  have hunit : ∀ A : Finset (Site ν),
      IsUnit (Infra.restrictedOp a V A - z • (1 : Matrix A A ℂ)) := fun A =>
    FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _
      (Infra.isHermitian_restrictedOp hsymm V A) z hz
  have hne : (B ×ˢ B).Nonempty := ⟨(u.1, w.1), Finset.mem_product.2 ⟨hu, hw⟩⟩
  set X := (B ×ˢ B).sup' hne (fun p => ‖Infra.resolventColumn a V R z p.2 p.1‖) with hX
  have hXle : ∀ b ∈ B, ∀ y ∈ B, ‖Infra.resolventColumn a V R z y b‖ ≤ X := fun b hb y hy =>
    Finset.le_sup' (f := fun p => ‖Infra.resolventColumn a V R z p.2 p.1‖) (b := (b, y))
      (Finset.mem_product.2 ⟨hb, hy⟩)
  have hX0 : 0 ≤ X := (norm_nonneg _).trans (hXle u.1 hu w.1 hw)
  set S1 : ℝ := 2 * ν * Cb.card with hS1
  set S2 : ℝ := 2 * ν * B.card with hS2
  have hS1_0 : 0 ≤ S1 :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hS2_0 : 0 ≤ S2 :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  -- row sums against the block `B`
  have hrow : ∀ s : Finset (Site ν), ∑ q ∈ s, ∑ b ∈ B, ‖a q b‖ ≤ S2 := fun s => by
    rw [Finset.sum_comm]
    calc ∑ b ∈ B, ∑ q ∈ s, ‖a q b‖ = ∑ b ∈ B, ∑ q ∈ s, ‖a b q‖ := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun q _ => ?_
          exact hnorm_symm b q
      _ ≤ ∑ _b ∈ B, (2 * (ν : ℝ)) :=
          Finset.sum_le_sum fun b _ => sum_norm_hoppingKernel_le ν b s
      _ = S2 := by rw [Finset.sum_const, nsmul_eq_mul, hS2]; ring
  -- the `Q`-cut: entries `G_R(y, c')` for `c' ∈ R \ Cb`
  have hcut : ∀ y ∈ B, ∀ c ∈ Cb, ∀ c' ∈ R \ Cb, a c c' ≠ 0 →
      ‖Infra.resolventColumn a V R z y c'‖ ≤ η * S2 * X := by
    intro y hy c hc c' hc' hcc'
    have hc'R := (Finset.mem_sdiff.1 hc').1
    have hc'Cb := (Finset.mem_sdiff.1 hc').2
    have hc'B : c' ∉ B := fun h => hc'Cb (hB h)
    have hc'Q : c' ∈ R \ B := Finset.mem_sdiff.2 ⟨hc'R, hc'B⟩
    have hyQ : y ∉ R \ B := fun h => (Finset.mem_sdiff.1 h).2 hy
    have hid := Infra.resolventColumn_eq_neg_sum_coupling (a := a) V Finset.sdiff_subset
      (hunit R) (hunit (R \ B)) hc'Q (hBR hy) hyQ
    rw [Finset.sdiff_sdiff_eq_self hBR] at hid
    rw [hid, norm_neg]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ R \ B, ‖∑ k' ∈ B, Infra.resolventColumn a V (R \ B) z k c' * a k k' *
            Infra.resolventColumn a V R z y k'‖
        ≤ ∑ k ∈ R \ B, ∑ k' ∈ B, η * ‖a k k'‖ * X := by
          refine Finset.sum_le_sum fun k hk => ?_
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' hk' => ?_)
          rw [norm_mul, norm_mul]
          by_cases h0 : a k k' = 0
          · simp [h0]
          · have hkΛ : (k : Site ν) ∈ R \ B := hk
            have h1 := hη ⟨c', hc'Q⟩ ⟨k, hk⟩ hc'Cb ⟨c, hc, hcc'⟩ ⟨k', hk', h0⟩
            rw [finiteGreen_eq_resolventColumn] at h1
            exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
              (hXle k' hk' y hy) (norm_nonneg _) (mul_nonneg hη0 (norm_nonneg _))
      _ = η * X * ∑ k ∈ R \ B, ∑ k' ∈ B, ‖a k k'‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k' _ => by ring
      _ ≤ η * X * S2 := mul_le_mul_of_nonneg_left (hrow _) (mul_nonneg hη0 hX0)
      _ = η * S2 * X := by ring
  -- the `C̄`-cut
  have key : ∀ x ∈ B, ∀ y ∈ B, ‖Infra.resolventColumn a V R z y x‖ ≤ g + X / 2 := by
    intro x hx y hy
    have hxCb := hB hx
    have hyCb := hB hy
    have hid := resolventColumn_eq_sub_sum_coupling_of_mem (a := a) hsymm V hCb hz hxCb hyCb
    rw [hid]
    refine (norm_sub_le _ _).trans ?_
    have hg1 : ‖Infra.resolventColumn a V Cb z y x‖ ≤ g := by
      have := hg ⟨x, hxCb⟩ ⟨y, hyCb⟩
      rwa [finiteGreen_eq_resolventColumn] at this
    have hrest : ‖∑ k ∈ Cb, ∑ k' ∈ R \ Cb, Infra.resolventColumn a V Cb z k x * a k k' *
        Infra.resolventColumn a V R z y k'‖ ≤ X / 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k ∈ Cb, ‖∑ k' ∈ R \ Cb, Infra.resolventColumn a V Cb z k x * a k k' *
            Infra.resolventColumn a V R z y k'‖
          ≤ ∑ k ∈ Cb, ∑ k' ∈ R \ Cb, g * ‖a k k'‖ * (η * S2 * X) := by
            refine Finset.sum_le_sum fun k hk => ?_
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' hk' => ?_)
            rw [norm_mul, norm_mul]
            by_cases h0 : a k k' = 0
            · simp [h0]
            · have h1 := hg ⟨x, hxCb⟩ ⟨k, hk⟩
              rw [finiteGreen_eq_resolventColumn] at h1
              exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
                (hcut y hy k hk k' hk' h0) (norm_nonneg _) (mul_nonneg hg0 (norm_nonneg _))
        _ = g * (η * S2 * X) * ∑ k ∈ Cb, ∑ k' ∈ R \ Cb, ‖a k k'‖ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k' _ => by ring
        _ ≤ g * (η * S2 * X) * S1 := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg hg0 (mul_nonneg (mul_nonneg hη0 hS2_0) hX0))
            calc ∑ k ∈ Cb, ∑ k' ∈ R \ Cb, ‖a k k'‖ ≤ ∑ _k ∈ Cb, (2 * (ν : ℝ)) :=
                  Finset.sum_le_sum fun k _ => sum_norm_hoppingKernel_le ν k _
              _ = S1 := by rw [Finset.sum_const, nsmul_eq_mul, hS1]; ring
        _ = (S1 * S2 * g * η) * X := by ring
        _ ≤ 1 / 2 * X := mul_le_mul_of_nonneg_right hsmall hX0
        _ = X / 2 := by ring
    linarith
  have hX2 : X ≤ g + X / 2 :=
    Finset.sup'_le _ _ fun p hp => by
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
      exact key p.1 h1 p.2 h2
  rw [finiteGreen_eq_resolventColumn]
  have := hXle u.1 hu w.1 hw
  linarith
end FroehlichSpencer.T12
end
