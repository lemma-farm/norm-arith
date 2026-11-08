/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v28afaa9d8af8.FroehlichSpencer.Infra.Resolvent.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Matrix.Order
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Nonreal resolvents of Hermitian matrices

The estimates here abstract the finite-volume bound `|G| ≤ 1/|ε|` used in
Fröhlich–Spencer (1983), and the resolvent identities in equations (2.10)–(2.13),
pp. 159–160. They apply to arbitrary finite Hermitian matrices.
-/
public section
open scoped Matrix.Norms.L2Operator
namespace FroehlichSpencer
namespace Matrix
namespace IsHermitian
/-- The spectral formula for the inverse of `H - z I`, when `z` is off the real axis. -/
@[expose] noncomputable def spectralResolvent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) : Matrix ι ι ℂ :=
  (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
    Matrix.diagonal (fun i => ((hH.eigenvalues i : ℂ) - z)⁻¹) *
    star (hH.eigenvectorUnitary : Matrix ι ι ℂ)
/-- The spectral formula is a two-sided inverse of `H - z I` off the real axis. -/
theorem spectralResolvent_spec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    (H - z • (1 : Matrix ι ι ℂ)) * spectralResolvent hH z = 1 ∧
      spectralResolvent hH z * (H - z • (1 : Matrix ι ι ℂ)) = 1 := by
  let Uu := hH.eigenvectorUnitary
  let U : Matrix ι ι ℂ := Uu
  let eig : ι → ℂ := fun i => (hH.eigenvalues i : ℂ)
  let val : ι → ℂ := fun i => eig i - z
  let invVal : ι → ℂ := fun i => (val i)⁻¹
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) Uu
  have hval : ∀ i, val i ≠ 0 := by
    intro i hi
    have him := congrArg Complex.im hi
    have him' : -z.im = 0 := by simpa [val, eig] using him
    exact hz (neg_eq_zero.mp him')
  have hs : H = φ (Matrix.diagonal eig) := by
    simpa [φ, eig, Function.comp_def] using hH.spectral_theorem
  have hscalar : φ (z • (1 : Matrix ι ι ℂ)) = z • (1 : Matrix ι ι ℂ) := by
    simp [φ]
  have hdiag : Matrix.diagonal eig - z • (1 : Matrix ι ι ℂ) = Matrix.diagonal val := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  have hfact : H - z • (1 : Matrix ι ι ℂ) = U * Matrix.diagonal val * star U := by
    calc
      H - z • (1 : Matrix ι ι ℂ) = φ (Matrix.diagonal eig) - z • 1 := by rw [hs]
      _ = φ (Matrix.diagonal eig) - φ (z • (1 : Matrix ι ι ℂ)) := by rw [hscalar]
      _ = φ (Matrix.diagonal eig - z • (1 : Matrix ι ι ℂ)) := by rw [← map_sub]
      _ = φ (Matrix.diagonal val) := by rw [hdiag]
      _ = U * Matrix.diagonal val * star U := by
        change ((Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ)) Uu) _ = _
        rw [Unitary.conjStarAlgAut_apply]
  have hdiagLeft : Matrix.diagonal val * Matrix.diagonal invVal = 1 := by
    simp [Matrix.diagonal_mul_diagonal, invVal, hval]
  have hdiagRight : Matrix.diagonal invVal * Matrix.diagonal val = 1 := by
    simp [Matrix.diagonal_mul_diagonal, invVal, hval]
  have hUstar : star U * U = 1 := by
    simp [U, Uu]
  have hUstar' : U * star U = 1 := by
    simp [U, Uu]
  constructor
  · change (H - z • (1 : Matrix ι ι ℂ)) *
      (U * Matrix.diagonal invVal * star U) = 1
    rw [hfact]
    calc
      _ = U * (Matrix.diagonal val * (star U * U)) *
          Matrix.diagonal invVal * star U := by noncomm_ring
      _ = U * (Matrix.diagonal val * 1) * Matrix.diagonal invVal * star U := by rw [hUstar]
      _ = U * (Matrix.diagonal val * Matrix.diagonal invVal) * star U := by noncomm_ring
      _ = U * 1 * star U := by rw [hdiagLeft]
      _ = 1 := by simpa only [mul_one] using hUstar'
  · change (U * Matrix.diagonal invVal * star U) *
      (H - z • (1 : Matrix ι ι ℂ)) = 1
    rw [hfact]
    calc
      _ = U * Matrix.diagonal invVal * (star U * U) *
          Matrix.diagonal val * star U := by noncomm_ring
      _ = U * Matrix.diagonal invVal * 1 * Matrix.diagonal val * star U := by rw [hUstar]
      _ = U * (Matrix.diagonal invVal * Matrix.diagonal val) * star U := by noncomm_ring
      _ = U * 1 * star U := by rw [hdiagRight]
      _ = 1 := by simpa only [mul_one] using hUstar'
/-- A Hermitian matrix has no nonreal spectral parameter in the spectrum of `H`. -/
theorem isUnit_sub_zsmul_one_of_im_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    IsUnit (H - z • (1 : Matrix ι ι ℂ)) := by
  have h := spectralResolvent_spec hH z hz
  exact isUnit_iff_exists.mpr ⟨spectralResolvent hH z, h.1, h.2⟩
theorem norm_ringInverse_sub_zsmul_one_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    ‖(H - z • (1 : Matrix ι ι ℂ))⁻¹‖ ≤ 1 / |z.im| := by
  have him : 0 < |z.im| := abs_pos.mpr hz
  let Uu := hH.eigenvectorUnitary
  let U : Matrix ι ι ℂ := Uu
  let val : ι → ℂ := fun i => (hH.eigenvalues i : ℂ) - z
  let invVal : ι → ℂ := fun i => (val i)⁻¹
  have hspec := spectralResolvent_spec hH z hz
  have hinv : (H - z • (1 : Matrix ι ι ℂ))⁻¹ = spectralResolvent hH z := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    calc
      Ring.inverse (H - z • (1 : Matrix ι ι ℂ)) =
          Ring.inverse (H - z • (1 : Matrix ι ι ℂ)) *
            ((H - z • (1 : Matrix ι ι ℂ)) * spectralResolvent hH z) := by
              rw [hspec.1, mul_one]
      _ = (Ring.inverse (H - z • (1 : Matrix ι ι ℂ)) *
            (H - z • (1 : Matrix ι ι ℂ))) * spectralResolvent hH z := by rw [← mul_assoc]
      _ = spectralResolvent hH z := by
        rw [Ring.inverse_mul_cancel _
          (isUnit_sub_zsmul_one_of_im_ne_zero H hH z hz), one_mul]
  rw [hinv]
  change ‖U * Matrix.diagonal invVal * star U‖ ≤ 1 / |z.im|
  have hdiag : ‖Matrix.diagonal invVal‖ ≤ 1 / |z.im| := by
    rw [Matrix.l2_opNorm_diagonal]
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    have hden : |z.im| ≤ ‖val i‖ := by
      simpa [val] using (Complex.abs_im_le_norm (val i))
    calc
      ‖invVal i‖ = ‖val i‖⁻¹ := by simp [invVal, norm_inv]
      _ ≤ |z.im|⁻¹ := inv_anti₀ him hden
      _ = 1 / |z.im| := by rw [one_div]
  calc
    ‖U * Matrix.diagonal invVal * star U‖ = ‖Matrix.diagonal invVal‖ := by
      rw [mul_assoc]
      calc
        ‖(↑Uu : Matrix ι ι ℂ) *
            (Matrix.diagonal invVal * star (↑Uu : Matrix ι ι ℂ))‖ =
              ‖Matrix.diagonal invVal * star (↑Uu : Matrix ι ι ℂ)‖ :=
          CStarRing.norm_coe_unitary_mul Uu _
        _ = ‖Matrix.diagonal invVal‖ := CStarRing.norm_mul_coe_unitary _ (star Uu)
    _ ≤ 1 / |z.im| := hdiag
end IsHermitian
end Matrix
end FroehlichSpencer
