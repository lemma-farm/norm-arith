module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.DirichletDyadicBlocks
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.VinogradovNarrowDirichlet
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.ZetaPrimeGram
public import Examples.TomasOrtega__Sidon.Dependencies.vb7e04ba12323.Sidon.NumberTheory.RiemannGaussian.ZetaPrimeMomentEnvelope
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian.VinogradovDyadic
noncomputable section
open scoped BigOperators
open RiemannGaussian.DirichletDyadicBlocks
theorem root_saving_le {M X delta : ℝ} (hM : 0 < M) (hX : 0 < X)
    (hupper : X ≤ 2 * M ^ 4) (hd : 0 ≤ delta) (hd4 : delta ≤ 4) :
    M ^ (-delta) ≤ 2 * X ^ (-delta / 4) := by
  have hbase : X / 2 ≤ M ^ 4 := by linarith
  have h := Real.rpow_le_rpow_of_nonpos (show 0 < X / 2 by positivity)
    hbase (show -delta / 4 ≤ 0 by linarith)
  have hleft : (M ^ 4) ^ (-delta / 4) = M ^ (-delta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    congr 1
    push_cast
    ring
  have htwo : (2 : ℝ) ^ (delta / 4) ≤ 2 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show delta / 4 ≤ 1 by linarith)).trans_eq
    exact Real.rpow_one _
  rw [hleft, Real.div_rpow hX.le (by norm_num)] at h
  have hinv : (2 : ℝ) ^ (-delta / 4) = ((2 : ℝ) ^ (delta / 4))⁻¹ := by
    rw [show -delta / 4 = -(delta / 4) by ring, Real.rpow_neg (by norm_num)]
  rw [hinv, div_inv_eq_mul] at h
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hX.le (-delta / 4))])
end
end RiemannGaussian.VinogradovDyadic
