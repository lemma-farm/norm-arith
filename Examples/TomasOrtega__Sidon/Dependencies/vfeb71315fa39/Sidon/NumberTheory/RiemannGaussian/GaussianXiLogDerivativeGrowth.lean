module
/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: David Sanftenberg
-/
/- Adapted from dbsanfte/RiemannGaussian; provenance and modifications are
recorded in docs/rg-extraction-manifest.json. -/
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Meromorphic.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.Meromorphic.RCLike
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
namespace RiemannGaussian
noncomputable section
open Filter MeromorphicOn Metric Set Topology
open scoped Topology
lemma norm_finsum_zsmul_le_of_nonneg
    {ι : Type*} {d : ι → ℤ} {f : ι → ℂ}
    (hd : (Function.support d).Finite)
    (hdnonneg : ∀ i, 0 ≤ d i) {C : ℝ}
    (hf : ∀ i, d i ≠ 0 → ‖f i‖ ≤ C) :
    ‖∑ᶠ i, d i • f i‖ ≤ ((∑ᶠ i, d i : ℤ) : ℝ) * C := by
  classical
  have hsub : Function.support (fun i => d i • f i) ⊆ hd.toFinset := by
    intro i hi
    apply hd.mem_toFinset.mpr
    intro hdi
    apply hi
    simp [hdi]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  calc
    ‖∑ i ∈ hd.toFinset, d i • f i‖ ≤
        ∑ i ∈ hd.toFinset, ‖d i • f i‖ := norm_sum_le _ _
    _ = ∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ) * ‖f i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_zsmul ℂ]
      rw [Complex.norm_int_of_nonneg (hdnonneg i)]
    _ ≤ ∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ) * C := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hdi : d i = 0
      · simp [hdi]
      · exact mul_le_mul_of_nonneg_left (hf i hdi) (by
          exact_mod_cast hdnonneg i)
    _ = (∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ)) * C := by
      rw [Finset.sum_mul]
    _ = (∑ᶠ i, ((d i : ℤ) : ℝ)) * C := by
      congr 1
      symm
      exact finsum_eq_sum_of_support_subset _ (by
        intro i hi
        apply hd.mem_toFinset.mpr
        intro hdi
        apply hi
        simp [hdi])
    _ = ((∑ᶠ i, d i : ℤ) : ℝ) * C := by
      congr 1
      exact (map_finsum (Int.castRingHom ℝ) hd).symm
end
end RiemannGaussian
