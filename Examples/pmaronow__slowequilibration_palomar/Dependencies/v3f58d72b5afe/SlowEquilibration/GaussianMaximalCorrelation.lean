-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.v3f58d72b5afe.SlowEquilibration.GaussianNoiseL2
set_option autoImplicit false
/-! Dimension-free Gaussian maximal correlation, derived from the genuine
complete product-Hermite Hilbert basis and the true Mehler noise law. -/
@[expose] public section
namespace SlowEquilibration.GaussianMaximalCorrelation
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped ENNReal Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {ι : Type*} [Fintype ι]
lemma hermite_coeff_eq_inner {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) (a : ι → ℕ) :
    coeff f a=inner ℝ (productHermiteBasis a) (hf.toLp f) := by
  have hBasis : productHermiteBasis a=psiVec a := by
    simp only [productHermiteBasis,HilbertBasis.coe_mkOfOrthogonalEqBot]
  rw [hBasis]
  exact (integral_inner_toLp (memLp_psi a) hf).symm
lemma hermite_hasSum_sq {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) :
    HasSum (fun a => (coeff f a)^2) (∫ x,f x^2 ∂γpi ι) := by
  have hs:=productHermiteBasis.hasSum_inner_mul_inner (hf.toLp f) (hf.toLp f)
  have hc (a : ι → ℕ) : inner ℝ (hf.toLp f) (productHermiteBasis a)=coeff f a := by
    rw [real_inner_comm]
    exact (hermite_coeff_eq_inner hf a).symm
  simp only [hc,← hermite_coeff_eq_inner hf,← pow_two] at hs
  simpa only [integral_inner_toLp hf hf,← pow_two] using hs
end
end SlowEquilibration.GaussianMaximalCorrelation
