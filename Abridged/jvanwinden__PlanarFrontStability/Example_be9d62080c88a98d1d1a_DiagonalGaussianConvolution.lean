module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.v155535d682d6.Planarwave.Analysis.GaussianHeatKernel ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# The heat kernel and the paper's Fourier normalization

This identifies the Gaussian Fourier integral with the independently defined
Gaussian heat flow. All integral representations here are for positive time;
no spatial integrability of the bounded initial datum is required.
-/
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Planarwave
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- A real Gaussian density, normalized by its exact dimensional mass. -/
def gaussianDensity (b : ℝ) (x : V) : ℝ :=
  ((Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℝ))⁻¹ * Real.exp (-b * ‖x‖ ^ 2)

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

end
end Planarwave

end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Examples.Example_be9d62080c88a98d1d1a_DiagonalGaussianConvolution ====
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# Gaussian convolution through a finite diffusion eigenbasis

This is the matrix version of the Gaussian multiplier identity. A finite family
of Gaussian kernels is followed by fixed bounded operators and a fixed coordinate
map. All finite-coordinate and bounded-linear-map interchanges are justified in
the Banach norm.
-/
open MeasureTheory
open scoped RealInnerProductSpace
namespace Planarwave
noncomputable section
variable {V E G H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [Fintype ι]
/-- A finite diagonal Gaussian kernel, with arbitrary bounded coordinate maps. -/
def diagonalGaussianKernel (b : ι → ℝ) (A : ι → E →L[ℂ] G)
    (J : (ι → G) →L[ℂ] H) (x : V) : E →L[ℂ] H :=
  J.comp (ContinuousLinearMap.pi fun i ↦ gaussianDensity (4 * b i)⁻¹ x • A i)

omit [CompleteSpace E] [CompleteSpace G] [CompleteSpace H]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
set_option linter.unusedVariables false in
/-- Pointwise domination of the operator kernel by the finite sum of scalar densities. -/
theorem norm_diagonalGaussianKernel_le (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (A : ι → E →L[ℂ] G) (J : (ι → G) →L[ℂ] H) (x : V) 
    (h_Planarwave_gaussianDensity_nonneg : ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] {b : ℝ},
      0 < b → ∀ (x : V), 0 ≤ Planarwave.gaussianDensity b x)
    :
    ‖diagonalGaussianKernel b A J x‖ ≤
      ‖J‖ * ∑ i, gaussianDensity (4 * b i)⁻¹ x * ‖A i‖ := by
  classical
  have hρ (i : ι) : 0 ≤ gaussianDensity (4 * b i)⁻¹ x :=
    h_Planarwave_gaussianDensity_nonneg (by have := hb i; positivity) x
  have hnorm (i : ι) : ‖gaussianDensity (4 * b i)⁻¹ x • A i‖ =
      gaussianDensity (4 * b i)⁻¹ x * ‖A i‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ i)]
  have hpi : ‖ContinuousLinearMap.pi (fun i ↦ gaussianDensity (4 * b i)⁻¹ x • A i)‖ ≤
      ∑ i, gaussianDensity (4 * b i)⁻¹ x * ‖A i‖ := by
    apply ContinuousLinearMap.norm_pi_le_of_le
    · intro i
      rw [hnorm]
      exact Finset.single_le_sum (fun j _ ↦ mul_nonneg (hρ j) (norm_nonneg _)) (Finset.mem_univ i)
    · exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hρ i) (norm_nonneg _)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left hpi (norm_nonneg J))

end
end Planarwave
