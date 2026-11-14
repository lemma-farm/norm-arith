module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

-- ==== Examples.CoolRmal__centered_maximal_constant.Examples.Example_df205d6c7dde83d3100b_WeakPairingDensity ====
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
set_option autoImplicit false
/-!
# Extending weak convergence of bounded densities to integrable kernels

Uniformly bounded densities define uniformly bounded functionals on `L¹`.
Consequently, convergence of their pairings with smooth compact tests extends to
all integrable kernels, including the singular Green kernels.
-/
@[expose] public section
noncomputable section
open MeasureTheory Metric Filter
open scoped ENNReal Topology
namespace CenteredMaximal.Ball
private axiom norm_integral_mul_sub_le (n : ℕ)
    (K φ g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : Integrable K) (hφ : Integrable φ)
    (hg : AEStronglyMeasurable g volume)
    {B : ℝ} (hB : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B) :
    ‖(∫ y, K y * g y) - (∫ y, φ y * g y)‖ ≤
      B * ∫ y, ‖K y - φ y‖
private axiom exists_smooth_compact_integral_norm_sub_le (n : ℕ)
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) φ ∧
        (∫ y, ‖K y - φ y‖) ≤ ε
/-- A uniformly bounded sequence of densities that converges weakly against every
smooth compactly supported test also converges against every integrable kernel.
This is the density step needed for Green kernels, which are singular but in `L¹`. -/
theorem tendsto_integral_mul_of_weak_test_convergence (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (gₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : AEStronglyMeasurable g volume)
    (hgₖ : ∀ k, AEStronglyMeasurable (gₖ k) volume)
    (B : ℝ) (hB₀ : 0 ≤ B)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ‖gₖ k y‖ ≤ B)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        Tendsto (fun k ↦ ∫ y, φ y * gₖ k y) atTop (𝓝 (∫ y, φ y * g y)))
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K) :
    Tendsto (fun k ↦ ∫ y, K y * gₖ k y) atTop (𝓝 (∫ y, K y * g y)) := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  let δ : ℝ := ε / (8 * (B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨φ, hφsupp, hφsmooth, hclose⟩ :=
    exists_smooth_compact_integral_norm_sub_le n K hK hδ
  have hφint : Integrable φ := hφsmooth.continuous.integrable_of_hasCompactSupport hφsupp
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hweak φ hφsupp hφsmooth))
    (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ ?_⟩
  rw [Real.dist_eq]
  have hleft := norm_integral_mul_sub_le n K φ (gₖ k) hK hφint
    (hgₖ k) (hBgₖ k)
  have hright := norm_integral_mul_sub_le n K φ g hK hφint hg hBg
  have hsmall : B * (∫ y, ‖K y - φ y‖) ≤ B * δ :=
    mul_le_mul_of_nonneg_left hclose hB₀
  have hmiddle : |(∫ y, φ y * gₖ k y) - (∫ y, φ y * g y)| < ε / 2 := by
    simpa only [Real.dist_eq] using hN k hk
  have htri : |(∫ y, K y * gₖ k y) - (∫ y, K y * g y)| ≤
      |(∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y)| +
      |(∫ y, φ y * gₖ k y) - (∫ y, φ y * g y)| +
      |(∫ y, φ y * g y) - (∫ y, K y * g y)| := by
    have h₁ := abs_add_le
      ((∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y))
      ((∫ y, φ y * gₖ k y) - (∫ y, φ y * g y))
    have h₂ := abs_add_le
      (((∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y)) +
        ((∫ y, φ y * gₖ k y) - (∫ y, φ y * g y)))
      ((∫ y, φ y * g y) - (∫ y, K y * g y))
    have h₃ :
        |((∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y)) +
          ((∫ y, φ y * gₖ k y) - (∫ y, φ y * g y)) +
          ((∫ y, φ y * g y) - (∫ y, K y * g y))| ≤
        |(∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y)| +
        |(∫ y, φ y * gₖ k y) - (∫ y, φ y * g y)| +
        |(∫ y, φ y * g y) - (∫ y, K y * g y)| := by linarith
    convert h₃ using 1; ring_nf
  calc
    |(∫ y, K y * gₖ k y) - (∫ y, K y * g y)| ≤ _ := htri
    _ < B * δ + ε / 2 + B * δ := by
      rw [abs_sub_comm (∫ y, φ y * g y) (∫ y, K y * g y)]
      have hl : |(∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y)| ≤ B * δ :=
        hleft.trans hsmall
      have hr : |(∫ y, K y * g y) - (∫ y, φ y * g y)| ≤ B * δ :=
        hright.trans hsmall
      linarith
    _ < ε := by
      have hBpos : 0 < B + 1 := by linarith
      have hratio : B / (B + 1) < 1 :=
        (div_lt_one hBpos).2 (by linarith)
      have hbound : B * δ < ε / 8 := by
        calc
          B * δ = (ε / 8) * (B / (B + 1)) := by
            dsimp [δ]
            field_simp
          _ < (ε / 8) * 1 := mul_lt_mul_of_pos_left hratio (by positivity)
          _ = ε / 8 := by ring
      linarith

end CenteredMaximal.Ball
