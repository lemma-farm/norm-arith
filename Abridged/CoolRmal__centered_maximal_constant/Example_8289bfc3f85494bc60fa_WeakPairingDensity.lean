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

-- ==== Examples.CoolRmal__centered_maximal_constant.Examples.Example_8289bfc3f85494bc60fa_WeakPairingDensity ====
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
private theorem norm_integral_mul_sub_le (n : ℕ)
    (K φ g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : Integrable K) (hφ : Integrable φ)
    (hg : AEStronglyMeasurable g volume)
    {B : ℝ} (hB : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B) :
    ‖(∫ y, K y * g y) - (∫ y, φ y * g y)‖ ≤
      B * ∫ y, ‖K y - φ y‖ := by
  have hKg : Integrable (fun y ↦ K y * g y) := hK.mul_bdd hg hB
  have hφg : Integrable (fun y ↦ φ y * g y) := hφ.mul_bdd hg hB
  have hdiff : Integrable (fun y ↦ (K y - φ y) * g y) :=
    (hK.sub hφ).mul_bdd hg hB
  have hnormdiff : Integrable (fun y ↦ ‖K y - φ y‖) := (hK.sub hφ).norm
  rw [← integral_sub hKg hφg]
  have hfun : (fun y ↦ K y * g y - φ y * g y) =
      (fun y ↦ (K y - φ y) * g y) := by
    funext y
    ring
  rw [hfun]
  calc
    ‖∫ y, (K y - φ y) * g y‖ ≤
        ∫ y, ‖(K y - φ y) * g y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, B * ‖K y - φ y‖ := by
      apply integral_mono_ae hdiff.norm (hnormdiff.const_mul B)
      filter_upwards [hB] with y hy
      rw [norm_mul]
      calc
        ‖K y - φ y‖ * ‖g y‖ ≤ ‖K y - φ y‖ * B :=
          mul_le_mul_of_nonneg_left hy (norm_nonneg _)
        _ = B * ‖K y - φ y‖ := mul_comm _ _
    _ = B * ∫ y, ‖K y - φ y‖ := by rw [integral_const_mul]

end CenteredMaximal.Ball
