/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module
public import Examples.alejandro_soto_franco__EllipticPDE.Dependencies.ve6742b225530.EllipticPdes.Analysis.Mollifier
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Young's `Lᵖ` inequality for a probability kernel

On a finite-dimensional real normed space `E` with an additive Haar measure `μ`, convolving an
`Lᵖ` function `h : E → F` (with `1 ≤ p < ∞`) against a non-negative kernel of unit mass does not
increase its `Lᵖ` seminorm (`eLpNorm_convolution_le_of_integral_eq_one`). The proof derives the
pointwise bound from Hölder's inequality in `ℝ≥0∞` and closes with Tonelli, so no Minkowski
integral inequality is required.

The mollifications `ρₙ ⋆ h` of an `Lᵖ` function by normed bumps converge to `h` in `Lᵖ` as the
outer radii tend to `0` (`tendsto_eLpNorm_normed_convolution_sub`). The argument is a density
`3ε` argument: approximate `h` by a smooth compactly supported `w`
(`MeasureTheory.MemLp.exist_eLpNorm_sub_le`), control the tail `ρ ⋆ (h - w)` by the Young bound,
and drive `ρ ⋆ w - w` to zero with the uniform convergence of
`ContDiffBump.dist_normed_convolution_le` on a fixed compact set. It holds along an arbitrary
filter.

The real-valued statements with the kernel on the right (`eLpNorm_convolution_le`,
`contDiff_convolution_normed`, `tendsto_eLpNorm_convolution_sub`) are the forms the coordinate
files use; they are instances of the general statements through the commutativity of
convolution against scalar multiplication. The file also contains the elementary `Lᵖ`
bookkeeping shared by the Sobolev ladders and the continuous linear maps into `Lp` built from
almost everywhere linear families.
-/
@[expose] public section
open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology Pointwise
noncomputable section
namespace EllipticPdes.Embedding
section Young
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
end Young
/-! ### Real-valued statements with the kernel on the right -/
section RealKernelRight
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
end RealKernelRight
variable {d : ℕ}
theorem exists_const_eLpNorm_le_of_le {α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] [NormedAddCommGroup E] {p q : ℝ≥0∞} (hp : p ≠ 0) (hpq : p ≤ q) :
    ∃ A : ℝ≥0, ∀ f : α → E, AEStronglyMeasurable f μ → eLpNorm f p μ ≤ A * eLpNorm f q μ := by
  have he : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
    rcases eq_or_ne q ⊤ with rfl | hq
    · simp
    · rw [sub_nonneg]
      exact one_div_le_one_div_of_le (ENNReal.toReal_pos hp (ne_top_of_le_ne_top hq hpq))
        (ENNReal.toReal_mono hq hpq)
  refine ⟨(μ univ ^ (1 / p.toReal - 1 / q.toReal)).toNNReal, fun f hf => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top μ _)), mul_comm]
  exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf
def lpCLM {X α F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : X → α → F) (hT : ∀ x, MemLp (T x) p μ)
    (hadd : ∀ x y, T (x + y) =ᵐ[μ] T x + T y) (hsmul : ∀ (c : ℝ) x, T (c • x) =ᵐ[μ] c • T x)
    (C : ℝ≥0) (hC : ∀ x, eLpNorm (T x) p μ ≤ C * ‖x‖ₑ) : X →L[ℝ] Lp F p μ :=
  LinearMap.mkContinuous
    { toFun := fun x => (hT x).toLp (T x)
      map_add' := fun x y => by
        rw [MemLp.toLp_congr _ ((hT x).add (hT y)) (hadd x y), MemLp.toLp_add]
      map_smul' := fun c x => by
        rw [MemLp.toLp_congr _ ((hT x).const_smul c) (hsmul c x), MemLp.toLp_const_smul]
        rfl }
    C (fun x => by
      change ‖(hT x).toLp (T x)‖ ≤ C * ‖x‖
      rw [Lp.norm_toLp]
      refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg C.coe_nonneg (norm_nonneg x))
        ((hC x).trans_eq ?_)
      rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ofReal_norm])
/-- `lpCLM T` agrees almost everywhere with the family it is built from. -/
theorem coeFn_lpCLM {X α F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {T : X → α → F}
    {hT : ∀ x, MemLp (T x) p μ} {hadd : ∀ x y, T (x + y) =ᵐ[μ] T x + T y}
    {hsmul : ∀ (c : ℝ) x, T (c • x) =ᵐ[μ] c • T x} {C : ℝ≥0}
    {hC : ∀ x, eLpNorm (T x) p μ ≤ C * ‖x‖ₑ} (x : X) :
    ⇑(lpCLM T hT hadd hsmul C hC x) =ᵐ[μ] T x :=
  MemLp.coeFn_toLp (hT x)
/-- **Inclusion of `Lq` into `Lp` on a finite measure space**, for `p ≤ q`. -/
def lpInclusion {α F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : MeasurableSpace α}
    (μ : Measure α) [IsFiniteMeasure μ]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) : Lp F q μ →L[ℝ] Lp F p μ :=
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos (Fact.out : 1 ≤ p)).ne'
  lpCLM (fun f : Lp F q μ => ⇑f) (fun f => (Lp.memLp f).mono_exponent hpq)
    (fun f g => Lp.coeFn_add f g) (fun c f => Lp.coeFn_smul c f)
    (exists_const_eLpNorm_le_of_le (μ := μ) (E := F) hp0 hpq).choose fun f =>
    ((exists_const_eLpNorm_le_of_le (μ := μ) (E := F) hp0 hpq).choose_spec f
      (Lp.aestronglyMeasurable f)).trans_eq (by rw [Lp.enorm_def])
/-- The inclusion of `Lq` into `Lp` is the identity on representatives. -/
theorem coeFn_lpInclusion {α F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) (f : Lp F q μ) :
    ⇑(lpInclusion μ hpq f) =ᵐ[μ] ⇑f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hpq)
/-- The inclusion of `Lq` into `Lp` is injective. -/
theorem lpInclusion_injective {α F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ] {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] (hpq : p ≤ q) :
    Function.Injective (lpInclusion (F := F) μ hpq) := fun f g h =>
  Lp.ext ((coeFn_lpInclusion μ hpq f).symm.trans
    ((Lp.ext_iff.mp h).trans (coeFn_lpInclusion μ hpq g)))
end EllipticPdes.Embedding
