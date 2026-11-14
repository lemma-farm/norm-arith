module

public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L2Space

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v0bab4bdfc62d.RothschildStein.H2.HolderSpaces ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]
/-- Hölder seminorm on a set, using Mathlib's least Hölder constant.
BB Definition 7.6, p. 298. An infinite value records failure of Hölder boundedness. -/
def holderSemi (δ : ℝ≥0) (A : Set X) (f : X → ℝ) : ℝ≥0∞ :=
  eHolderNorm δ (fun x : A => f x)
/-- Supremum term of the bounded Hölder norm, including the empty set. -/
def holderSup (A : Set X) (f : X → ℝ) : ℝ≥0∞ := ⨆ x : A, ENNReal.ofReal |f x|
/-- The full norm is the supremum plus the Hölder seminorm. -/
def boundedHolderNorm (δ : ℝ≥0) (A : Set X) (f : X → ℝ) : ℝ≥0∞ :=
  holderSup A f + holderSemi δ A f
end RothschildStein.H2

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Examples.Example_945eb5fd6af8e3691449_HolderLinear ====
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
omit [MeasurableSpace X] [BorelSpace X] in
/-- Absolute homogeneity of the auxiliary Hölder norm. -/
theorem boundedHolderNorm_smul {δ : ℝ≥0} {U : Set X} (c : ℝ) (f : X → ℝ) :
    boundedHolderNorm δ U (c • f) = ENNReal.ofReal |c| * boundedHolderNorm δ U f := by
  unfold boundedHolderNorm holderSup holderSemi
  have hs : (⨆ x : U, ENNReal.ofReal |(c • f) x|) =
      ENNReal.ofReal |c| * ⨆ x : U, ENNReal.ofReal |f x| := by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
    rw [ENNReal.mul_iSup]
  rw [hs]
  have hh : eHolderNorm δ (fun x : U => (c • f) x) =
      ENNReal.ofReal |c| * eHolderNorm δ (fun x : U => f x) := by
    have he := eHolderNorm_smul (r := δ) (f := fun x : U => f x) c
    rw [← ENNReal.ofReal_coe_nnreal] at he
    have hfun : (fun x : U => (c • f) x) = c • (fun x : U => f x) := by
      funext x
      rfl
    rw [hfun]
    simpa only [coe_nnnorm, Real.norm_eq_abs] using he
  rw [hh, mul_add]
end RothschildStein.H2
