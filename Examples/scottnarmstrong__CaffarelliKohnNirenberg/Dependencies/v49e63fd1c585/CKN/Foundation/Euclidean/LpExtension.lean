-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.RieszSecondOperator
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN
/- The dense domain consists of `L^p` classes which also have an `L²`
   representative. -/
structure LpExtensionInput (p : ℝ≥0∞) (C : ℝ) where
  T : (Vec3 → ℝ) → Vec3 → ℝ
  measurable : ∀ {f : Vec3 → ℝ}, MemLp f (2 : ℝ≥0∞) volume → Measurable (T f)
  output_mem : ∀ {f : Vec3 → ℝ}, MemLp f p volume →
    MemLp f (2 : ℝ≥0∞) volume →
    MemLp (T f) p volume
  congr_ae : ∀ {f g : Vec3 → ℝ}, MemLp f (2 : ℝ≥0∞) volume →
    MemLp g (2 : ℝ≥0∞) volume → f =ᵐ[volume] g → T f =ᵐ[volume] T g
  add_ae : ∀ {f g : Vec3 → ℝ}, MemLp f (2 : ℝ≥0∞) volume →
    MemLp g (2 : ℝ≥0∞) volume → T (f + g) =ᵐ[volume] T f + T g
  smul_ae : ∀ (c : ℝ) {f : Vec3 → ℝ}, MemLp f (2 : ℝ≥0∞) volume →
    T (c • f) =ᵐ[volume] c • T f
  bound : ∀ {f : Vec3 → ℝ} (hf : MemLp f p volume)
    (hf₂ : MemLp f (2 : ℝ≥0∞) volume),
    ‖(output_mem hf hf₂).toLp (T f)‖ ≤
      C * ‖hf.toLp f‖
end CKN.Foundation.Euclidean
