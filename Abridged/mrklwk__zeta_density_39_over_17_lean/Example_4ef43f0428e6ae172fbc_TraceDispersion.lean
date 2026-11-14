module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Finset.Prod
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Order.Chebyshev

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_4ef43f0428e6ae172fbc_TraceDispersion ====
set_option autoImplicit false
@[expose] public section
open Finset
open scoped BigOperators
namespace GuthMaynard.NativeMoment
/-!
# Sixth-moment trace dispersion

The first lemma is the nonnegativity assertion needed for the sixth root in
Guth--Maynard Lemma 4.2.  It is a direct finite Jensen inequality, proved here
over the reals before the spectral specialization.
-/
theorem sixthMoment_dispersion_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (hs : s.Nonempty) :
    0 ≤ (∑ i ∈ s, x i ^ 6) -
      (∑ i ∈ s, x i ^ 2) ^ 3 / (s.card : ℝ) ^ 2 := by
  have hJensen := pow_sum_le_card_mul_sum_pow
    (s := s) (f := fun i => x i ^ 2) (fun i hi => sq_nonneg (x i)) 2
  have hcard : 0 < (s.card : ℝ) ^ 2 := by
    positivity
  have hpow : ∑ i ∈ s, (x i ^ 2) ^ 3 = ∑ i ∈ s, x i ^ 6 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [sub_nonneg]
  rw [div_le_iff₀ hcard]
  rw [hpow] at hJensen
  simpa only [mul_comm] using hJensen
end GuthMaynard.NativeMoment
