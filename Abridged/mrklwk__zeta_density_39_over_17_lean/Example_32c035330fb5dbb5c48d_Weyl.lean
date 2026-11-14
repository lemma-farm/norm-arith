module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.Basic

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v98a67904ba4b.GuthMaynard.NativeSource.GuthMaynard.VanDerCorput ====
public section
set_option autoImplicit false
@[expose] public section
open Complex Finset Set
open scoped BigOperators InnerProductSpace
namespace GuthMaynard.NativeMoment
/-!
# The logarithmic exponential sums used in the classical density argument

This file develops the two concrete van der Corput estimates needed by the
project.  Angles in `unitaryPhase` are measured in radians; this avoids a
pervasive factor `2 * pi` when the phase is `-t * log x`.
-/
/-- The standard additive character with its argument measured in radians. -/
noncomputable def unitaryPhase (x : ℝ) : ℂ := Complex.exp (Complex.I * x)

/-- The logarithmic phase occurring in `n ^ (-it)`. -/
noncomputable def logarithmicPhase (t x : ℝ) : ℝ := -t * Real.log x

/-! ## Kusmin--Landau cancellation -/

/-! ## Finite Weyl differencing -/

/-- A zero-padded translate of an integer-indexed sequence. -/
noncomputable def paddedShift (a : ℤ → ℂ) (N : ℕ) (n : ℤ) (h : ℕ) : ℂ :=
  if n + h ∈ Finset.Ico (0 : ℤ) N then a (n + h) else 0

end GuthMaynard.NativeMoment

end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_32c035330fb5dbb5c48d_Weyl ====
set_option autoImplicit false
@[expose] public section
open Complex Finset Set
open scoped BigOperators InnerProductSpace
namespace GuthMaynard.NativeMoment
/-!
# Weyl differencing for the logarithmic phase

The correlation phase below is the phase produced by one A-process shift.
Its curvature is controlled on a dyadic interval and is fed into the
multi-period B-process from `SecondDerivative.lean`.
-/
/-- Complex-correlation form of finite Weyl differencing. -/
axiom interval_weyl_differencing_complex
    (a : Int -> Complex) (N H : Nat) (C : Real)
    (ha : forall n, n ∈ Finset.Ico (0 : Int) N -> ‖a n‖ <= 1)
    (hC : 0 <= C)
    (hcorr : forall h, h ∈ Finset.range H -> forall k, k ∈ Finset.range H -> h ≠ k ->
      ‖∑ n ∈ Finset.Ico (-(H : Int)) N,
        star (paddedShift a N n h) * paddedShift a N n k‖ <= C) :
    (H : Real) ^ 2 * ‖∑ n ∈ Finset.Ico (0 : Int) N, a n‖ ^ 2 <=
      ((N + H : Nat) : Real) * ((H : Real) * N + (H : Real) ^ 2 * C)

/-- Integer-indexed logarithmic phase term used by zero-padded shifts. -/
noncomputable def integerLogarithmicTerm (t A : Real) (n : Int) : Complex :=
  unitaryPhase (logarithmicPhase t (A + n))
@[simp] axiom norm_integerLogarithmicTerm (t A : Real) (n : Int) :
    ‖integerLogarithmicTerm t A n‖ = 1

/-- Explicit B-process majorant for a correlation at shift distance `r`. -/
noncomputable def logarithmicCorrelationBound
    (t A : Real) (N r : Nat) : Real :=
  let M := N - r - 1
  ((M : Real) * (4 * t * r / A ^ 3) / (2 * Real.pi) + 2) *
    (2 * Real.pi / Real.sqrt (t * r / (8 * A ^ 3)) +
      2 * (Real.sqrt (t * r / (8 * A ^ 3)) /
        (t * r / (8 * A ^ 3)) + 1))
axiom logarithmicCorrelationBound_nonneg
    (t A : Real) (N r : Nat) (ht : 0 < t) (hA : 0 < A) :
    0 <= logarithmicCorrelationBound t A N r

/-- Symmetric natural-number distance between two shifts. -/
def shiftDistance (h k : Nat) : Nat := (h - k) + (k - h)
axiom padded_logarithmic_correlation_norm_le
    (t A : Real) (N H h k : Nat) (ht : 0 < t) (hA : 0 < A)
    (hH : H <= N) (hNA : (N : Real) <= A)
    (hh : h < H) (hk : k < H) (hne : h ≠ k) :
    ‖∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k‖ <=
      logarithmicCorrelationBound t A N (shiftDistance h k)
/-- The finite logarithmic A-process with every correlation discharged by
the proved B-process.  The correlation majorant is written as an explicit
finite sum over the possible nonzero shift distances. -/
theorem logarithmic_weyl_AB_process
    (t A : Real) (N H : Nat) (ht : 0 < t) (hA : 0 < A)
    (hH : H <= N) (hNA : (N : Real) <= A) :
    (H : Real) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : Int) N, integerLogarithmicTerm t A n‖ ^ 2 <=
      ((N + H : Nat) : Real) *
        ((H : Real) * N + (H : Real) ^ 2 *
          ∑ r ∈ Finset.Icc 1 (H - 1), logarithmicCorrelationBound t A N r) := by
  let C := ∑ r ∈ Finset.Icc 1 (H - 1), logarithmicCorrelationBound t A N r
  apply interval_weyl_differencing_complex
    (integerLogarithmicTerm t A) N H C
  · intro n _hn
    simp
  · dsimp only [C]
    exact Finset.sum_nonneg fun r _hr => logarithmicCorrelationBound_nonneg t A N r ht hA
  · intro h hh k hk hne
    have hbase := padded_logarithmic_correlation_norm_le
      t A N H h k ht hA hH hNA (Finset.mem_range.mp hh)
        (Finset.mem_range.mp hk) hne
    have hdistPos : 0 < shiftDistance h k := by
      unfold shiftDistance
      omega
    have hdistHigh : shiftDistance h k <= H - 1 := by
      unfold shiftDistance
      by_cases hle : h <= k
      · rw [Nat.sub_eq_zero_of_le hle, zero_add]
        exact (Nat.sub_le k h).trans (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk))
      · have kle : k <= h := Nat.le_of_not_ge hle
        rw [Nat.sub_eq_zero_of_le kle, add_zero]
        exact (Nat.sub_le h k).trans (Nat.le_sub_one_of_lt (Finset.mem_range.mp hh))
    have hmem : shiftDistance h k ∈ Finset.Icc 1 (H - 1) :=
      Finset.mem_Icc.mpr ⟨hdistPos, hdistHigh⟩
    exact hbase.trans (Finset.single_le_sum
      (fun r hr => logarithmicCorrelationBound_nonneg t A N r ht hA) hmem)

end GuthMaynard.NativeMoment
