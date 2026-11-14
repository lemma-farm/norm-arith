module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.Basic

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.vc341c38807d2.GuthMaynard.NativeSource.GuthMaynard.VanDerCorput ====
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

noncomputable def logarithmicPhase (t x : ℝ) : ℝ := -t * Real.log x

/-! ## Finite Weyl differencing -/
noncomputable def paddedShift (a : ℤ → ℂ) (N : ℕ) (n : ℤ) (h : ℕ) : ℂ :=
  if n + h ∈ Finset.Ico (0 : ℤ) N then a (n + h) else 0
end GuthMaynard.NativeMoment

end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_78e28edc4879b584891b_Weyl ====
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
noncomputable def logarithmicDifferencePhase
    (t A : Real) (h k : Nat) (x : Real) : Real :=
  logarithmicPhase t (A + x + h) - logarithmicPhase t (A + x + k)

/-- Integer-indexed logarithmic phase term used by zero-padded shifts. -/
noncomputable def integerLogarithmicTerm (t A : Real) (n : Int) : Complex :=
  unitaryPhase (logarithmicPhase t (A + n))

/-- Explicit B-process majorant for a correlation at shift distance `r`. -/
noncomputable def logarithmicCorrelationBound
    (t A : Real) (N r : Nat) : Real :=
  let M := N - r - 1
  ((M : Real) * (4 * t * r / A ^ 3) / (2 * Real.pi) + 2) *
    (2 * Real.pi / Real.sqrt (t * r / (8 * A ^ 3)) +
      2 * (Real.sqrt (t * r / (8 * A ^ 3)) /
        (t * r / (8 * A ^ 3)) + 1))
set_option linter.unusedVariables false in
theorem padded_logarithmic_correlation_norm_le_of_lt
    (t A : Real) (N H h k : Nat) (ht : 0 < t) (hA : 0 < A)
    (hH : H <= N) (hNA : (N : Real) <= A)
    (hh : h < H) (hk : k < H) (hhk : h < k) 
    (h_GuthMaynard_NativeMoment_padded_logarithmic_correlation_eq : ∀ (t A : ℝ) (N H h k : ℕ),
      h < H →
        k < H →
          h < k →
            ∑ n ∈ Finset.Ico (-(↑H : ℤ)) (↑N : ℤ),
                Star.star
                    (GuthMaynard.NativeMoment.paddedShift
                      (GuthMaynard.NativeMoment.integerLogarithmicTerm t A) N n h) *
                  GuthMaynard.NativeMoment.paddedShift
                    (GuthMaynard.NativeMoment.integerLogarithmicTerm t A) N n k =
              Star.star
                (∑ m ∈ Finset.range (N - (k - h)),
                  GuthMaynard.NativeMoment.unitaryPhase
                    (GuthMaynard.NativeMoment.logarithmicDifferencePhase t A 0 (k - h) (↑m : ℝ))))
    (h_GuthMaynard_NativeMoment_logarithmicDifference_B_process : ∀ (t A : ℝ) (h k N : ℕ),
      0 < t →
        0 < A →
          h < k →
            (↑(N + 1 + k) : ℝ) ≤ A →
              ‖∑ n ∈ Finset.range (N + 1),
                    GuthMaynard.NativeMoment.unitaryPhase
                      (GuthMaynard.NativeMoment.logarithmicDifferencePhase t A h k (↑n : ℝ))‖ ≤
                ((↑N : ℝ) * (4 * t * (↑(k - h) : ℝ) / A ^ 3) / (2 * Real.pi) + 2) *
                  (2 * Real.pi / √(t * (↑(k - h) : ℝ) / (8 * A ^ 3)) +
                    2 * (√(t * (↑(k - h) : ℝ) / (8 * A ^ 3)) / (t * (↑(k - h) : ℝ) / (8 * A ^ 3)) + 1)))
    :
    ‖∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k‖ <=
      logarithmicCorrelationBound t A N (k - h) := by
  have hrpos : 0 < k - h := Nat.sub_pos_of_lt hhk
  have hrN : k - h < N := by omega
  let M := N - (k - h) - 1
  have hlength : M + 1 = N - (k - h) := by
    dsimp only [M]
    omega
  have hsizeNat : M + 1 + (k - h) <= N := by
    dsimp only [M]
    omega
  have hsize : ((M + 1 + (k - h) : Nat) : Real) <= A := by
    exact (Nat.cast_le.mpr hsizeNat).trans hNA
  have hB := h_GuthMaynard_NativeMoment_logarithmicDifference_B_process t A 0 (k - h) M ht hA
    (by omega) hsize
  rw [h_GuthMaynard_NativeMoment_padded_logarithmic_correlation_eq t A N H h k hh hk hhk,
    norm_star, ← hlength]
  simpa only [logarithmicCorrelationBound, M, Nat.sub_zero] using hB
end GuthMaynard.NativeMoment
