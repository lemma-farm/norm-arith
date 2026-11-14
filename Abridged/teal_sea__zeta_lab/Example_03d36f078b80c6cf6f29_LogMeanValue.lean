import Mathlib

-- ==== Examples.teal_sea__zeta_lab.Dependencies.v3bf7595bd248.ZetaLean.HigherXi ====
section
/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Kernel-checked algebra for the `URMS2-051` witness

This file formalizes the closed algebraic obligations in
`hunts/higher_xi/URMS2-051.md`:

* the rational parameter witness at bandwidth `51/100` and all of its strict
  margins;
* the logarithmic nearest-neighbour spacing bound used for frequencies
  `log n`;
* the integer multiplicity inequality behind the simple-zero lower bound;
* positivity of the exact rational downstream output.

It deliberately does **not** state `URMS2-051`.  The analytic Montgomery--
Vaughan mean-value estimate, RAMS2 cluster asymptotic, height-freezing estimate,
and contour transfer are not yet formalized in this project.  Keeping those
inputs out of the statement prevents the kernel-checked arithmetic below from
being mistaken for the analytic theorem.
-/
namespace ZetaLean.HigherXi
/-! ## The exact bandwidth witness -/
open Complex Finset
/-- A unit Fourier atom with real frequency `lambda`. -/
noncomputable def fourierAtom (lambda t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (t * lambda))
noncomputable def sharpBlockKernel (U theta : ℝ) : ℂ :=
  ∫ t in U..2 * U, fourierAtom theta t

end ZetaLean.HigherXi

end

-- ==== Examples.teal_sea__zeta_lab.Examples.Example_03d36f078b80c6cf6f29_LogMeanValue ====
/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Logarithmic-frequency mean-value bounds

The general weighted Montgomery--Vaughan inequality gives a constant multiple
of `sum n * |c n|^2` for the frequencies `log n`.  The rebuilt level-two bridge
does not need the sharp constant: an additional harmonic factor is harmless
against its strict power saving.

This file starts an elementary application-specific route.  It proves the
exact sharp-kernel bound, the logarithmic gap estimate for arbitrary positive
integers, and the weighted two-coefficient inequality that makes the final
finite double sum harmonic rather than polynomial in its cutoff.
-/
namespace ZetaLean.HigherXi
open Complex Finset
/-! ## Sharp-block kernel -/

/-! ## Logarithmic gaps -/

/-! ## Finite harmonic rows -/
/-- The real harmonic mass on the positive integers through `W`.  Keeping this
as a real finite sum avoids an irrelevant coercion through Mathlib's rational
`harmonic` while the mean-value estimate is assembled. -/
noncomputable def realHarmonicMass (W : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 W, ((k : ℝ)⁻¹)

/-! ## Triangular summation -/
/-- The endpoint-weighted square mass for a polynomial supported on
`{1, ..., W}`. -/
noncomputable def weightedCoefficientEnergy (W : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 W, (n : ℝ) * c n ^ 2

/-- The absolute lower-triangular off-diagonal mass associated with the
logarithmic frequencies `log n`. -/
noncomputable def logarithmicOffDiagonalMass (W : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 W,
    ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
      2 * |c m| * |c n| / (Real.log n - Real.log m)

/-- The absolute contribution of both orientations of every strict pair to
the exact sharp-block kernel expansion. -/
noncomputable def sharpKernelOffDiagonalMass
    (U : ℝ) (W : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 W,
    ∑ m ∈ (Finset.Icc 1 W).filter (fun m => m < n),
      2 * |c m| * |c n| *
        ‖sharpBlockKernel U (Real.log n - Real.log m)‖
set_option linter.unusedVariables false in
/-- Concrete sharp-block corollary for logarithmic frequencies.  The diagonal
is exact in `dirichletPolynomial_integral_expansion`; both off-diagonal
orientations together cost at most six harmonic masses of weighted energy. -/
theorem sharpKernelOffDiagonalMass_le
    (U : ℝ) (W : ℕ) (c : ℕ → ℝ) 
    (h_ZetaLean_HigherXi_norm_sharpBlockKernel_le_of_ne : ∀ (U theta : ℝ), theta ≠ 0 → ‖ZetaLean.HigherXi.sharpBlockKernel U theta‖ ≤ 2 / |theta|)
    (h_ZetaLean_HigherXi_logarithmicOffDiagonalMass_le : ∀ (W : ℕ) (c : ℕ → ℝ),
      ZetaLean.HigherXi.logarithmicOffDiagonalMass W c ≤
        3 * ZetaLean.HigherXi.realHarmonicMass W * ZetaLean.HigherXi.weightedCoefficientEnergy W c)
    :
    sharpKernelOffDiagonalMass U W c ≤
      6 * realHarmonicMass W * weightedCoefficientEnergy W c := by
  have hkernel :
      sharpKernelOffDiagonalMass U W c ≤ 2 * logarithmicOffDiagonalMass W c := by
    unfold sharpKernelOffDiagonalMass logarithmicOffDiagonalMass
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm hn
    have hgap_pos : 0 < Real.log n - Real.log m := by
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm.1.1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.1
      exact sub_pos.mpr
        (Real.strictMonoOn_log hmpos hnpos (by exact_mod_cast hm.2))
    have hk := h_ZetaLean_HigherXi_norm_sharpBlockKernel_le_of_ne U (Real.log n - Real.log m)
      hgap_pos.ne'
    rw [abs_of_pos hgap_pos] at hk
    have hcoeff : 0 ≤ 2 * |c m| * |c n| := by positivity
    calc
      2 * |c m| * |c n| * ‖sharpBlockKernel U (Real.log n - Real.log m)‖
          ≤ 2 * |c m| * |c n| * (2 / (Real.log n - Real.log m)) :=
        mul_le_mul_of_nonneg_left hk hcoeff
      _ = 2 * (2 * |c m| * |c n| /
          (Real.log n - Real.log m)) := by ring
  calc
    sharpKernelOffDiagonalMass U W c ≤ 2 * logarithmicOffDiagonalMass W c := hkernel
    _ ≤ 2 * (3 * realHarmonicMass W * weightedCoefficientEnergy W c) :=
      mul_le_mul_of_nonneg_left (h_ZetaLean_HigherXi_logarithmicOffDiagonalMass_le W c) (by norm_num)
    _ = 6 * realHarmonicMass W * weightedCoefficientEnergy W c := by ring
end ZetaLean.HigherXi
