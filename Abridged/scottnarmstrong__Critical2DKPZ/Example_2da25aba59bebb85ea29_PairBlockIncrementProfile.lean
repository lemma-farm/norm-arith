module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Tactic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Int.Interval
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Site ====
public section
/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The integer lattice and its nearest-neighbour averaging operator

Sites in dimension `d` are functions `Fin d → ℤ`; the walk operator averages over
the `2d` signed coordinate directions. -/
@[expose] public section
namespace LatticeProb
/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ
/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1
/-- The sum of `u` over the neighbours of `x`, direction by direction. -/
def nbrSum {d : ℕ} (u : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))
/-- The simple random walk operator `(P u)(x) = (1/2d) ∑_{y ∼ x} u(y)`. -/
noncomputable def walkOp {d : ℕ} (u : Site d → ℝ) (x : Site d) : ℝ :=
  nbrSum u x / (2 * d)
end LatticeProb
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Walk.SRW ====
public section
/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The simple random walk kernel and its parity constraint

Iterating the nearest-neighbour averaging operator from the unit atom at the origin
gives a kernel supported inside the graph-distance ball and on the parity class of time. -/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LatticeProb
open Finset
variable {d : ℕ}
/-! ### The `ℓ¹` norm of a site -/
/-- The graph distance from the origin: the `ℓ¹` norm of a site. -/
def graphNorm {d : ℕ} (x : Site d) : ℕ := ∑ i, (x i).natAbs

/-! ### The kernel -/
/-- `P^j(0, x)`, the `j`-step transition probability of the simple random walk
started at the origin. -/
noncomputable def srwHeat (d : ℕ) : ℕ → Site d → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | j + 1 => fun x => walkOp (srwHeat d j) x

end LatticeProb
namespace LatticeProb
open Finset
/-! ### The one-dimensional nearest-neighbour recursion -/

end LatticeProb
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Walk.GaussianFourier ====
public section
/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Gaussian Fourier integrals

The complex Gaussian integral along any horizontal line equals the Gaussian density
at the integer frequency times `2π`. -/
@[expose] public section
open MeasureTheory
noncomputable section
namespace LatticeProb.ContinuousTime
/-- The Gaussian kernel of variance `s` at an integer, `(2πs)^{-1/2} e^{-k²/(2s)}`. -/
def lineGauss (s : ℝ) (k : ℤ) : ℝ :=
  (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(k : ℝ) ^ 2 / (2 * s))

/-- The product Gaussian with covariance `(t / d) I` for positive dimension and time. -/
def ctGauss (d : ℕ) (t : ℝ) (x : Site d) : ℝ := ∏ i, lineGauss (t / d) (x i)
end LatticeProb.ContinuousTime
end

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Walk.OneDim ====
public section
/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The one-dimensional lazy random walk kernel

The kernel `p_m(k) = 4^{-m} binom(2m,m+k)` describes a walk that stays put with
probability one half and moves in each direction with probability one quarter. It is
symmetric and unimodal, has total mass one, and its maximum is at most `(m+1)^{-1/2}`. -/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LatticeProb
open Finset
/-! ### Binomial coefficients with an integer lower index -/
/-- `binom n j` for an integer `j`, extended by `0` to `j < 0`.  `Nat.choose`
already vanishes for `j > n`. -/
noncomputable def binomZ (n : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j then (n.choose j.toNat : ℝ) else 0

/-! ### Total variation of the discrete gradient

Symmetry and unimodality give `∑_k |p_m(k+1) - p_m(k)| = 2 p_m(0)`. -/
end LatticeProb
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.WalkTails.Hypergeometric ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The squared-binomial walk law

The normalized squared-binomial weights form a hypergeometric law.
Through the increment `2j-m`, they describe the common endpoint of two independent simple walks
conditioned to have the same endpoint after `m` steps.
-/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.WalkTails
open Finset.Nat Finset.HasAntidiagonal
/-- The finite hypergeometric mass at `j`: the squared binomial law on
`{0, ..., m}`.  It is zero outside that interval. -/
def hypergeometricWeight (m j : ℕ) : ℝ :=
  ((Nat.choose m j : ℝ) ^ 2) / (Nat.choose (2 * m) m : ℝ)

end Critical2DKPZ.WalkTails
end

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.WalkTails.LogConcavity ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Log-concavity and finite walk-law convolution

Repeated convolution with the coefficient sequence of `1+x` gives the binomial coefficients.
Nonnegative Toeplitz minors are preserved by this convolution and imply log-concavity of the
squared-binomial laws.
-/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.WalkTails
def hypergeometricIntWeight (m : ℕ) (z : ℤ) : ℝ :=
  (LatticeProb.binomZ m z) ^ 2 / (Nat.choose (2 * m) m : ℝ)

end Critical2DKPZ.WalkTails
end

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_2da25aba59bebb85ea29_PairBlockIncrementProfile ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Local central limit estimates for pair-block increments -/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open Filter


set_option linter.unusedVariables false in
/-- The scaled squared-binomial law of one composition block has a uniform
`O(1/m)` local Gaussian error over all accessible marks. -/
theorem exists_hypergeometricWeight_localGaussian_error 
    (h_Critical2DKPZ_SHF_Moments_ctGauss_one_pair_profile : ∀ (m : ℕ),
      0 < m →
        ∀ (x : ℤ),
          √(↑m : ℝ) *
              ((2 * LatticeProb.ContinuousTime.ctGauss 1 (↑m : ℝ) ![x]) ^ 2 /
                (2 * LatticeProb.ContinuousTime.ctGauss 1 (2 * (↑m : ℝ)) ![0])) =
            2 / √Real.pi * Real.exp (-(↑x : ℝ) ^ 2 / (↑m : ℝ)))
    (h_Critical2DKPZ_SHF_Moments_ctGauss_one_scaled_bounds : ∀ (m : ℕ),
      1 ≤ m →
        ∀ (x : ℤ),
          0 ≤ √(↑m : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1 (↑m : ℝ) ![x] ∧
            √(↑m : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1 (↑m : ℝ) ![x] ≤ 2)
    (h_Critical2DKPZ_SHF_Moments_srwHeat_one_scaled_bounds : ∀ (m : ℕ),
      1 ≤ m →
        ∀ (x : ℤ),
          0 ≤ √(↑m : ℝ) * LatticeProb.srwHeat 1 m ![x] ∧ √(↑m : ℝ) * LatticeProb.srwHeat 1 m ![x] ≤ 2)
    (h_Critical2DKPZ_SHF_Moments_ctGauss_one_return_scaled : ∀ (m : ℕ),
      0 < m → √(↑m : ℝ) * (2 * LatticeProb.ContinuousTime.ctGauss 1 (2 * (↑m : ℝ)) ![0]) = (√Real.pi)⁻¹)
    (h_Critical2DKPZ_SHF_Moments_abs_sq_ratio_sub_le : ∀ {A B D E : ℝ},
      1 / 4 ≤ D →
        1 / 2 ≤ E →
          -2 ≤ A → A ≤ 2 → -2 ≤ B → B ≤ 2 → |A ^ 2 / D - B ^ 2 / E| ≤ 16 * |A - B| + 32 * |D - E|)
    (h_LatticeProb_srwHeat_one_binom : ∀ (n a b : ℕ),
      a + b = n → LatticeProb.srwHeat 1 n ![(↑a : ℤ) - (↑b : ℤ)] = (↑(n.choose a) : ℝ) / 2 ^ n)
    (h_Critical2DKPZ_WalkTails_hypergeometricIntWeight_eq_nat : ∀ (m j : ℕ),
      Critical2DKPZ.WalkTails.hypergeometricIntWeight m (↑j : ℤ) =
        Critical2DKPZ.WalkTails.hypergeometricWeight m j)
    (h_Critical2DKPZ_SHF_Moments_graphNorm_two_mul_sub_parity : ∀ (m j : ℕ), (↑(LatticeProb.graphNorm ![2 * (↑j : ℤ) - (↑m : ℤ)]) : ZMod 2) = (↑m : ZMod 2))
    (h_Critical2DKPZ_SHF_Moments_exists_srwHeat_one_scaled_parity_error : ∃ (C : ℝ),
      0 < C ∧
        ∀ (n : ℕ),
          1 ≤ n →
            ∀ (x : LatticeProb.Site 1),
              (↑(LatticeProb.graphNorm x) : ZMod 2) = (↑n : ZMod 2) →
                |√(↑n : ℝ) * LatticeProb.srwHeat 1 n x -
                      √(↑n : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1 (↑n : ℝ) x| ≤
                  C / (↑n : ℝ))
    (h_Critical2DKPZ_SHF_Moments_srwHeat_one_return_scaled_error : ∀ (C : ℝ),
      0 ≤ C →
        (∀ (n : ℕ),
            1 ≤ n →
              ∀ (x : LatticeProb.Site 1),
                (↑(LatticeProb.graphNorm x) : ZMod 2) = (↑n : ZMod 2) →
                  |√(↑n : ℝ) * LatticeProb.srwHeat 1 n x -
                        √(↑n : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1 (↑n : ℝ) x| ≤
                    C / (↑n : ℝ)) →
          ∀ (m : ℕ),
            1 ≤ m →
              |√(↑m : ℝ) * LatticeProb.srwHeat 1 (2 * m) ![0] -
                    √(↑m : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1 (2 * (↑m : ℝ)) ![0]| ≤
                C / (↑m : ℝ))
    (h_Critical2DKPZ_SHF_Moments_hypergeometricIntWeight_eq_srwHeat_sq_div_return : ∀ (m j : ℕ),
      j ≤ m →
        Critical2DKPZ.WalkTails.hypergeometricIntWeight m (↑j : ℤ) =
          LatticeProb.srwHeat 1 m ![(↑j : ℤ) - (↑(m - j) : ℤ)] ^ 2 / LatticeProb.srwHeat 1 (2 * m) ![0])
    :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ k : ℕ, k ≤ m →
        |Real.sqrt (m : ℝ) * WalkTails.hypergeometricWeight m k -
          2 / Real.sqrt Real.pi * Real.exp
            (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))| ≤ C / (m : ℝ) := by
  obtain ⟨C, hC, hlocal⟩ := h_Critical2DKPZ_SHF_Moments_exists_srwHeat_one_scaled_parity_error
  have hlarge1 : ∀ᶠ m : ℕ in atTop, 4 * C < (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (4 * C)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hlarge1
  refine ⟨48 * C, by positivity, m₀, ?_⟩
  intro m hm₀m
  have hmLarge1 : 4 * C < (m : ℝ) := hm₀ m hm₀m
  intro k hk
  have hmReal : 0 < (m : ℝ) := by linarith [hC, hmLarge1]
  have hmPos : 0 < m := by exact_mod_cast hmReal
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmPos)
  let x : ℤ := 2 * (k : ℤ) - (m : ℤ)
  let a : ℝ := LatticeProb.srwHeat 1 m ![x]
  let d : ℝ := LatticeProb.srwHeat 1 (2 * m) ![(0 : ℤ)]
  let e : ℝ := 2 * LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![(0 : ℤ)]
  let A : ℝ := Real.sqrt (m : ℝ) * a
  let B : ℝ := Real.sqrt (m : ℝ) * 2 *
    LatticeProb.ContinuousTime.ctGauss 1 (m : ℝ) ![x]
  let D : ℝ := Real.sqrt (m : ℝ) * d
  let E : ℝ := Real.sqrt (m : ℝ) * e
  have hxpar :
      ((LatticeProb.graphNorm (![x] : LatticeProb.Site 1) : ℕ) : ZMod 2) =
        ((m : ℕ) : ZMod 2) := by
    dsimp [x]
    exact h_Critical2DKPZ_SHF_Moments_graphNorm_two_mul_sub_parity m k
  have hAB : |A - B| ≤ C / (m : ℝ) := by
    simpa [A, B, a] using hlocal m hm (![x] : LatticeProb.Site 1) hxpar
  have hDE : |D - E| ≤ C / (m : ℝ) := by
    have hEq : |D - E| = |Real.sqrt (m : ℝ) *
        LatticeProb.srwHeat 1 (2 * m) ![0] -
          Real.sqrt (m : ℝ) * 2 *
            LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![0]| := by
      congr 1
      dsimp [D, E, d, e]
      ring
    rw [hEq]
    exact h_Critical2DKPZ_SHF_Moments_srwHeat_one_return_scaled_error C hC.le hlocal m hm
  have hE : E = (Real.sqrt Real.pi)⁻¹ := by
    simpa [E, e] using h_Critical2DKPZ_SHF_Moments_ctGauss_one_return_scaled m (Nat.zero_lt_of_lt hm)
  have hpiRoot : Real.sqrt Real.pi ≤ 2 := by
    calc
      Real.sqrt Real.pi ≤ Real.sqrt 4 := Real.sqrt_le_sqrt Real.pi_lt_four.le
      _ = 2 := by norm_num
  have hEhalf : 1 / 2 ≤ E := by
    rw [hE, inv_eq_one_div, div_le_div_iff₀ (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)]
    nlinarith [hpiRoot]
  have hCsmall : C / (m : ℝ) < 1 / 4 := by
    rw [div_lt_iff₀ hmReal]
    nlinarith [hmLarge1]
  have hDlow : 1 / 4 ≤ D := by
    have hlow := (abs_le.mp hDE).1
    dsimp [D]
    nlinarith [hEhalf, hCsmall]
  have hDpos : 0 < D := by linarith
  have hEpos : 0 < E := by rw [hE]; positivity
  have haBounds := h_Critical2DKPZ_SHF_Moments_srwHeat_one_scaled_bounds m hm x
  have hbBounds := h_Critical2DKPZ_SHF_Moments_ctGauss_one_scaled_bounds m hm x
  have hAlo : -2 ≤ A := by
    have : 0 ≤ A := by simpa [A, a] using haBounds.1
    linarith
  have hAhi : A ≤ 2 := by simpa [A, a] using haBounds.2
  have hBlo : -2 ≤ B := by
    have : 0 ≤ B := by simpa [B] using hbBounds.1
    linarith
  have hBhi : B ≤ 2 := by simpa [B] using hbBounds.2
  have hmass : WalkTails.hypergeometricWeight m k = a ^ 2 / d := by
    have hsite : (k : ℤ) - ((m - k : ℕ) : ℤ) = x := by
      dsimp [x]
      push_cast [Nat.cast_sub hk]
      ring
    rw [← h_Critical2DKPZ_WalkTails_hypergeometricIntWeight_eq_nat]
    rw [h_Critical2DKPZ_SHF_Moments_hypergeometricIntWeight_eq_srwHeat_sq_div_return m k hk, hsite]
  have hdpos : 0 < d := by
    have hdenEq : LatticeProb.srwHeat 1 (2 * m) ![(0 : ℤ)] =
        (Nat.choose (2 * m) m : ℝ) / 2 ^ (2 * m) := by
      have hden := h_LatticeProb_srwHeat_one_binom (2 * m) m m (by omega)
      have hsite : (m : ℤ) - (m : ℤ) = 0 := by ring
      rw [hsite] at hden
      exact hden
    have hchoose : 0 < Nat.choose (2 * m) m := Nat.choose_pos (by omega)
    dsimp [d]
    rw [hdenEq]
    exact div_pos (by exact_mod_cast hchoose) (by positivity)
  have hscaledMass : Real.sqrt (m : ℝ) * WalkTails.hypergeometricWeight m k =
      A ^ 2 / D := by
    rw [hmass]
    dsimp [A, D, a, d]
    field_simp [hmReal.ne', hdpos.ne', hDpos.ne']
  have hscaledGaussian : B ^ 2 / E =
      2 / Real.sqrt Real.pi *
        Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ)) := by
    have hprof := h_Critical2DKPZ_SHF_Moments_ctGauss_one_pair_profile m (Nat.zero_lt_of_lt hm) x
    have hsqrtmpos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmReal
    have hepos : 0 < e := by
      have hprod : 0 < Real.sqrt (m : ℝ) * e := by simpa [E] using hEpos
      exact (mul_pos_iff_of_pos_left hsqrtmpos).mp hprod
    calc
      B ^ 2 / E = Real.sqrt (m : ℝ) *
          ((2 * LatticeProb.ContinuousTime.ctGauss 1 (m : ℝ) ![x]) ^ 2 / e) := by
            dsimp [B, E, e]
            field_simp [hsqrtmpos.ne', hepos.ne']
      _ = _ := by simpa [x] using hprof
  have herr : |A ^ 2 / D - B ^ 2 / E| ≤ 48 * C / (m : ℝ) := by
    calc
      |A ^ 2 / D - B ^ 2 / E| ≤ 16 * |A - B| + 32 * |D - E| :=
        h_Critical2DKPZ_SHF_Moments_abs_sq_ratio_sub_le hDlow hEhalf hAlo hAhi hBlo hBhi
      _ ≤ 16 * (C / (m : ℝ)) + 32 * (C / (m : ℝ)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hAB (by norm_num))
          (mul_le_mul_of_nonneg_left hDE (by norm_num))
      _ = 48 * C / (m : ℝ) := by ring
  calc
    |Real.sqrt (m : ℝ) * WalkTails.hypergeometricWeight m k -
        2 / Real.sqrt Real.pi *
          Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))| =
        |A ^ 2 / D - B ^ 2 / E| := by rw [hscaledMass, hscaledGaussian]
    _ ≤ 48 * C / (m : ℝ) := herr
end Critical2DKPZ.SHF.Moments
end
