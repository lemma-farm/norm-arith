module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.ContinuedFractions.Translations
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Data.List.Range
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Analysis.Complex.TaylorSeries

-- ==== Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Cardinal.Strong.RationalArctan ====
public section
@[expose] public section
/-! Executable rational arctangent values with uniform certified precision.
Every value below is a finite rational calculation; its error against the
ACTUAL arctangent is proved rather than supplied by an approximation oracle.
-/
namespace MeyerGeneralProblem.StrongParity
/-- The literal finite rational left endpoint quadrature. -/
def rationalArctanQuadrature (q : ℚ) (N : ℕ) : ℚ :=
  q / N * ∑ i ∈ Finset.range N, 1 / (1 + (q / N * i) ^ 2)
/-- A definite positive grid size, scaling precision by the actual numerator. -/
def rationalArctanGridSize (q : ℚ) (p : ℕ) : ℕ := (q.num.natAbs + 1) * 2 ^ p
/-- The executable rational arctangent approximation at binary precision `p`. -/
def rationalArctanApprox (q : ℚ) (p : ℕ) : ℚ :=
  rationalArctanQuadrature q (rationalArctanGridSize q p)
noncomputable section

end
end MeyerGeneralProblem.StrongParity

end
end

-- ==== Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Cardinal.Strong.RationalPi ====
public section
@[expose] public section
/-! Executable rational pi intervals from the ACTUAL arctangent evaluator. -/
namespace MeyerGeneralProblem.StrongParity
/-- A finite rational approximation to pi at the requested binary precision. -/
def rationalPiApprox (p : ℕ) : ℚ := 4 * rationalArctanApprox 1 (p + 2)
noncomputable section

end
end MeyerGeneralProblem.StrongParity

end
end

-- ==== Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Examples.Example_c2332fb9fdcafb118461_RationalUnitPhaseNames ====
@[expose] public section
/-! Ordinary unit-phase names with a size bound computed from the input name
itself. No supplied real-size or phase-accuracy certificate is used by the program. -/
namespace MeyerGeneralProblem.StrongParity
/-- Integer size budget read from the zero-precision rational input. -/
def rationalRealNameSize (name : ℕ → ℚ) : ℕ := ⌈|name 0|⌉₊ + 1
noncomputable section


set_option linter.unusedVariables false in
/-- The actual angle error includes BOTH the computed input and pi approximations. -/
theorem rationalNamedUnitPhase_angle_error (name : ℕ → ℚ) {x : ℝ}
    (hname : ∀ p, |(name p : ℝ) - x| ≤ 1 / (2 : ℝ) ^ p) (p : ℕ) 
    (h_MeyerGeneralProblem_StrongParity_rationalPiApprox_error : ∀ (p : ℕ), |(↑(MeyerGeneralProblem.StrongParity.rationalPiApprox p) : ℝ) - Real.pi| ≤ 1 / 2 ^ p)
    (h_MeyerGeneralProblem_StrongParity_rationalRealNameSize_bound : ∀ (name : ℕ → ℚ) {x : ℝ},
      (∀ (p : ℕ), |(↑(name p) : ℝ) - x| ≤ 1 / 2 ^ p) →
        |x| ≤ (↑(MeyerGeneralProblem.StrongParity.rationalRealNameSize name) : ℝ))
    (h_MeyerGeneralProblem_StrongParity_rationalPiApprox_abs_le_five : ∀ (p : ℕ), |(↑(MeyerGeneralProblem.StrongParity.rationalPiApprox p) : ℝ)| ≤ 5)
    :
    |((2 * rationalPiApprox p * name p : ℚ) : ℝ) - 2 * Real.pi * x| ≤
      ((2 * (5 + rationalRealNameSize name) : ℕ) : ℝ) * (1 / (2 : ℝ) ^ p) := by
  have heq : ((2 * rationalPiApprox p * name p : ℚ) : ℝ) - 2 * Real.pi * x =
      2 * ((rationalPiApprox p : ℝ) * ((name p : ℝ) - x) +
        ((rationalPiApprox p : ℝ) - Real.pi) * x) := by push_cast; ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsum : |(rationalPiApprox p : ℝ) * ((name p : ℝ) - x) +
      ((rationalPiApprox p : ℝ) - Real.pi) * x| ≤
      5 * (1 / (2 : ℝ) ^ p) + (1 / (2 : ℝ) ^ p) * (rationalRealNameSize name : ℝ) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul (h_MeyerGeneralProblem_StrongParity_rationalPiApprox_abs_le_five p) (hname p) (abs_nonneg _) (by norm_num))
      (mul_le_mul (h_MeyerGeneralProblem_StrongParity_rationalPiApprox_error p) (h_MeyerGeneralProblem_StrongParity_rationalRealNameSize_bound name hname)
        (abs_nonneg _) (by positivity))
  calc
    _ ≤ 2 * (5 * (1 / (2 : ℝ) ^ p) +
      (1 / (2 : ℝ) ^ p) * (rationalRealNameSize name : ℝ)) := by linarith
    _ = _ := by push_cast; ring
end
end MeyerGeneralProblem.StrongParity
