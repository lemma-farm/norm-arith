module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.Round

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vfa4e946990b7.RegularityStructures.Analysis.Parabolic.Basic ====
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
/-!
# Parabolic geometry on `ℝ⁴ = ℝ × ℝ³`

Space-time `ℝ⁴` is the product `ℝ × (Fin 3 → ℝ)`, a time coordinate and three space coordinates,
with the parabolic scaling `𝔰 = (2, 1, 1, 1)`. We measure distances with the parabolic size
`‖z‖_𝔰 = |z₀|^{1/2} + |z₁| + |z₂| + |z₃|` of [Hos25, §2.1] (`‖x‖_s = ∑ᵢ |xᵢ|^{1/sᵢ}`), which is
comparable to Hairer's `|z|_𝔰 = |z₀|^{1/2} + |z'|` [Hai14, §2], and satisfies the triangle
inequality and exact scaling `‖(c² t, c x)‖_𝔰 = c ‖(t, x)‖_𝔰`.

Sources: [Hos25] = arXiv:2310.07396v2, §2.1; [Hai14] = arXiv:1303.5113v4, §2.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- Space-time `ℝ⁴ = ℝ × ℝ³`, with time first. -/
abbrev ParabolicSpace : Type := ℝ × (Fin 3 → ℝ)

/-- The parabolic dilation `S^c z = (c² z₀, c z')`. -/
def parabolicDilate (c : ℝ) (z : ParabolicSpace) : ParabolicSpace := (c ^ 2 * z.1, c • z.2)
end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vfa4e946990b7.RegularityStructures.Analysis.Parabolic.Lattice.Bump ====
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
/-!
# One- and four-dimensional lattice bumps

`latticeBump s = σ(s) - σ(s - 1)` with `σ = Real.smoothTransition` is a smooth function with values
in `[0, 1]` supported in `[0, 2]` whose integer translates telescope to a partition of unity
(`sum_latticeBump_Icc`). Its tensor power `latticeBump4` on `ℝ × ℝ³` is the building block of the
causal lattice partition of unity used for finite-sum reconstruction (Hairer, arXiv:1303.5113v4,
proof of Prop. 7.2).
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- `b(s) = σ(s) − σ(s − 1)`, `σ = Real.smoothTransition`; supported in `(0, 2)`. -/
def latticeBump (s : ℝ) : ℝ := Real.smoothTransition s - Real.smoothTransition (s - 1)
/-- Indices of the space-time lattice `ℤ × ℤ³`. -/
abbrev LatticeIndex : Type := ℤ × (Fin 3 → ℤ)
/-- The embedding of a lattice index into `ℝ × ℝ³`. -/
def latticeCoe (k : LatticeIndex) : ParabolicSpace := ((k.1 : ℝ), fun i => (k.2 i : ℝ))
/-- The tensor-product bump on `ℝ × ℝ³`. -/
def latticeBump4 (v : ParabolicSpace) : ℝ := latticeBump v.1 * ∏ i, latticeBump (v.2 i)
end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vfa4e946990b7.RegularityStructures.Analysis.Parabolic.Lattice.Cell ====
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
/-!
# Causal lattice cells on parabolic space

`latticePoint n k = S^{2^{-n}} k` is the `k`-th point of the parabolic lattice at scale `2^{-n}`, and
`latticeCell n k` is the rescaled bump `latticeBump4 (S^{2^n} · - k)`. Its support lies in the
causal box `latticePoint n k + (0, 2·2^{-n}]^4`-type region (`latticeCell_ne_zero`), and has
parabolic radius at most `8 · 2^{-n}` around `latticePoint n k`
(`parabolicNorm_sub_latticePoint_le`).
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The lattice point `S^{2^{-n}} k` at scale `2^{-n}`. -/
def latticePoint (n : ℕ) (k : LatticeIndex) : ParabolicSpace :=
  parabolicDilate ((2 : ℝ) ^ n)⁻¹ (latticeCoe k)
/-- The lattice cell `w ↦ latticeBump4 (S^{2^n} w - k)`. -/
def latticeCell (n : ℕ) (k : LatticeIndex) (w : ParabolicSpace) : ℝ :=
  latticeBump4 (parabolicDilate ((2 : ℝ) ^ n) w - latticeCoe k)
end RegularityStructures
end
public section
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_4178805f5804b67aa8c6_LatticeAvg ====
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
/-!
# The lattice average of the model functions, and its domination

`latticeAvg 𝒯 g γ f n y = ∑_k χ_{n,k}(y) (Π_{z_{n,k}} f(z_{n,k}))(y)` is the integrand of the lattice
approximation `S_n f ψ = ∫ ψ · latticeAvg n`.  Since the cells form a causal partition of unity,
`latticeAvg` is an average of the values `G_z(y)` over the lattice points `z` at distance
`≤ 8 · 2^{-n}` in the past of `y`; for such `z` in the slab `s^2 ≤ z₀` (`s = 2^{-n}`), so
`d(y, z) ≤ 8 w_z` and the crude bound `abs_fnComb_le_of_slab` applies, giving the uniform bound
`|latticeAvg n y| ≤ identDom y` for `n ≥ 1` (`abs_latticeAvg_le`).

Source: [Hai14] = arXiv:1303.5113v4, Remark 3.15 and proof of Prop. 7.2 (lattice form).
-/
@[expose] public noncomputable section
open Set Filter
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end RegularityStructures
end
public section
namespace RegularityStructures
variable {ι : Type*} [Fintype ι] [DecidableEq ι] 


set_option linter.unusedVariables false in
theorem abs_finsum_cell_sub_le {n : ℕ} {y : ParabolicSpace} {a : LatticeIndex → ℝ} {c B : ℝ}
    (h : ∀ k, latticeCell n k y ≠ 0 → |a k - c| ≤ B) 
    (h_RegularityStructures_sum_latticeCell_eq_one : ∀ {n : ℕ} {w : RegularityStructures.ParabolicSpace} {s : Finset RegularityStructures.LatticeIndex},
      (∀ (k : RegularityStructures.LatticeIndex), RegularityStructures.latticeCell n k w ≠ 0 → k ∈ s) →
        ∑ k ∈ s, RegularityStructures.latticeCell n k w = 1)
    (h_RegularityStructures_latticeCell_nonneg : ∀ (n : ℕ) (k : RegularityStructures.LatticeIndex) (w : RegularityStructures.ParabolicSpace),
      0 ≤ RegularityStructures.latticeCell n k w)
    (h_RegularityStructures_finite_support_latticeCell : ∀ (n : ℕ) (w : RegularityStructures.ParabolicSpace),
      (Function.support fun (k : RegularityStructures.LatticeIndex) ↦
          RegularityStructures.latticeCell n k w).Finite)
    :
    |(∑ᶠ k, latticeCell n k y * a k) - c| ≤ B := by
  classical
  set s := (h_RegularityStructures_finite_support_latticeCell n y).toFinset with hsdef
  have hs : ∀ k, latticeCell n k y ≠ 0 → k ∈ s := fun k hk => by
    simpa [hsdef, Set.Finite.mem_toFinset] using hk
  have h1 : ∑ k ∈ s, latticeCell n k y = 1 := h_RegularityStructures_sum_latticeCell_eq_one hs
  have h2 : ∑ᶠ k, latticeCell n k y * a k = ∑ k ∈ s, latticeCell n k y * a k :=
    finsum_eq_sum_of_support_subset _ fun k hk => hs k (left_ne_zero_of_mul hk)
  have h3 : ∑ k ∈ s, latticeCell n k y * a k - c = ∑ k ∈ s, latticeCell n k y * (a k - c) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
  rw [h2, h3]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ s, |latticeCell n k y * (a k - c)| ≤ ∑ k ∈ s, latticeCell n k y * B := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : latticeCell n k y ≠ 0 := by
          simpa [hsdef, Set.Finite.mem_toFinset] using hk
        rw [abs_mul, abs_of_nonneg (h_RegularityStructures_latticeCell_nonneg _ _ _)]
        exact mul_le_mul_of_nonneg_left (h k hk') (h_RegularityStructures_latticeCell_nonneg _ _ _)
    _ = B := by rw [← Finset.sum_mul, h1, one_mul]
namespace Model
end Model
end RegularityStructures
