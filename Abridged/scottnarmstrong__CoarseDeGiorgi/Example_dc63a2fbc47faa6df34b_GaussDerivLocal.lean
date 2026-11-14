module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Calculus.ParametricIntegral

-- ==== Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v3955459bdd7a.Homogenization.Ambient.Basic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
open scoped BigOperators
namespace Homogenization
abbrev Vec (d : ℕ) := Fin d → ℝ

def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

axiom vecNormSq_add_le {d : ℕ} (x y : Vec d) :
    vecNormSq (x + y) ≤ 2 * (vecNormSq x + vecNormSq y)

end Homogenization

end
end

-- ==== Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v3955459bdd7a.CoarseDeGiorgi.Statements.GaussianKernel ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
namespace CoarseDeGiorgi
/-- Appendix `a.besov`: for `t > 0`, the Gaussian
`G_t(x) = (4πt)^{-d/2} exp(-|x|² / (4t))`, `x ∈ ℝ^d`, with `|x|² = vecNormSq x`. -/
noncomputable def gaussianKernel {d : ℕ} (t : ℝ) (_ht : 0 < t) (x : Vec d) : ℝ :=
  (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) * Real.exp (-(vecNormSq x) / (4 * t))
end CoarseDeGiorgi

end
end

-- ==== Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v3955459bdd7a.CoarseDeGiorgi.NegSobolev.GaussianBasic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Elementary estimates for the Gaussian kernel

All distances here use `vecNormSq`, the Euclidean squared length on `Vec d`.
-/
@[expose] public section
open Homogenization MeasureTheory
open scoped BigOperators
namespace CoarseDeGiorgi.NegSobolev
axiom gaussianKernel_le_double_time {d : ℕ} (t : ℝ) (ht : 0 < t)
    (u v : Vec d) (h : vecNormSq v ≤ 2 * vecNormSq u + 2 * (d : ℝ) * t) :
    gaussianKernel t ht u ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4) *
        gaussianKernel (2 * t) (by positivity) v
end CoarseDeGiorgi.NegSobolev

end
end

-- ==== Examples.scottnarmstrong__CoarseDeGiorgi.Examples.Example_dc63a2fbc47faa6df34b_GaussDerivLocal ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Coordinate differential formulas and local domination of Gaussian derivatives. -/
@[expose] public section
open Homogenization MeasureTheory
open scoped BigOperators Topology
namespace CoarseDeGiorgi.NegSobolev
/-- A ball whose radius is the square root of the time admits one wider Gaussian
as a common integrable envelope for all shifts of its center. -/
theorem gaussDeriv_gaussian_local {d : ℕ} (s : ℝ) (hs : 0 < s)
    (x x₀ y : Vec d) (hx : ‖x - x₀‖ < Real.sqrt s) :
    gaussianKernel s hs (x - y) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4) *
        gaussianKernel (2 * s) (by positivity) (x₀ - y) := by
  apply gaussianKernel_le_double_time
  have hb : vecNormSq (x₀ - x) ≤ (d : ℝ) * s := by
    unfold vecNormSq vecDot
    have hc (i : Fin d) : (x₀ i - x i) ^ 2 ≤ s := by
      have hi := norm_le_pi_norm (x - x₀) i
      have hsq := sq_le_sq₀ (abs_nonneg ((x - x₀) i)) (Real.sqrt_nonneg s)
      have hi' : |(x - x₀) i| ≤ Real.sqrt s :=
        (show |(x - x₀) i| ≤ ‖x - x₀‖ by simpa only [Real.norm_eq_abs] using hi).trans hx.le
      have h := hsq.mpr hi'
      rw [sq_abs, Real.sq_sqrt hs.le] at h
      simpa only [Pi.sub_apply, sub_sq_comm] using h
    calc
      _ = ∑ i : Fin d, (x₀ i - x i) ^ 2 := by simp only [Pi.sub_apply, pow_two]
      _ ≤ ∑ _i : Fin d, s := Finset.sum_le_sum fun i _ => hc i
      _ = _ := by simp
  have htri := vecNormSq_add_le (x - y) (x₀ - x)
  rw [show x - y + (x₀ - x) = x₀ - y by abel] at htri
  linarith only [htri, hb]
end CoarseDeGiorgi.NegSobolev
