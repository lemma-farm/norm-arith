module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.Basic.Inner
@[expose] public section
/-!
# Positive spectral truncation and square domination

A selected positive spectral lift uses the original orthonormal eigenbasis,
retaining the positive part of each selected eigenvalue. Its square is bounded
by the square of the original Hermitian matrix in the positive semidefinite
order. For graph adjacency matrices this yields the degree-diagonal bound
used in the low-degree transfer argument.
-/
namespace KKPAsymptotic
open Matrix Unitary
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : Matrix V V ℝ}
theorem spectralConjugate_trace (hA : A.IsHermitian) (d : V → ℝ) :
    (conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary (diagonal d)).trace = ∑ i, d i := by
  rw [conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, trace_diagonal]
end KKPAsymptotic
