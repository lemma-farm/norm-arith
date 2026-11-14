module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Dimension.Constructions

-- ==== Examples.macgregor_sudo__compact_albert_recognition.Dependencies.v99f681f20ee2.Glennie.Native ====
public section
/- Formalization of the compact real Albert model. -/
@[expose] public section
open scoped BigOperators Quaternion
namespace Glennie
noncomputable section
set_option linter.unusedVariables false in
axiom _root_.Glennie.atLeastTwoOneAddOne : (1 + 1).AtLeastTwo
attribute [instance] _root_.Glennie.atLeastTwoOneAddOne
set_option linter.unusedVariables false in
axiom _root_.Glennie.neZeroTwoAddOne : NeZero (2 + 1)
attribute [instance] _root_.Glennie.neZeroTwoAddOne
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-- The ordinary real Cayley–Dickson octonions, as two ordinary quaternions. -/
abbrev Octonion := Quaternion ℝ × Quaternion ℝ
/-- The declared compact Cayley–Dickson convention; the doubling parameter is −1. -/
def octMul (x y : Octonion) : Octonion :=
  (x.1 * y.1 - star y.2 * x.2, y.2 * x.1 + x.2 * star y.1)
def octConj (x : Octonion) : Octonion := (star x.1, -x.2)
def octRe (x : Octonion) : ℝ := x.1.re
def octScalar (r : ℝ) : Octonion := ((r : Quaternion ℝ), 0)

/-- Real diagonal and upper off-diagonal coordinates (01,02,12). -/
@[ext] structure Albert where
  d0 : ℝ
  d1 : ℝ
  d2 : ℝ
  o01 : Octonion
  o02 : Octonion
  o12 : Octonion
namespace Albert

end Albert

def toMatrix (x : Albert) : Matrix (Fin 3) (Fin 3) Octonion :=
  ![![octScalar x.d0, x.o01, x.o02],
    ![octConj x.o01, octScalar x.d1, x.o12],
    ![octConj x.o02, octConj x.o12, octScalar x.d2]]
/-- Binary matrix multiplication only; no associative matrix-algebra law is assumed. -/
def matrixMul (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    Matrix (Fin 3) (Fin 3) Octonion := fun i j => ∑ k, octMul (A i k) (B k j)
def fromMatrix (A : Matrix (Fin 3) (Fin 3) Octonion) : Albert :=
  ⟨octRe (A 0 0), octRe (A 1 1), octRe (A 2 2), A 0 1, A 0 2, A 1 2⟩
/-- Native symmetrized binary matrix product, stored in Hermitian coordinates. -/
def jordan (x y : Albert) : Albert :=
  fromMatrix ((1/2 : ℝ) • (matrixMul (toMatrix x) (toMatrix y) +
    matrixMul (toMatrix y) (toMatrix x)))
def trace (x : Albert) : ℝ := x.d0+x.d1+x.d2
def inner (x y : Albert) : ℝ := trace (jordan x y)

end
end Glennie

end
end

-- ==== Examples.macgregor_sudo__compact_albert_recognition.Dependencies.v99f681f20ee2.Glennie.Sector ====
public section
/- Fixed compact complex-sector coordinates in the declared gauge.
The hidden columns are (-extract(o12), +extract(o02), -extract(o01)). -/
@[expose] public section
namespace Glennie
noncomputable section
set_option maxHeartbeats 2000000

def complexOct (z : ℂ) : Octonion := (⟨z.re,z.im,0,0⟩,0)

def complexAlbert (a b c : ℝ) (u v w : ℂ) : Albert :=
  ⟨a,b,c,complexOct u,complexOct v,complexOct w⟩

end
end Glennie

end
end

-- ==== Examples.macgregor_sudo__compact_albert_recognition.Examples.Example_49f4ffbc77bc2a9fc1df_SectorBudgets ====
/- Native metric adapters for the sharp compact sector estimate. -/
@[expose] public section
namespace Glennie
noncomputable section


set_option linter.unusedVariables false in
theorem complex_coefficient_bound (a b c : ℝ) (u v w : ℂ) 
    (h_Glennie_complexAlbert_inner : ∀ (a b c : ℝ) (u v w : ℂ),
      Glennie.inner (Glennie.complexAlbert a b c u v w) (Glennie.complexAlbert a b c u v w) =
        a ^ 2 + b ^ 2 + c ^ 2 +
          2 * ((Complex.normSq : ℂ → ℝ) u + (Complex.normSq : ℂ → ℝ) v + (Complex.normSq : ℂ → ℝ) w))
    (h_Glennie_ScalarEstimates_amgm_three : ∀ (a b c : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ c → 27 * (a * b * c) ≤ (a + b + c) ^ 3)
    :
    216*(u*w*star v).im^2 ≤ inner (complexAlbert a b c u v w)
      (complexAlbert a b c u v w)^3 := by
  have him : (u*w*star v).im^2 ≤ Complex.normSq u*Complex.normSq v*Complex.normSq w := by
    have h := sq_nonneg (u*w*star v).re
    have hid : Complex.normSq (u*w*star v) =
        Complex.normSq u*Complex.normSq v*Complex.normSq w := by
      simp only [map_mul, Complex.star_def, Complex.normSq_conj]
      ring
    rw [Complex.normSq_apply] at hid
    nlinarith
  have ham := h_Glennie_ScalarEstimates_amgm_three (Complex.normSq u) (Complex.normSq v)
    (Complex.normSq w) (Complex.normSq_nonneg u) (Complex.normSq_nonneg v)
    (Complex.normSq_nonneg w)
  have hsum : 2*(Complex.normSq u+Complex.normSq v+Complex.normSq w) ≤
      inner (complexAlbert a b c u v w) (complexAlbert a b c u v w) := by
    rw [h_Glennie_complexAlbert_inner]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hs0 : 0 ≤ 2*(Complex.normSq u+Complex.normSq v+Complex.normSq w) := by
    exact mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (Complex.normSq_nonneg u) (Complex.normSq_nonneg v))
        (Complex.normSq_nonneg w))
  have hc := pow_le_pow_left₀ hs0 hsum 3
  nlinarith

end
end Glennie
