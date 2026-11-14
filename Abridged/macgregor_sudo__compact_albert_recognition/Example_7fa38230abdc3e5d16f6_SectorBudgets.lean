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

-- ==== Examples.macgregor_sudo__compact_albert_recognition.Dependencies.vfa707d235d8f.Glennie.Native ====
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

-- ==== Examples.macgregor_sudo__compact_albert_recognition.Dependencies.vfa707d235d8f.Glennie.Sector ====
public section
/- Fixed compact complex-sector coordinates in the declared gauge.
The hidden columns are (-extract(o12), +extract(o02), -extract(o01)). -/
@[expose] public section
namespace Glennie
noncomputable section
set_option maxHeartbeats 2000000
def complexPart (x : Octonion) : ℂ := ⟨x.1.re,x.1.imI⟩
def complexOct (z : ℂ) : Octonion := (⟨z.re,z.im,0,0⟩,0)
/-- The last imaginary coordinate has the sign i(jℓ)=−kℓ. -/
def hiddenColumn (x : Octonion) : Fin 3 → ℂ :=
  ![⟨x.1.imJ,x.1.imK⟩,⟨x.2.re,x.2.imI⟩,⟨x.2.imJ,-x.2.imK⟩]

def hiddenMatrix (z : Albert) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i => ![-hiddenColumn z.o12 i, hiddenColumn z.o02 i, -hiddenColumn z.o01 i]

def complexProjection (z : Albert) : Albert :=
  ⟨z.d0,z.d1,z.d2,complexOct (complexPart z.o01),
    complexOct (complexPart z.o02),complexOct (complexPart z.o12)⟩

def sectorFrobeniusSq (M : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

end
end Glennie

end
end

-- ==== Examples.macgregor_sudo__compact_albert_recognition.Examples.Example_7fa38230abdc3e5d16f6_SectorBudgets ====
/- Native metric adapters for the sharp compact sector estimate. -/
@[expose] public section
namespace Glennie
noncomputable section


set_option linter.unusedVariables false in
theorem hidden_energy_le (z : Albert) 
    (h_Glennie_inner_self_nonneg : ∀ (x : Glennie.Albert), 0 ≤ Glennie.inner x x)
    (h_Glennie_inner_hidden_decomposition : ∀ (z : Glennie.Albert),
      Glennie.inner z z =
        Glennie.inner (Glennie.complexProjection z) (Glennie.complexProjection z) +
          2 * Glennie.sectorFrobeniusSq (Glennie.hiddenMatrix z))
    :
    2*sectorFrobeniusSq (hiddenMatrix z) ≤ inner z z := by
  rw [h_Glennie_inner_hidden_decomposition]
  linarith [h_Glennie_inner_self_nonneg (complexProjection z)]
end
end Glennie
