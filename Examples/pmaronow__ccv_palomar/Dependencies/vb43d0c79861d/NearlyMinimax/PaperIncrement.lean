module
public import Examples.pmaronow__ccv_palomar.Dependencies.vb43d0c79861d.NearlyMinimax.PaperInverse
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
@[expose] public section
/-! Free-coordinate increment polynomials and their vector-moment structure in Lemma U5(3). -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open MvPolynomial
/-- Current and parent matrix entries together with their regression and density vector moments. -/
abbrev incrementVariables (r : ℕ) := parentInverseVariables r ⊕ (Bool × Bool × Fin r)
def currentVariableMatrix (r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (parentInverseVariables r) ℝ) :=
  fun i j => X (Sum.inl (i, j))
def parentVariableMatrix (r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (parentInverseVariables r) ℝ) :=
  fun i j => X (Sum.inr ⟨0, (i, j)⟩)
def vectorMoment (r : ℕ) (parent response : Bool) (i : Fin r) :
    MvPolynomial (incrementVariables r) ℝ := X (Sum.inr (parent, response, i))
def rawNumeratorPolynomial (r : ℕ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  rename Sum.inl (parentVariableMatrix r).det * vectorMoment r false response i -
    ∑ j, ∑ k, ∑ l,
      rename Sum.inl (currentVariableMatrix r i j) * C (T j k) *
      rename Sum.inl ((parentVariableMatrix r).adjugate k l) * vectorMoment r true response l
/-- The exact determinant-cleared numerator, affine in the formal response `y`. -/
def numeratorPolynomial (r : ℕ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (i : Fin r) :
    MvPolynomial (incrementVariables r) ℝ :=
  rawNumeratorPolynomial r T false i - C y * rawNumeratorPolynomial r T true i
def incrementEntryPolynomial (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  ∑ j, rename Sum.inl (parentInverseEntryPolynomial a b r m i j) * numeratorPolynomial r T y j
open RoughRegime.CombinedPolynomial
open scoped Matrix.Norms.L2Operator
end NearlyMinimax
