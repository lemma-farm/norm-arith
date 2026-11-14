import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

-- ==== Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vc49f6ac0ca69.GraphMatrices.Walsh ====
section
/-! Exact Walsh orthogonality for all finite independent uniform sign assignments.
These are finite sums, not an assumed probabilistic moment formula. -/
namespace GraphMatrices.Walsh
open scoped symmDiff
variable {E : Type*} [Fintype E] [DecidableEq E]
def sign (b : Bool) : ℝ := if b then 1 else -1

def character (S : Finset E) (σ : E → Bool) : ℝ :=
  ∏ i, if i ∈ S then sign (σ i) else 1
@[simp] axiom character_empty (σ : E → Bool) : character ∅ σ = 1

/-- A finite Walsh expansion, with an explicit finite set of coefficients. -/
def polynomial (I : Finset (Finset E)) (c : Finset E → ℝ) (σ : E → Bool) : ℝ :=
  ∑ S ∈ I, c S * character S σ

end GraphMatrices.Walsh

end

-- ==== Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vc49f6ac0ca69.GraphMatrices.FiniteProbability ====
section
/-
Ported on 2026-09-06 from F:/Lean2/SparseFockFormal/FiniteProbability.lean.
Original source SHA256: DD4DC454139C756000138340CDB135EA7DB4E898BBE9296D9DD3BF1EFBB034F1
Reused from the user's prior SparseFock formalization. Namespace and imports
are adapted to this project; proof bodies are retained. These are generic
finite-law/moment tools, not a verification of a graph-matrix application.
-/
/-!
# Elementary probability on finite types

This file supplies a small, explicit probability foundation for the finite
random objects in the sparse-Fock argument.  A `FiniteLaw α` is a nonnegative
real weight on the finite type `α` whose total mass is one.  Expectations and
event probabilities are finite sums, so none of the results below hide
measurability, integrability, or independence hypotheses.

The main construction is `FiniteLaw.independentProduct`.  Its outcome is a
function `x : ι → α`, and its mass is the literal product of the coordinate
masses.  The coordinate marginal, separated-observable factorization, and
cylinder-event factorization theorems therefore give genuine mutual
independence of the coordinates.
-/
open scoped BigOperators
namespace GraphMatrices
noncomputable section
/-- A probability law on a finite type, represented by explicit real weights. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  /-- Probability mass of an outcome. -/
  weight : α → ℝ
  /-- Every outcome has nonnegative mass. -/
  weight_nonneg : ∀ x, 0 ≤ weight x
  /-- The total mass is one. -/
  sum_weight : ∑ x, weight x = 1
namespace FiniteLaw
variable {α β ι κ : Type*}
section Basic
variable [Fintype α]
/-- The expectation of a real-valued observable under a finite law. -/
def expect (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

@[simp] axiom expect_const (μ : FiniteLaw α) (c : ℝ) :
    μ.expect (fun _ => c) = c

axiom expect_nonneg (μ : FiniteLaw α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ μ.expect f

end Basic
section IndependentProduct
variable [Fintype ι] [DecidableEq ι] [Fintype α]
/-- Product law with independent coordinates.  The joint mass is definitionally
the product of the individual coordinate masses. -/
def independentProduct (μ : ι → FiniteLaw α) : FiniteLaw (ι → α) where
  weight x := ∏ i, (μ i).weight (x i)
  weight_nonneg x := Finset.prod_nonneg fun i _hi => (μ i).weight_nonneg (x i)
  sum_weight := by
    rw [← Fintype.prod_sum]
    simp only [(μ _).sum_weight, Finset.prod_const_one]

end IndependentProduct
end FiniteLaw
end
end GraphMatrices

end

-- ==== Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vc49f6ac0ca69.GraphMatrices.SignGraphDegree ====
section
/-! Actual coordinate-degree bounds for injective sign graph matrices.
The primitive coordinates are unordered pairs; diagonal coordinates are unused. -/
namespace GraphMatrices
noncomputable section
variable {n r s : ℕ}
def fairBitLaw : FiniteLaw Bool where
  weight _ := 1 / 2
  weight_nonneg _ := by norm_num
  sum_weight := by norm_num
/-- Full independent signs, encoded by independent fair bits on unordered pairs. -/
def independentSignLaw {E : Type*} [Fintype E] [DecidableEq E] : FiniteLaw (E → Bool) :=
  FiniteLaw.independentProduct (fun _ => fairBitLaw)

variable {α : Type*} [Fintype α] [DecidableEq α]



end
end GraphMatrices

end

-- ==== Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vc49f6ac0ca69.GraphMatrices.FinitePaleyZygmund ====
section
/-! Finite probability inequalities used in the lower-bound argument. -/
namespace GraphMatrices.FiniteLaw
noncomputable section
open scoped BigOperators
variable {α : Type*} [Fintype α]
axiom expect_mul_sq_le (μ : FiniteLaw α) (f g : α → ℝ) :
    (μ.expect (fun x => f x * g x)) ^ 2 ≤
      μ.expect (fun x => f x ^ 2) * μ.expect (fun x => g x ^ 2)
end
end GraphMatrices.FiniteLaw

end

-- ==== Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Examples.Example_1afd72c35a9df69508cb_WalshFourthMoment ====
namespace GraphMatrices.Walsh
noncomputable section
open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

def series (D : Finset E) (c : Finset E → ℝ) (σ : E → Bool) : ℝ :=
  polynomial D.powerset c σ
def weightedEnergy (D : Finset E) (c : Finset E → ℝ) : ℝ :=
  ∑ S ∈ D.powerset, (3 : ℝ)^S.card * (c S)^2
axiom weightedEnergy_nonneg (D : Finset E) (c : Finset E → ℝ) :
    0 ≤ weightedEnergy D c

axiom weightedEnergy_insert (D : Finset E) (c : Finset E → ℝ)
    (x : E) (hx : x ∉ D) :
    weightedEnergy (insert x D) c = weightedEnergy D c +
      3 * weightedEnergy D (fun S => c (insert x S))

axiom expect_fourth_split (D : Finset E) (c : Finset E → ℝ)
    (x : E) (hx : x ∉ D) :
    independentSignLaw.expect (fun σ => (series (insert x D) c σ)^4) =
      independentSignLaw.expect (fun σ => (series D c σ)^4) +
      6 * independentSignLaw.expect (fun σ =>
        (series D c σ)^2 * (series D (fun S => c (insert x S)) σ)^2) +
      independentSignLaw.expect (fun σ => (series D (fun S => c (insert x S)) σ)^4)
/-- Finite Boolean hypercontractivity in its weighted coefficient form. -/
theorem fourth_le_weightedEnergy_sq (D : Finset E) (c : Finset E → ℝ) :
    independentSignLaw.expect (fun σ => (series D c σ)^4) ≤ (weightedEnergy D c)^2 := by
  induction D using Finset.induction_on generalizing c with
  | empty => simp [series, polynomial, character_empty, weightedEnergy, ← pow_mul]
  | @insert x D hx ih =>
    let a := series D c
    let b := series D (fun S => c (insert x S))
    let A := weightedEnergy D c
    let B := weightedEnergy D (fun S => c (insert x S))
    have hA : 0 ≤ A := weightedEnergy_nonneg _ _
    have hB : 0 ≤ B := weightedEnergy_nonneg _ _
    have ha : independentSignLaw.expect (fun σ => a σ^4) ≤ A^2 := ih c
    have hb : independentSignLaw.expect (fun σ => b σ^4) ≤ B^2 := ih _
    have hcross : independentSignLaw.expect (fun σ => a σ^2*b σ^2) ≤ A*B := by
      have hcs := FiniteLaw.expect_mul_sq_le independentSignLaw
        (fun σ => a σ^2) (fun σ => b σ^2)
      have h4 (z : ℝ) : (z^2)^2 = z^4 := by ring
      simp only [h4] at hcs
      have han : 0 ≤ independentSignLaw.expect (fun σ => a σ^4) :=
        FiniteLaw.expect_nonneg _ (fun _ => by positivity)
      have hbn : 0 ≤ independentSignLaw.expect (fun σ => b σ^4) :=
        FiniteLaw.expect_nonneg _ (fun _ => by positivity)
      have hp := mul_le_mul ha hb hbn (sq_nonneg A)
      have hAB := mul_nonneg hA hB
      nlinarith [sq_nonneg (independentSignLaw.expect (fun σ => a σ^2*b σ^2) - A*B)]
    rw [expect_fourth_split D c x hx, weightedEnergy_insert D c x hx]
    change independentSignLaw.expect (fun σ => a σ^4) +
      6*independentSignLaw.expect (fun σ => a σ^2*b σ^2) +
      independentSignLaw.expect (fun σ => b σ^4) ≤ (A+3*B)^2
    nlinarith [sq_nonneg B]
end
end GraphMatrices.Walsh
