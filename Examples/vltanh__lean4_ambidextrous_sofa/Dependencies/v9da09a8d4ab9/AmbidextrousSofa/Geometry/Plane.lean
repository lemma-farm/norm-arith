module
public import Mathlib
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Coordinate plane and the two unit corridors

The plane is represented by a pair of real coordinates, with its product
topology and product Lebesgue measure. The product norm is not the Euclidean
norm. Rotations are therefore defined by their coordinate formula.

The lower corridor is the union of the incoming horizontal arm and the
downward outgoing arm. The upper corridor is its reflection in `y = 1 / 2`.
-/
noncomputable section
namespace AmbidextrousSofa
abbrev Plane := ℝ × ℝ
/-- Counterclockwise rotation in Euclidean coordinates. -/
def rotate (θ : ℝ) (p : Plane) : Plane :=
  (Real.cos θ * p.1 - Real.sin θ * p.2,
    Real.sin θ * p.1 + Real.cos θ * p.2)
/-- A proper rigid placement: rotate, then translate. -/
def rigidMap (θ : ℝ) (v p : Plane) : Plane := rotate θ p + v
def unitStrip : Set Plane := {p | 0 ≤ p.2 ∧ p.2 ≤ 1}
def incomingArm : Set Plane := {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}
def lowerOutgoingArm : Set Plane := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}
def upperOutgoingArm : Set Plane := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2}
def lowerHall : Set Plane := incomingArm ∪ lowerOutgoingArm
def upperHall : Set Plane := incomingArm ∪ upperOutgoingArm
end AmbidextrousSofa
