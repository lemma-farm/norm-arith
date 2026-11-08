module

public import Mathlib

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

       
                                                                                       
                                     

       
                                                                                             
                                       

       
                                                  
                                                             
                                                    

                                                                 
                                                                                       
                             

/-- Sine and cosine are positive on `(0, π / 2)`. -/
theorem sin_cos_pos_of_mem_quarter {t : ℝ} (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin t ∧ 0 < Real.cos t :=
  ⟨Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos]),
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩⟩

end AmbidextrousSofa
