module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Source-objective identities on normed vector spaces

Only bilinearity and the weak equation enter the gap identity. In particular
it applies to the concrete Sobolev graph, whose default norm is a graph norm,
without pretending that this norm is induced by an inner product.
-/

namespace SubdiffusiveProcess
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

                                                                               
                                                             
                                                       
                                     
                                                       
                                
                         
      

                                                                         
theorem bilinear_affine_energy_gap (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (u v : V) (hu : B u (v - u) = 0) :
    B v v = B u u + B (v - u) (v - u) := by
  simp only [map_sub] at hu
  simp only [map_sub, sub_apply]
  rw [hB v u]
  linarith

end SubdiffusiveProcess
