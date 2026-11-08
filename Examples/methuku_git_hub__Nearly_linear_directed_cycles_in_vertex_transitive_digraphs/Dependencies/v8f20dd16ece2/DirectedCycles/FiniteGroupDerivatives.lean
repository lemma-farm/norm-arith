module
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G]
def leftShift (g : G) (f : G → ℝ) : G → ℝ := fun x => f (g⁻¹*x)
section Finite
variable [Fintype G]
end Finite
end DirectedCycles
