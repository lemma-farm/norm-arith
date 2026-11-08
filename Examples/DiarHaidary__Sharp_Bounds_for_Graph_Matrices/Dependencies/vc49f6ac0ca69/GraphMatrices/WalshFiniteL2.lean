import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vc49f6ac0ca69.GraphMatrices.FiniteL2
import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vc49f6ac0ca69.GraphMatrices.Walsh
import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vc49f6ac0ca69.GraphMatrices.SignGraphDegree
/-! A complete finite Walsh basis and its exact matrix-valued vacuum identity. -/
namespace GraphMatrices.Walsh
noncomputable section
open scoped BigOperators
variable {E : Type*} [Fintype E] [DecidableEq E]
theorem character_eq_prod (S : Finset E) (σ : E → Bool) :
    character S σ = ∏ i ∈ S, sign (σ i) := by
  simp [character]
end
end GraphMatrices.Walsh
