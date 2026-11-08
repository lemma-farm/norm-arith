import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic
import Examples.DiarHaidary__Sharp_Bounds_for_Graph_Matrices.Dependencies.vc00133292587.GraphMatrices.CrossedEdges
/-!
# Explicit Euclidean operator norms

The norm below is defined through continuous linear maps of Euclidean spaces.
It never uses an unqualified/default norm on matrices.
-/
namespace GraphMatrices
noncomputable section
open scoped BigOperators RealInnerProductSpace
open WithLp
variable {m n k p q : Type*}
variable [Fintype m] [Fintype n] [Fintype k] [Fintype p] [Fintype q]
variable [DecidableEq n] [DecidableEq k] [DecidableEq p] [DecidableEq q]
variable [DecidableEq m]
end
end GraphMatrices
