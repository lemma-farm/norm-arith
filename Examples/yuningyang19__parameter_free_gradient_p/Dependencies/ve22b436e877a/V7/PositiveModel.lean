import Examples.yuningyang19__parameter_free_gradient_p.Dependencies.ve22b436e877a.V7.Foundation
namespace V7
def IsCoordinateGradient (oracle : PairOracle d) : Prop :=
  O3.IsCoordinateGradient oracle.value oracle.gradient
def MinimizerSet (oracle : PairOracle d) : Set (Point d) :=
  O3.MinimizerSet oracle.value
noncomputable def minimizerDistance (p : ℝ) (oracle : PairOracle d)
    (x0 : Point d) : ℝ :=
  O3.minimizerDistance p oracle.value x0
def IsLpSmooth (p L : ℝ) (oracle : PairOracle d) : Prop :=
  O3.IsLpSmooth p (conjugateExponent p) L oracle.gradient
/-- Proof-side objective certificate.  It is never an algorithm input. -/
structure PositiveInstance (p : ℝ) (d : ℕ) (x0 : Point d) where
  oracle : PairOracle d
  L : ℝ
  L_pos : 0 < L
  coordinateGradient : IsCoordinateGradient oracle
  convex : O3.IsConvexObjective oracle.value
  minimizerNonempty : (MinimizerSet oracle).Nonempty
  smooth : IsLpSmooth p L oracle
noncomputable def PositiveInstance.fstar (inst : PositiveInstance p d x0) : ℝ :=
  sInf (inst.oracle.value '' MinimizerSet inst.oracle)
end V7
