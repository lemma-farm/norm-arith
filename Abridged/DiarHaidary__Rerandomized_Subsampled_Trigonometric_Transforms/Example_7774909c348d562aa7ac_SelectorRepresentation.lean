import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Matrix.Kronecker

-- ==== Examples.DiarHaidary__Rerandomized_Subsampled_Trigonometric_Transforms.Dependencies.v82da0885e94e.SRHT.PositiveSelector ====
section
/-! Positive hard-core selector creation.  All norms are genuine Hilbert
operator norms; effects need not commute. -/
open scoped BigOperators InnerProduct
namespace SRHT.PositiveSelector
noncomputable section
variable {J H : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
local notation "⟪" x ", " y "⟫" => @inner ℝ H _ x y

/-- The genuine selector Hilbert space, including a zero extension above q. -/
abbrev Space (J H : Type*) [Fintype J] := PiLp 2 (fun _ : Finset J => H)

section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open scoped Matrix.Norms.L2Operator

end Matrix
end
end SRHT.PositiveSelector

end

-- ==== Examples.DiarHaidary__Rerandomized_Subsampled_Trigonometric_Transforms.Examples.Example_7774909c348d562aa7ac_SelectorRepresentation ====
/-! Concrete matrix representation of the positive-selector operator.
The matrix index is `ι × Finset J`: the effect coordinate precedes the
selector subset. -/
namespace SRHT.SelectorRepresentation
open SRHT.PositiveSelector
open scoped BigOperators InnerProduct Matrix.Norms.L2Operator
noncomputable section

variable {J ι : Type*} [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι]
def regroup : EuclideanSpace ℝ (ι × Finset J) ≃ₗᵢ[ℝ] Space J (EuclideanSpace ℝ ι) where
  toFun f := WithLp.toLp 2 fun S => WithLp.toLp 2 fun i => f (i,S)
  invFun f := WithLp.toLp 2 fun z => f z.2 z.1
  left_inv f := by ext z; rfl
  right_inv f := by ext S i; rfl
  map_add' f g := by ext S i; rfl
  map_smul' c f := by ext S i; rfl
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [PiLp.norm_sq_eq_of_L2]
    change (∑ S : Finset J, ∑ i : ι, ‖f (i,S)‖ ^ 2) = ∑ z : ι × Finset J, ‖f z‖ ^ 2
    rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- The concrete star algebra isomorphism between selector Hilbert operators
and matrices on the coordinate/subset product basis. -/
def matrixRepresentation :
    (Space J (EuclideanSpace ℝ ι) →L[ℝ] Space J (EuclideanSpace ℝ ι)) ≃⋆ₐ[ℝ]
      Matrix (ι × Finset J) (ι × Finset J) ℝ :=
  regroup.symm.conjStarAlgEquiv.trans (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm

theorem norm_matrixRepresentation (K : Space J (EuclideanSpace ℝ ι) →L[ℝ] Space J (EuclideanSpace ℝ ι)) :
    ‖matrixRepresentation K‖ = ‖K‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  change ‖Matrix.toEuclideanCLM (n := ι × Finset J) (𝕜 := ℝ)
    ((Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (regroup.symm.conjStarAlgEquiv K))‖ = _
  rw [StarAlgEquiv.apply_symm_apply]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    change ‖regroup.symm (K (regroup f))‖ ≤ ‖K‖ * ‖f‖
    rw [LinearIsometryEquiv.norm_map]
    simpa only [LinearIsometryEquiv.norm_map] using ContinuousLinearMap.le_opNorm K (regroup f)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    have h := ContinuousLinearMap.le_opNorm (regroup.symm.conjStarAlgEquiv K) (regroup.symm f)
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.norm_map] using h

end
end SRHT.SelectorRepresentation
