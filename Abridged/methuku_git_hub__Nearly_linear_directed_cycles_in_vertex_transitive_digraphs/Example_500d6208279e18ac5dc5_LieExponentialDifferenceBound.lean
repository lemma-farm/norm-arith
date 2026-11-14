module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v72d1ee4af233.DirectedCycles.LieOneParameterExistence ====
public section
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]
include hLie in
/-- Every identity-coordinate tangent of a smooth real Lie group is realized
by an actual global smooth one-parameter subgroup. The curve is constructed
from a local ODE and then extended by finite subdivisions. -/
axiom lie_group_exists_one_parameter (v : E) :
    ∃ φ : ℝ → G, φ 0 = 1 ∧ (∀ s t : ℝ, φ (s+t) = φ s*φ t) ∧
      ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ φ ∧
      HasDerivAt (fun t => (chartAt E (1 : G)) (φ t)-(chartAt E (1 : G)) 1) v 0
end DirectedCycles

end
end

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v72d1ee4af233.DirectedCycles.LieExponentialCurve ====
public section
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]
/-- The constructed one-parameter subgroup with a prescribed coordinate
identity tangent. Uniqueness is proved separately, so the choice is immaterial. -/
noncomputable def lieOneParameter (v : E) : ℝ → G :=
  Classical.choose (lie_group_exists_one_parameter (G := G) v)

/-- The actual Lie exponential in identity-chart tangent coordinates. -/
noncomputable def lieExponential (v : E) : G := lieOneParameter v 1

end DirectedCycles

end
end

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v72d1ee4af233.DirectedCycles.LieExponentialProductCoordinates ====
public section
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]
include hLie in
/-- Actual exponential coordinates have a local multiplication with addition
derivative. Only the proved strict derivative and local inverse are used;
full smooth dependence of the exponential on its tangent is unnecessary. -/
axiom lie_exponential_product_coordinates :
    ∃ ν : E × E → E, ν (0,0) = 0 ∧
      HasFDerivAt ν (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (0,0) ∧
      ∀ᶠ p : E × E in 𝓝 (0,0), lieExponential (G := G) (ν p) =
        lieExponential p.1*lieExponential p.2

end DirectedCycles

end
end

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v72d1ee4af233.DirectedCycles.LieExponentialSymmetry ====
public section
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
open scoped Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]
axiom lieExponential_neg (v : E) :
    lieExponential (G := G) (-v) = (lieExponential v)⁻¹

end DirectedCycles

end
end

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Examples.Example_500d6208279e18ac5dc5_LieExponentialDifferenceBound ====
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ,E) ∞ G]
/-- The actual group difference of nearby exponential values has the
additive difference coordinate plus an arbitrarily small first-order error. -/
theorem lie_exponential_difference_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ x y : E, ‖x‖ < R → ‖y‖ < R →
      ∃ z : E, ‖z‖ ≤ ‖y-x‖+ε*(‖x‖+‖y‖) ∧
        lieExponential (G := G) z = (lieExponential x)⁻¹*lieExponential y := by
  obtain ⟨ν,hν0,hν,heq⟩ := lie_exponential_product_coordinates (G := G) (E := E)
  have he := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hν).bound hε
  have he' : ∀ᶠ p : E × E in 𝓝 (0,0), ‖ν p-(p.1+p.2)‖ ≤ ε*‖p‖ := by
    filter_upwards [he] with p hp
    change ‖ν ((0 : E × E)+p)-ν (0,0)-(p.1+p.2)‖ ≤ ε*‖p‖ at hp
    simpa only [zero_add,hν0,sub_zero] using hp
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (he'.and heq)
  refine ⟨R,hR,?_⟩
  intro x y hx hy
  have hp : (-x,y) ∈ Metric.ball (0,0) R := by
    simp only [Metric.mem_ball,Prod.dist_eq,dist_zero_right,norm_neg]
    exact max_lt hx hy
  obtain ⟨hb,he⟩ := hball hp
  have hb' : ‖ν (-x,y)-(y-x)‖ ≤ ε*‖(-x,y)‖ := by simpa only [sub_eq_add_neg,add_comm] using hb
  have hpn : ‖(-x,y)‖ ≤ ‖x‖+‖y‖ := by
    simp only [Prod.norm_def,norm_neg]
    exact max_le (le_add_of_nonneg_right (norm_nonneg y)) (le_add_of_nonneg_left (norm_nonneg x))
  refine ⟨ν (-x,y),?_,?_⟩
  · have ht := norm_le_insert' (ν (-x,y)) (y-x)
    have hm := mul_le_mul_of_nonneg_left hpn hε.le
    linarith
  · simpa only [lieExponential_neg] using he
end DirectedCycles
