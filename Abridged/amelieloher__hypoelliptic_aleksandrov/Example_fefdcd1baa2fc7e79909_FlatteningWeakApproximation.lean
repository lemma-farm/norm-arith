module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Set.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.MetricSpace.Thickening

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v12ef8e4d3780.PDEFoundation.Ambient.Basic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Ambient carriers

The common finite-dimensional carriers used by the PDE libraries. The
inherited norm on `Vec d` is the finite-product supremum norm; Euclidean
quadratic structure is defined explicitly in `PDEFoundation.Ambient.EuclideanNorm`.
-/
@[expose] public section
namespace PDE
/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v12ef8e4d3780.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Bounded approximate identities on finite-measure regions

These analytic helpers use actual normalized smooth kernels. They are independent
of the Appendix C profile constructor and apply to measurable coefficients.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ENNReal

section Kernels
variable {G : Type*} [NormedAddCommGroup G]
/-- A smooth spatial kernel with inner radius half its specified outer radius. -/
def spatialMollifier (h : ℝ) (hh : 0 < h) : ContDiffBump (0 : G) where
  rIn := h / 2
  rOut := h
  rIn_pos := half_pos hh
  rIn_lt_rOut := half_lt_self hh
/-- A concrete family of kernels at scales `1/(n+1)`. -/
def standardMollifierSequence (n : ℕ) : ContDiffBump (0 : G) :=
  spatialMollifier (1 / ((n : ℝ) + 1)) (by positivity)
/-- The concrete kernels have radii tending to zero. -/
axiom standardMollifierSequence_rOut_tendsto :
    Tendsto (fun n => (standardMollifierSequence (G := G) n).rOut) atTop (𝓝 0)

end Kernels
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
   [Measure.IsAddHaarMeasure (volume : Measure G)]

/-- Spatial smoothing by an actual normalized bump kernel. -/
def spatialMollify (φ : ContDiffBump (0 : G)) (g : G → ℝ) : G → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] g

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v12ef8e4d3780.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Literal stationary geometry for Appendix C

The gauge uses the Euclidean squared norms, independently of the native supremum norm.
The derivative selectors below are total Frechet derivatives on the native product.
Their identification with weak jets on axes is a separate analytic step.
-/
@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
/-- Native position--velocity coordinates. -/
abbrev XV (d : ℕ) := PDE.Vec d × PDE.Vec d
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_fefdcd1baa2fc7e79909_FlatteningWeakApproximation ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Local bounds for the normalized convolutions used in the weak chain rule

The mollification API is the independently written generic M-lane API. All uses here
are of proved normalized-convolution lemmas, with their ordinary analytic hypotheses.
-/
@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter Set Metric
open scoped Convolution
/-- A local bound on the kernel sampling ball suffices for the normalized convolution bound. -/
axiom spatialMollify_norm_le_on_ball {d : ℕ} (phi : ContDiffBump (0 : XV d))
    (g : XV d → ℝ) (hg : AEStronglyMeasurable g volume) (C : ℝ) (hC : 0 ≤ C)
    (q : XV d) (hb : ∀ y ∈ ball q phi.rOut, ‖g y‖ ≤ C) :
    ‖spatialMollify phi g q‖ ≤ C
/-- Compact bounds away from zero give a uniform eventual bound on all sampled convolutions. -/
theorem spatialMollify_eventually_bounded_on_compact {d : ℕ} (g : XV d → ℝ)
    (hg : AEStronglyMeasurable g volume)
    (hb : ∀ L : Set (XV d), IsCompact L → 0 ∉ L →
      ∃ M : ℝ, ∀ q ∈ L, ‖g q‖ ≤ M)
    (K : Set (XV d)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ q ∈ K, ‖spatialMollify (standardMollifierSequence n) g q‖ ≤ C := by
  have hsub : K ⊆ ({0}ᶜ : Set (XV d)) := by
    intro q hq
    change q ≠ 0
    intro he
    exact hz (he ▸ hq)
  obtain ⟨delta, hd, hdelta⟩ := hK.exists_cthickening_subset_open
    isOpen_compl_singleton hsub
  have hL : IsCompact (cthickening delta K) := hK.cthickening
  obtain ⟨M, hM⟩ := hb (cthickening delta K) hL
    (fun hmem => (by simpa using hdelta hmem))
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  have he : ∀ᶠ n in atTop, (standardMollifierSequence (G := XV d) n).rOut < delta :=
    standardMollifierSequence_rOut_tendsto.eventually (gt_mem_nhds hd)
  filter_upwards [he] with n hn
  intro q hq
  apply spatialMollify_norm_le_on_ball _ g hg _ (le_max_right _ _) q
  intro y hy
  have hym : y ∈ cthickening delta K :=
    mem_cthickening_of_dist_le y q delta K hq ((mem_ball.mp hy).le.trans hn.le)
  exact (hM y hym).trans (le_max_left _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
