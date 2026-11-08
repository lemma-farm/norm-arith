module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Analytic.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Data.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Tactic.Cases
import Mathlib.Topology.Basic
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Misc.Bounds
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Misc.Multilinear
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Misc.Topology
/-!
## Facts about analytic functions (general field case)
-/
open Classical
open Filter (atTop)
open Function (curry uncurry)
open Metric (ball closedBall sphere isOpen_ball)
open Set (univ)
open scoped ContDiff Real NNReal ENNReal Topology
noncomputable section
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
/-- Drop 'Within' from `AnalyticWithinAt` if we have a neighborhood -/
public lemma AnalyticWithinAt.analyticAt {f : E → F} {s : Set E} {x : E}
    (fa : AnalyticWithinAt 𝕜 f s x) (xs : s ∈ 𝓝 x) : AnalyticAt 𝕜 f x := by
  obtain ⟨p, r, fp⟩ := fa
  obtain ⟨e, e0, es⟩ := Metric.mem_nhds_iff.mp xs
  refine ⟨p, min r (.ofReal e),
    {r_le := by simp [fp.r_le], r_pos := by simp [fp.r_pos, e0], hasSum := fun {y} yr ↦ ?_}⟩
  simp only [Metric.mem_eball, edist_zero_right, lt_inf_iff] at yr
  obtain ⟨yr, ye⟩ := yr
  simp only [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff e0] at ye
  exact fp.hasSum (.inr (es (by simp [ye]))) (by simp [yr])
/-- Extract `AnalyticAt` from `ContDiffOn 𝕜 ω` if we have a neighborhood -/
public lemma ContDiffOn.analyticAt {f : E → F} {s : Set E} (fa : ContDiffOn 𝕜 ω f s) {x : E}
    (xs : s ∈ 𝓝 x) : AnalyticAt 𝕜 f x :=
  (fa x (mem_of_mem_nhds xs)).analyticWithinAt.analyticAt xs
