module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Stream.Init
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.v9848e5a487a8.Ray.Analytic.Analytic
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.v9848e5a487a8.Ray.Analytic.Uniform
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.v9848e5a487a8.Ray.Misc.Bounds
/-!
## Infinite series of analytic functions

Uniformly convergent series of analytic functions have analytic limits.
-/
open Complex
open Filter (atTop)
open Metric (ball closedBall sphere)
open scoped Real NNReal ENNReal Topology symmDiff
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type} [NormedAddCommGroup G]
variable [CompleteSpace E] [CompleteSpace G]
