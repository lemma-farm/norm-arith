module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Geodesic/MaximalInterval.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream options and proof-preserving API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Equation
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Existence
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Uniqueness
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain upstream typeclass binders; this new linter changes no proof checks.
set_option linter.overlappingInstances false
/-!
# Maximal interval of definition for a geodesic with prescribed initial data

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, every initial datum
`(p : M, v : T_p M)` gives rise to a *maximal open interval*
`I_max(p, v) ⊆ ℝ` containing `0` on which a geodesic with that initial
datum is defined, together with a canonical curve `maximalGeodesic g p v : ℝ → M`
that realises this geodesic on `I_max(p, v)` (and is junk-valued outside).

## Main definitions

* `IsGeodesicOn g γ s`: an interval-restricted geodesic predicate; the
  set-relativised analogue of `IsGeodesic`. There exist a chart basepoint
  `α : M` and a lifted curve `f : ℝ → TangentBundle I M` projecting to
  `γ` such that `f` is an integral curve of the chart-fixed geodesic
  vector field `geodesicVectorFieldChart g α` on `s`.

* `maximalGeodesicInterval g p v`: the union of all open intervals
  containing `0` on which there exists a geodesic with `γ 0 = p` and
  velocity-lift value `v` at `0`. By construction, this is an open set
  containing `0`.

* `maximalGeodesic g p v`: a `ℝ → M`-curve obtained from
  `exists_geodesic_with_initial_velocity_at` together with a `Classical.choice` selection of a
  geodesic that covers each point of the maximal interval, junk-extended
  to the entire real line by the constant value `p` outside.

## Main theorems

* `maximalGeodesicInterval_isOpen`: openness.
* `zero_mem_maximalGeodesicInterval`: `0` is in the maximal interval.
* `maximalGeodesic_zero`: `maximalGeodesic g p v 0 = p`.
* `isGeodesicAt_maximalGeodesic`: at every `t ∈ maximalGeodesicInterval g p v`,
  the curve `maximalGeodesic g p v` is a local geodesic at `t`.

## Strategy

We follow the standard "union over local extensions" construction. The
maximal interval is the union of all open intervals `J` containing both
`0` and the point of interest on which a geodesic with the prescribed
initial condition exists. The curve `maximalGeodesic` is then defined by
picking, for each `t` in the maximal interval, the value of any such
local geodesic at `t`; the value is junk (= `p`) for `t` outside the
maximal interval. The headline geodesic predicate is established at the
pointwise `IsGeodesicAt` level, which is the regularity that the existence
theorem `exists_geodesic_with_initial_velocity_at` directly delivers. A globalised
`IsGeodesicOn` statement on the maximal interval would require integral
curves of the chart-fixed vector field to glue across chart changes; that
requires a moving-chart formulation of the geodesic equation and is
deferred.
-/
noncomputable section
open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff
namespace Riemannian
namespace Geodesic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]
/-- **Math.** `γ` is a geodesic on `s` with initial datum `(p, v)` at time `0` if
the velocity lift `f` projects to `γ`, satisfies `f 0 = ⟨p, v⟩`, and is an
integral curve of the chart-fixed geodesic vector field at the chart
basepoint `p`. The chart basepoint is fixed to be the initial point `p`,
which guarantees that the vector field is smooth at the initial data
(since `p ∈ (chartAt H p).source` is automatic). -/
def IsGeodesicOnWithInitial
    (g : RiemannianMetric I M) (γ : ℝ → M) (s : Set ℝ)
    (p : M) (v : TangentSpace I p) : Prop :=
  ∃ f : ℝ → TangentBundle I M,
    (∀ t, (f t).proj = γ t) ∧
    f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
    IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g p) s
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** `IsGeodesicOnWithInitial` is monotone in the set. -/
lemma IsGeodesicOnWithInitial.mono
    {g : RiemannianMetric I M} {γ : ℝ → M} {s s' : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (hs : s' ⊆ s) :
    IsGeodesicOnWithInitial (I := I) g γ s' p v := by
  obtain ⟨f, hproj, hf0, hf⟩ := hγ
  exact ⟨f, hproj, hf0, hf.mono hs⟩
/-- **Math.** The "membership witness" predicate for the maximal interval: at time
`t`, there exists a connected open `J ∋ 0, t` and a geodesic with initial
data `(p, v)` on `J`. Preconnectedness of `J` (i.e., `J` is an interval in
`ℝ`) is required to enable interval-propagation arguments, e.g.
identifying the witness curve with a known geodesic at every `t ∈ J` from
agreement at `t = 0`. This is packaged as a single-existential `Prop` so
that `Classical.choose` works cleanly. -/
def MaximalGeodesicWitness
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : Prop :=
  ∃ γ : ℝ → M, ∃ J : Set ℝ,
    IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v
/-- **Math.** The maximal interval of definition of a geodesic with initial data
`(p, v)`: the set of times `t : ℝ` admitting an open interval `J ∋ 0, t`
on which a geodesic with initial data `(p, v)` is defined. -/
def maximalGeodesicInterval
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    Set ℝ :=
  {t : ℝ | MaximalGeodesicWitness (I := I) g p v t}
section LocalExistence
end LocalExistence
section MaximalGeodesicDefinition
/-- **Math.** A local geodesic witness at time `t`, taken via `Classical.choose`
when `t ∈ maximalGeodesicInterval g p v`. -/
def maximalGeodesicChosenCurve
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : MaximalGeodesicWitness (I := I) g p v t) :
    ℝ → M :=
  Classical.choose h
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma maximalGeodesicChosenCurve_spec
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : MaximalGeodesicWitness (I := I) g p v t) :
    ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g
        (maximalGeodesicChosenCurve (I := I) g p v h) J p v :=
  Classical.choose_spec h
/-- **Math.** The canonical maximal geodesic with initial data `(p, v)`. On the
maximal interval, it equals some local geodesic with the prescribed
initial data, chosen by `Classical.choose`; outside, it is the constant
`p`. -/
def maximalGeodesic
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : M :=
  letI : Decidable (MaximalGeodesicWitness (I := I) g p v t) := Classical.dec _
  if h : MaximalGeodesicWitness (I := I) g p v t then
    maximalGeodesicChosenCurve (I := I) g p v h t
  else p
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** On the maximal interval, `maximalGeodesic g p v` equals the chosen
local geodesic. -/
lemma maximalGeodesic_of_mem
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    maximalGeodesic (I := I) g p v t =
      maximalGeodesicChosenCurve (I := I) g p v h t := by
  unfold maximalGeodesic
  letI : Decidable (MaximalGeodesicWitness (I := I) g p v t) := Classical.dec _
  exact dif_pos h
end MaximalGeodesicDefinition
section MaximalGeodesicValue
end MaximalGeodesicValue
section MaximalGeodesicAtTime
end MaximalGeodesicAtTime
section MaximalGeodesicMain
end MaximalGeodesicMain
end Geodesic
end Riemannian
end
