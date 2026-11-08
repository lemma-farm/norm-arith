module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Exponential/StrictDerivative.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream package-option restoration, and
proof-preserving calculus API compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.UniformExistence
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.FlowDependence
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Exponential.Ray
public import Mathlib
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain the upstream overlapping finite-dimensional instance binders.
set_option linter.overlappingInstances false
/-!
# Strict differentiability of the exponential map at the origin

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 2.9: `d(exp_p)_0 = id`, and
`exp_p` is a local diffeomorphism at `0`. This file proves the strict-derivative
form of that statement and its topological consequences:

* `fderiv_geodesicSprayCoord_equilibrium` — the linearization of the coordinate
  geodesic spray `F(x, w) = (w, -Γ_p(w, w)(x))` at the zero-section point is the
  two-step nilpotent map `A(u, w) = (w, 0)`: the Christoffel term is quadratic
  in the velocity, so it does not contribute to the derivative at `w = 0`.
* `exists_hasStrictFDerivAt_extChartAt_expMap` — **`exp_p` is strictly
  differentiable at `0` with derivative the identity**, read in the chart at
  `p`; moreover a ball around `0` lies in the exponential domain and its image
  stays in the chart. The proof composes the C¹-dependence-on-initial-conditions
  theorem (`hasStrictFDerivAt_of_picardResidual`, applied to the spray at its
  equilibrium over a short time `T` with `T‖A‖ < 1`) with the geodesic
  homogeneity `γ(1, p, w) = γ(T, p, w/T)` (realized by fibre scaling of the
  flow witness), which trades the fixed evaluation time `1` for the short
  Picard–Lindelöf time `T`. The derivative is computed exactly: since
  `A ∘ A = 0` the Neumann series terminates.
* `map_expMap_nhds` — `exp_p` maps neighbourhoods of `0 ∈ T_pM` exactly onto
  neighbourhoods of `p`: normal-neighbourhood existence at the topological
  level.
* `exists_injOn_expMap` — `exp_p` is injective on a small ball around `0`.

The full `C^∞`-diffeomorphism statement of do Carmo's Proposition 2.9 requires
`C^k` dependence of the geodesic flow on initial conditions and remains open;
the strict-derivative and local-homeomorphism content is complete here.
-/
noncomputable section
open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal
namespace Riemannian
namespace Exponential
open Riemannian.Geodesic Riemannian.FlowDependence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The two-step nilpotent linearization `A(u, w) = (w, 0)` of the geodesic
spray squares to zero. -/
lemma sprayLinearization_comp_self :
    (((ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E)).comp
      ((ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E)))
      = (0 : E × E →L[ℝ] E × E) := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp
omit [T2Space (TangentBundle I M)] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **The linearization of the geodesic spray at the zero section.** At the
equilibrium `(φ_p(p), 0)`, the derivative of `F(x, w) = (w, -Γ_p(w, w)(x))` is the
nilpotent map `A(u, w) = (w, 0)`: the Christoffel contraction is quadratic in `w`,
so its derivative vanishes at `w = 0` (do Carmo Ch. 3, the computation behind
`d(exp_p)_0 = id` in Prop. 2.9). -/
lemma fderiv_geodesicSprayCoord_equilibrium (g : RiemannianMetric I M) (p : M) :
    fderiv ℝ (fun ζ : E × E => geodesicSprayCoord (I := I) g p ζ.1 ζ.2)
        ((extChartAt I p p, (0 : E)) : E × E)
      = (ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E) := by
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set F : E × E → E × E := fun ζ => geodesicSprayCoord (I := I) g p ζ.1 ζ.2
  have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  have hmem : z₀ ∈ (extChartAt I p).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target p, mem_univ _⟩
  have hFs : ContDiffOn ℝ ∞ F ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    contDiffOn_geodesicSprayCoord_prod (I := I) g p
  have hFd : HasFDerivAt F (fderiv ℝ F z₀) z₀ :=
    ((hFs.contDiffAt (hopen.mem_nhds hmem)).differentiableAt
      (by simp)).hasFDerivAt
  refine ContinuousLinearMap.ext fun q => ?_
  obtain ⟨u, w⟩ := q
  -- the straight line through the equilibrium in direction `(u, w)`
  set c : ℝ → E × E := fun t => z₀ + t • ((u, w) : E × E) with hcdef
  have hline : HasDerivAt c ((u, w) : E × E) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • ((u, w) : E × E))
        ((1 : ℝ) • ((u, w) : E × E)) 0 := (hasDerivAt_id 0).smul_const _
    simpa [hcdef, one_smul] using h1.const_add z₀
  -- derivative of `F ∘ c` via the chain rule
  have hchain : HasDerivAt (fun t => F (c t)) (fderiv ℝ F z₀ ((u, w) : E × E)) 0 := by
    have hc0 : c 0 = z₀ := by simp [hcdef]
    have hFd' : HasFDerivAt F (fderiv ℝ F z₀) (c 0) := by rw [hc0]; exact hFd
    exact hFd'.comp_hasDerivAt 0 hline
  -- direct computation of the same derivative
  have hcval : ∀ t : ℝ, F (c t) =
      ((t • w : E),
        -((t * t) • chartChristoffelContraction (I := I) g p w w
          (extChartAt I p p + t • u))) := by
    intro t
    have hc1 : (c t).1 = extChartAt I p p + t • u := by
      simp [hcdef, hz₀def, Prod.smul_def]
    have hc2 : (c t).2 = t • w := by
      simp [hcdef, hz₀def, Prod.smul_def]
    show geodesicSprayCoord (I := I) g p (c t).1 (c t).2 = _
    rw [hc1, hc2, geodesicSprayCoord_def,
      chartChristoffelContraction_smul_smul (I := I) g p t w _]
  -- the quadratic coefficient is differentiable in the base slot near `0`
  have hGdiff : DifferentiableAt ℝ
      (fun t : ℝ => chartChristoffelContraction (I := I) g p w w
        (extChartAt I p p + t • u)) 0 := by
    have hslice : DifferentiableAt ℝ
        (fun y : E => chartChristoffelContraction (I := I) g p w w y)
        (extChartAt I p p) := by
      have hmem' : ((extChartAt I p p, w) : E × E) ∈
          (extChartAt I p).target ×ˢ (univ : Set E) :=
        ⟨mem_extChartAt_target p, mem_univ _⟩
      have hF1 : DifferentiableAt ℝ F ((extChartAt I p p, w) : E × E) :=
        (hFs.contDiffAt (hopen.mem_nhds hmem')).differentiableAt (by simp)
      have hin : DifferentiableAt ℝ (fun y : E => ((y, w) : E × E))
          (extChartAt I p p) :=
        differentiableAt_id.prodMk (differentiableAt_const w)
      have hyd : DifferentiableAt ℝ (fun y : E => F (y, w)) (extChartAt I p p) := by
        have h := hF1.comp (extChartAt I p p) hin
        exact h
      have hval : (fun y : E => chartChristoffelContraction (I := I) g p w w y)
          = fun y : E => -((F (y, w)).2) := by
        funext y
        show chartChristoffelContraction (I := I) g p w w y =
          -(geodesicSprayCoord (I := I) g p y w).2
        rw [geodesicSprayCoord_def]
        simp
      rw [hval]
      exact (differentiableAt_snd.comp _ hyd).neg
    have hin2 : DifferentiableAt ℝ (fun t : ℝ => extChartAt I p p + t • u) 0 :=
      (differentiableAt_const _).add (differentiableAt_id.smul_const u)
    have hslice' : DifferentiableAt ℝ
        (fun y : E => chartChristoffelContraction (I := I) g p w w y)
        (extChartAt I p p + (0 : ℝ) • u) := by
      simpa using hslice
    have h := hslice'.comp 0 hin2
    exact h
  -- product rule: `t² • G(t)` has derivative `0` at `t = 0`
  have hdirect : HasDerivAt (fun t => F (c t)) ((w, 0) : E × E) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t • w : E)) w 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have hsq : HasDerivAt (fun t : ℝ => t * t) 0 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).fun_mul (hasDerivAt_id (0 : ℝ))
    have h2 : HasDerivAt (fun t : ℝ =>
        (t * t) • chartChristoffelContraction (I := I) g p w w
          (extChartAt I p p + t • u)) 0 0 := by
      simpa using hsq.fun_smul hGdiff.hasDerivAt
    have h2' : HasDerivAt (fun t : ℝ =>
        -((t * t) • chartChristoffelContraction (I := I) g p w w
          (extChartAt I p p + t • u))) 0 0 := by
      simpa using h2.fun_neg
    have hpair := h1.prodMk h2'
    exact hpair.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => hcval t)
  -- uniqueness of the derivative identifies the two computations
  have huniq := hchain.unique hdirect
  rw [huniq]
  simp
-- The implicit-function argument times out at 250000 heartbeats; 300000 is sufficient.
end Exponential
end Riemannian
