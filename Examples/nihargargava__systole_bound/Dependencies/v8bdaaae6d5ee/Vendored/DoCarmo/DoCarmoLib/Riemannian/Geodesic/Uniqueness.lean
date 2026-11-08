module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Geodesic/Uniqueness.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream options and proof-preserving API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Equation
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Existence
public import Mathlib
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain upstream typeclass binders; this new linter changes no proof checks.
set_option linter.overlappingInstances false
/-!
# Local uniqueness of geodesics via Picard-Lindelöf / Gronwall

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, two local integral curves
of the chart-fixed geodesic vector field that agree at a base time `t₀`
agree on a neighbourhood of `t₀`. This is a direct lift of Mathlib's

* `isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless`
  (`Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean`),

specialised to the chart-fixed geodesic vector field
`geodesicVectorFieldChart g α`, whose `C^∞`-smoothness on
`(chartAt H α).source` is recorded in
`DifferentialGeometry/Geometry/Geodesic/Equation.lean`.

We then transfer the result to base curves on `M` via projection, and
package the conclusion at the `IsGeodesicAt`-predicate level. The key
observation is that the predicate `IsGeodesicAt g γ t₀` already exposes a
lift `f : ℝ → TangentBundle I M` projecting to `γ`; uniqueness of `f` in
the chart-fixed vector field hence projects to uniqueness of `γ` on a
neighbourhood of `t₀`.

The natural matching condition for two geodesics is "same initial tangent
vector" — i.e. the lifts `f₁, f₂` agree at `t₀` as points of
`TangentBundle I M`. This encodes both `γ₁ t₀ = γ₂ t₀` and a matching of
velocity vectors in `T_{γ t₀} M`.

The chart basepoint `α` is fixed once and for all in the predicate
`IsGeodesicAt`; comparison of geodesics produced from *different* chart
basepoints is a separate question (it asks whether two different
chart-Christoffel ODEs share solutions through a common initial point —
true on the chart overlap, but the natural statement is at the level of
the moving-chart geodesic equation).
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
section ChartFixedUniqueness
variable [I.Boundaryless]
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Uniqueness of integral curves of the chart-fixed geodesic vector
field.** Two `IsMIntegralCurveAt` witnesses `f₁, f₂` for the chart-fixed
geodesic vector field `geodesicVectorFieldChart g α` at `t₀` that agree
at `t₀` agree on a neighbourhood of `t₀`, provided the common base point
`(f₁ t₀).proj = (f₂ t₀).proj` lies in the chart-α source (so the vector
field is smooth there). -/
theorem isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
    {g : RiemannianMetric I M} {α : M} {t₀ : ℝ}
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hα_src : (f₁ t₀).proj ∈ (chartAt H α).source)
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g α) t₀)
    (hf₂ : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart (I := I) g α) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    f₁ =ᶠ[𝓝 t₀] f₂ := by
  have hsmooth_inf :
      ContMDiffAt I.tangent I.tangent.tangent ∞
        (fun p : TangentBundle I M =>
          (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
            TangentBundle I.tangent (TangentBundle I M)))
        (f₁ t₀) :=
    geodesicVectorFieldChart_contMDiffAt (I := I) g α
      (p₀ := f₁ t₀) hα_src
  have hsmooth1 :
      ContMDiffAt I.tangent I.tangent.tangent 1
        (fun p : TangentBundle I M =>
          (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
            TangentBundle I.tangent (TangentBundle I M)))
        (f₁ t₀) :=
    hsmooth_inf.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact
    isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorFieldChart (I := I) g α)
      (γ := f₁) (γ' := f₂) (t₀ := t₀)
      hsmooth1 hf₁ hf₂ h0
end ChartFixedUniqueness
section GeodesicUniqueness
variable [I.Boundaryless]
end GeodesicUniqueness
end Geodesic
end Riemannian
end
