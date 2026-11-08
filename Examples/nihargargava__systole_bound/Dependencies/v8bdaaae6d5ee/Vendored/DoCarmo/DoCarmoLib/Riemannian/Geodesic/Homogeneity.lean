module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Geodesic/Homogeneity.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream options and proof-preserving API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.FiberScaling
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.MaximalInterval
public import Mathlib
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain upstream typeclass binders; this new linter changes no proof checks.
set_option linter.overlappingInstances false
/-!
# Homogeneity of geodesics (do Carmo Ch. 3, Lemma 2.6)

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M` modelled
on a complete inner-product space `E`, the geodesic with initial data `(p, a • v)`
is the affine time-reparametrisation of the geodesic with initial data `(p, v)`:

`γ(t, p, a • v) = γ(a t, p, v)`.

The bundle-level mechanism is the degree-2 homogeneity of the geodesic spray under
the fibre scaling `S_a := fiberScaling a` (`Geodesic/FiberScaling.lean`): if
`f : ℝ → TM` is an integral curve of the chart-fixed spray, then so is
`t ↦ S_a (f (a t))`, with initial datum scaled by `a` in the fibre.

## Main results

* `IsMIntegralCurveOn.fiberScaling_comp_mul` — the integral-curve transform: the
  fibre-scaled time-rescaled lift of a spray integral curve is again a spray
  integral curve.
* `IsGeodesicOnWithInitial.fiberScale` — the witness-level homogeneity, do Carmo's
  Lemma 2.6: if `γ` is a geodesic on `s` with initial data `(p, v)`, then
  `t ↦ γ (a t)` is a geodesic on `{t | a t ∈ s}` with initial data `(p, a • v)`.
* `MaximalGeodesicWitness.fiberScale`, `maximalGeodesicInterval_fiberScale` — the
  maximal interval scales inversely with the velocity:
  `I_max(p, a • v) = {t | a t ∈ I_max(p, v)}` for `a ≠ 0`.
* `isMIntegralCurveOn_geodesicVectorFieldChart_eqOn` — connected-propagation
  uniqueness for spray integral curves whose common foot stays in the base chart
  (the clopen argument).
* `maximalGeodesic_fiberScale` — the value-level homogeneity for the canonical
  maximal geodesic, `maximalGeodesic g p (a • v) t = maximalGeodesic g p v (a t)`,
  under the chart-validity clause that every witness with initial data
  `(p, a • v)` keeps its foot in the chart at `p` (the same proviso as
  `maximalGeodesic_structure_of_footInSource`; off the chart the chart-`p`-fixed
  spray degenerates and the canonical curve is junk-extended).
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
section IntegralCurveTransform
variable [I.Boundaryless]
end IntegralCurveTransform
section WitnessTransform
variable [I.Boundaryless]
end WitnessTransform
section ConnectedPropagation
variable [I.Boundaryless] [T2Space (TangentBundle I M)]
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Connected-propagation uniqueness for spray integral curves.** Two
integral curves of the chart-fixed geodesic vector field on an open preconnected
set `J` that agree at some `t₀ ∈ J` agree on all of `J`, provided the foot of the
first curve stays in the base chart-source throughout `J` (where the chart-fixed
spray is the genuine geodesic spray). Clopen argument: the agreement set is closed
by Hausdorffness and open by local (Picard–Lindelöf/Grönwall) uniqueness. -/
theorem isMIntegralCurveOn_geodesicVectorFieldChart_eqOn
    {g : RiemannianMetric I M} {α : M} {f₁ f₂ : ℝ → TangentBundle I M} {J : Set ℝ}
    (hJo : IsOpen J) (hJc : IsPreconnected J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (h₁ : IsMIntegralCurveOn f₁ (geodesicVectorFieldChart (I := I) g α) J)
    (h₂ : IsMIntegralCurveOn f₂ (geodesicVectorFieldChart (I := I) g α) J)
    (heq : f₁ t₀ = f₂ t₀)
    (hsrc : ∀ t ∈ J, (f₁ t).proj ∈ (chartAt H α).source) :
    Set.EqOn f₁ f₂ J := by
  classical
  haveI : PreconnectedSpace (↥J) := isPreconnected_iff_preconnectedSpace.mp hJc
  set Tsub : Set (↥J) := {t : ↥J | f₁ (t : ℝ) = f₂ (t : ℝ)} with hTsub_def
  suffices hTsub_univ : Tsub = Set.univ by
    intro t ht
    have ht_sub : (⟨t, ht⟩ : ↥J) ∈ Tsub := by
      have hu : (⟨t, ht⟩ : ↥J) ∈ (Set.univ : Set ↥J) := Set.mem_univ _
      rw [← hTsub_univ] at hu
      exact hu
    exact ht_sub
  have h0_mem : (⟨t₀, ht₀⟩ : ↥J) ∈ Tsub := heq
  have hf₁_cont : Continuous (fun t : ↥J => f₁ (t : ℝ)) :=
    continuousOn_iff_continuous_restrict.mp h₁.continuousOn
  have hf₂_cont : Continuous (fun t : ↥J => f₂ (t : ℝ)) :=
    continuousOn_iff_continuous_restrict.mp h₂.continuousOn
  have hTsub_closed : IsClosed Tsub := by
    have hdiag : IsClosed {p : TangentBundle I M × TangentBundle I M | p.1 = p.2} :=
      isClosed_diagonal
    have hpair_cont : Continuous (fun t : ↥J => (f₁ (t : ℝ), f₂ (t : ℝ))) :=
      hf₁_cont.prodMk hf₂_cont
    have hpre : Tsub = (fun t : ↥J => (f₁ (t : ℝ), f₂ (t : ℝ))) ⁻¹'
        {p : TangentBundle I M × TangentBundle I M | p.1 = p.2} := by
      ext t; rfl
    rw [hpre]
    exact hdiag.preimage hpair_cont
  have hTsub_open : IsOpen Tsub := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hfs : f₁ (s : ℝ) = f₂ (s : ℝ) := hs
    have hsrc_s : (f₁ (s : ℝ)).proj ∈ (chartAt H α).source := hsrc _ s.2
    have h₁_at : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g α)
        (s : ℝ) := h₁.isMIntegralCurveAt (hJo.mem_nhds s.2)
    have h₂_at : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart (I := I) g α)
        (s : ℝ) := h₂.isMIntegralCurveAt (hJo.mem_nhds s.2)
    have hev : f₁ =ᶠ[𝓝 (s : ℝ)] f₂ :=
      isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
        (I := I) (g := g) (α := α) (t₀ := (s : ℝ))
        (f₁ := f₁) (f₂ := f₂) hsrc_s h₁_at h₂_at hfs
    rcases Filter.eventually_iff_exists_mem.mp hev with ⟨U, hU_nhds, hU_eq⟩
    rcases mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, hV_mem⟩
    refine Filter.mem_of_superset
      (hV_open.preimage continuous_subtype_val |>.mem_nhds hV_mem) ?_
    intro u hu
    exact hU_eq _ (hVU hu)
  exact (IsClopen.eq_univ ⟨hTsub_closed, hTsub_open⟩ ⟨_, h0_mem⟩ :)
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Agreement of initial-data geodesic witnesses.** Two geodesics with
the same initial data `(p, v)` on open witness sets agree on any preconnected open
subset of the overlap containing `0`, provided the first witness keeps its foot in
the chart at `p` there. -/
theorem IsGeodesicOnWithInitial.eqOn
    {g : RiemannianMetric I M} {γ₁ γ₂ : ℝ → M} {J₁ J₂ J : Set ℝ} {p : M}
    {v : TangentSpace I p}
    (h₁ : IsGeodesicOnWithInitial (I := I) g γ₁ J₁ p v)
    (h₂ : IsGeodesicOnWithInitial (I := I) g γ₂ J₂ p v)
    (hJo : IsOpen J) (hJc : IsPreconnected J) (h0 : (0 : ℝ) ∈ J)
    (hJ₁ : J ⊆ J₁) (hJ₂ : J ⊆ J₂)
    (hsrc : ∀ t ∈ J, γ₁ t ∈ (chartAt H p).source) :
    Set.EqOn γ₁ γ₂ J := by
  obtain ⟨f₁, hproj₁, hf₁0, hint₁⟩ := h₁
  obtain ⟨f₂, hproj₂, hf₂0, hint₂⟩ := h₂
  have heq0 : f₁ 0 = f₂ 0 := by rw [hf₁0, hf₂0]
  have hsrc' : ∀ t ∈ J, (f₁ t).proj ∈ (chartAt H p).source := by
    intro t ht
    rw [hproj₁ t]
    exact hsrc t ht
  have heqf : Set.EqOn f₁ f₂ J :=
    isMIntegralCurveOn_geodesicVectorFieldChart_eqOn (I := I)
      hJo hJc h0 (hint₁.mono hJ₁) (hint₂.mono hJ₂) heq0 hsrc'
  intro t ht
  rw [← hproj₁ t, ← hproj₂ t, heqf ht]
end ConnectedPropagation
section ValueHomogeneity
variable [I.Boundaryless] [T2Space (TangentBundle I M)]
end ValueHomogeneity
end Geodesic
end Riemannian
end
