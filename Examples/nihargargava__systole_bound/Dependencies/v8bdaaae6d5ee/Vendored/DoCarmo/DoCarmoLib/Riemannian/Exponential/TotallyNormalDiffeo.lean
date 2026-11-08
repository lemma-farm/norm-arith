module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Exponential/TotallyNormalDiffeo.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes and upstream package-option restoration.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Exponential.TotallyNormal
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.FlowReadback
public import Mathlib
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain the upstream overlapping finite-dimensional instance binders.
set_option linter.overlappingInstances false
/-!
# Totally normal neighborhoods: the C¹-diffeomorphism clause (do Carmo Ch. 3, Theorem 3.7)

`exists_totallyNormal_neighborhood` (`TotallyNormal.lean`) provides the
existence, uniqueness and covering content of do Carmo's Theorem 3.7: a
neighborhood `W ∋ p` and a uniform radius `δ` such that any two points of `W`
are joined by a geodesic segment with a unique chart-velocity parameter in the
`δ`-ball. This file closes the remaining clause of do Carmo's literal
statement — *`exp_q` is a diffeomorphism on `B_δ(0)`* — at the `C¹` level, by
proving that the pair map `G(y, w) = (y, (Z(y, w/T) T)₁)` (do Carmo's
`F(q, v) = (q, exp_q v)` read in the chart at `p`) is a `C¹` diffeomorphism of
a product ball onto an open set:

* `uniform_flow_pairMap_agree` — **two uniform local flows compute the same
  pair map**: the time-`T`-rescaled endpoint `(Z(y, w/T) T)₁` does not depend
  on the flow package `(r, ε, T, Z)`. Both flow segments are continuous
  intrinsic geodesics through `φ_p⁻¹(y)` with chart velocity `w`
  (`isGeodesicOn_uniform_flow_segment_Ioo`), so intrinsic uniqueness
  identifies them (`IsGeodesicOn.eq_uniform_flow_readback`); evaluating at
  time `1` and using injectivity of `φ_p⁻¹` on the chart target equates the
  endpoints. This transports the center derivative computed for one flow
  package (`exists_pairMap_hasStrictFDerivAt`) to the `C¹` package
  (`exists_pairMap_contDiffOn`), which produce *different* flow witnesses.
* `exists_pairMap_hasStrictFDerivAt_equiv_ball` — **the derivative of the pair
  map is invertible at every point of a ball around the zero section** (the
  pair-map analogue of `lem:dc-ch3-2-9-invertible`,
  `exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball`): a single flow
  package carrying the flow clauses, `C¹` regularity of `G` on the admissible
  set, the strict derivative at the center — the unipotent shear
  `(a, b) ↦ (a, a + b)` — and, at every point of a ball around the center, a
  strict derivative realized by a continuous linear *equivalence*: the
  derivative map is continuous on the admissible set and equals the invertible
  shear at the center, so nearby it is the Neumann-series perturbation
  `shear ∘ (1 - t)`, `t = shear⁻¹ ∘ (shear - dG_x)`, `‖t‖ < 1`.
* `exists_totallyNormal_c1_diffeo` — **totally normal neighborhoods with the
  `C¹`-diffeomorphism clause** (do Carmo Ch. 3, Theorem 3.7, complete at `C¹`
  regularity): all clauses of `exists_totallyNormal_neighborhood` (normal
  balls at every center of `W`, covering with unique parameter), and moreover
  on the product ball `B = B_{δ₁}(φ_p(p)) × B_δ(0)` the pair map `G` is `C¹`
  and injective, its image is open, and there is a two-sided inverse `Ginv`
  which is `C¹` on that image — the inverse function theorem
  (`HasStrictFDerivAt.toOpenPartialHomeomorph` at the center for the global
  injectivity, `HasStrictFDerivAt.to_local_left_inverse` at each point for the
  regularity of the inverse). The joining parameter of the covering clause is
  computed by `Ginv`: `w = (Ginv(φ_p(q), φ_p(m)))₂` — the differentiable
  dependence of the joining geodesic on its endpoints (do Carmo's Remark 3.8).
  Slicing at a fixed base point `y = φ_p(q)` exhibits `exp_q` as a `C¹`
  diffeomorphism of the uniform velocity ball `B_δ(0)` onto an open set, for
  every `q ∈ W` simultaneously.
-/
noncomputable section
open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal
namespace Riemannian
namespace Exponential
open Riemannian.Geodesic Riemannian.FlowDependence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
/-- **Math.** **Two uniform local flows of the chart-`p` spray compute the same
pair-map endpoint.** If `(r, ε, T, Z)` and `(r', ε', T', Z')` are two uniform
flow packages at `p` (each solving the spray ODE on its time interval with
chart confinement), then for any initial data `(y, w)` admissible for both,
`(Z(y, T⁻¹ • w) T)₁ = (Z'(y, T'⁻¹ • w) T')₁`.

Both time-rescaled flow segments are continuous intrinsic geodesics on an open
window containing `[0, 1]`, starting at `φ_p⁻¹(y)` with chart-`p` velocity `w`
(`isGeodesicOn_uniform_flow_segment_Ioo`); intrinsic uniqueness identifies the
first with the second (`IsGeodesicOn.eq_uniform_flow_readback`), and
evaluating at time `1` — which lies in the overlap window since `T < ε` and
`T' < ε'` — equates the chart readings via injectivity of `φ_p⁻¹` on the chart
target. -/
theorem uniform_flow_pairMap_agree
    (g : RiemannianMetric I M) (p : M) {r ε T r' ε' T' : ℝ}
    {Z Z' : E × E → ℝ → E × E}
    (hT : 0 < T) (hTε : T < ε) (hT' : 0 < T') (hT'ε' : T' < ε')
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    (hflow' : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r',
      Z' z 0 = z ∧
      (∀ t ∈ Icc (-ε') ε', HasDerivWithinAt (Z' z)
        (geodesicSprayCoord (I := I) g p (Z' z t).1 (Z' z t).2) (Icc (-ε') ε') t) ∧
      (∀ t ∈ Icc (-ε') ε', Z' z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    {y w : E}
    (hmem : ((y, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r)
    (hmem' : ((y, T'⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r') :
    (Z ((y, T⁻¹ • w) : E × E) T).1 = (Z' ((y, T'⁻¹ • w) : E × E) T').1 := by
  obtain ⟨hstart, hcont, hgeo, -, hvel0, -⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hT hTε hflow hmem
  have hεT : 0 < ε / T := div_pos (hT.trans hTε) hT
  have hε'T' : 0 < ε' / T' := div_pos (hT'.trans hT'ε') hT'
  have hEq := IsGeodesicOn.eq_uniform_flow_readback (p := p)
    hgeo hT' hT'ε' hflow' hmem' hεT hcont hstart hvel0
  -- `1` lies in the overlap window since `T < ε` and `T' < ε'`
  have h1T : (1 : ℝ) < ε / T := (one_lt_div hT).mpr hTε
  have h1T' : (1 : ℝ) < ε' / T' := (one_lt_div hT').mpr hT'ε'
  have h1mem : (1 : ℝ) ∈
      Ioo (-(min (ε / T) (ε' / T'))) (min (ε / T) (ε' / T')) := by
    constructor
    · have h0 : (0 : ℝ) < min (ε / T) (ε' / T') := lt_min hεT hε'T'
      linarith
    · exact lt_min h1T h1T'
  have h1 : (extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (1 * T)).1) =
      (extChartAt I p).symm ((Z' ((y, T'⁻¹ • w) : E × E) (1 * T')).1) :=
    hEq h1mem
  rw [one_mul, one_mul] at h1
  -- both endpoint readings lie in the chart target, where `φ_p⁻¹` is injective
  have hTIcc : T ∈ Icc (-ε) ε := ⟨by linarith, hTε.le⟩
  have hT'Icc : T' ∈ Icc (-ε') ε' := ⟨by linarith, hT'ε'.le⟩
  have htgt : (Z ((y, T⁻¹ • w) : E × E) T).1 ∈ (extChartAt I p).target :=
    ((hflow _ hmem).2.2 T hTIcc).1
  have htgt' : (Z' ((y, T'⁻¹ • w) : E × E) T').1 ∈ (extChartAt I p).target :=
    ((hflow' _ hmem').2.2 T' hT'Icc).1
  exact (extChartAt I p).symm.injOn htgt htgt' h1
omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **The derivative of the pair map is invertible at every point of a
ball around the zero section** (do Carmo Ch. 3, proof of Theorem 3.7; the
pair-map analogue of the invertibility clause `lem:dc-ch3-2-9-invertible`).
There are a flow package `(r, ε, T, Z)` and a radius `ρ > 0` such that:

* the flow clauses hold on the closed `r`-ball around the zero section;
* the pair map fixes the center: `(Z(φ_p(p), 0) T)₁ = φ_p(p)`;
* the `ρ`-ball around the center is admissible: `(x₁, T⁻¹ • x₂)` lies in the
  open flow ball for every `x` in it;
* the pair map `G(y, w) = (y, (Z(y, T⁻¹ • w) T)₁)` is `C¹` on the open set of
  admissible points;
* `G` is strictly differentiable at the center `(φ_p(p), 0)` with derivative
  the unipotent shear `(a, b) ↦ (a, a + b)`;
* at *every* point of the `ρ`-ball around the center, `G` has a strict Fréchet
  derivative realized by a continuous linear *equivalence*.

The center derivative is transported from
`exists_pairMap_hasStrictFDerivAt` — whose flow witness differs — via
`uniform_flow_pairMap_agree`; the derivative map of the `C¹` package
(`exists_pairMap_contDiffOn`) is continuous on the admissible set, so near the
center it stays within Neumann range of the invertible shear:
`dG_x = shear ∘ (1 - t)` with `t = shear⁻¹ ∘ (shear - dG_x)`, `‖t‖ < 1`. -/
theorem exists_pairMap_hasStrictFDerivAt_equiv_ball
    (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T ρ : ℝ) (Z : E × E → ℝ → E × E),
      0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧ 0 < ρ ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      (Z ((extChartAt I p p, (0 : E)) : E × E) T).1 = extChartAt I p p ∧
      (∀ x ∈ ball ((extChartAt I p p, (0 : E)) : E × E) ρ,
        ((x.1, T⁻¹ • x.2) : E × E) ∈
          ball ((extChartAt I p p, (0 : E)) : E × E) r) ∧
      ContDiffOn ℝ 1
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        {x : E × E | ((x.1, T⁻¹ • x.2) : E × E) ∈
          ball ((extChartAt I p p, (0 : E)) : E × E) r} ∧
      HasStrictFDerivAt
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        ((ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
        ((extChartAt I p p, (0 : E)) : E × E) ∧
      (∀ x ∈ ball ((extChartAt I p p, (0 : E)) : E × E) ρ,
        ∃ D' : (E × E) ≃L[ℝ] E × E,
          HasStrictFDerivAt
            (fun x' : E × E => ((x'.1 : E), (Z ((x'.1, T⁻¹ • x'.2) : E × E) T).1))
            (D' : (E × E) →L[ℝ] E × E) x) := by
  obtain ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hGC1, -⟩ :=
    exists_pairMap_contDiffOn (I := I) g p
  obtain ⟨ra, εa, Ta, Za, hra, hεa, hTa, hTaεa, hflowa, hzeroa, hstricta⟩ :=
    exists_pairMap_hasStrictFDerivAt (I := I) g p
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set G : E × E → E × E :=
    fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1)
  set Ga : E × E → E × E :=
    fun x => ((x.1 : E), (Za ((x.1, Ta⁻¹ • x.2) : E × E) Ta).1)
  -- the two pair maps agree near the zero section
  have hι : Continuous (fun x : E × E => ((x.1, T⁻¹ • x.2) : E × E)) :=
    continuous_fst.prodMk (continuous_snd.const_smul T⁻¹)
  have hιa : Continuous (fun x : E × E => ((x.1, Ta⁻¹ • x.2) : E × E)) :=
    continuous_fst.prodMk (continuous_snd.const_smul Ta⁻¹)
  have hι0 : ((z₀.1, T⁻¹ • z₀.2) : E × E) = z₀ := by
    rw [hz₀def]
    show ((extChartAt I p p, T⁻¹ • (0 : E)) : E × E) = _
    rw [smul_zero]
  have hιa0 : ((z₀.1, Ta⁻¹ • z₀.2) : E × E) = z₀ := by
    rw [hz₀def]
    show ((extChartAt I p p, Ta⁻¹ • (0 : E)) : E × E) = _
    rw [smul_zero]
  have hm : (fun x : E × E => ((x.1, T⁻¹ • x.2) : E × E)) ⁻¹' ball z₀ r
      ∈ 𝓝 z₀ := by
    refine hι.continuousAt.preimage_mem_nhds ?_
    rw [hι0]
    exact ball_mem_nhds z₀ hr
  have hma : (fun x : E × E => ((x.1, Ta⁻¹ • x.2) : E × E)) ⁻¹' ball z₀ ra
      ∈ 𝓝 z₀ := by
    refine hιa.continuousAt.preimage_mem_nhds ?_
    rw [hιa0]
    exact ball_mem_nhds z₀ hra
  have hev : G =ᶠ[𝓝 z₀] Ga := by
    filter_upwards [hm, hma] with x hx hxa
    refine Prod.ext rfl ?_
    exact uniform_flow_pairMap_agree (I := I) g p hT hTε hTa hTaεa hflow hflowa
      (ball_subset_closedBall hx) (ball_subset_closedBall hxa)
  have hstrictG : HasStrictFDerivAt G
      ((ContinuousLinearMap.fst ℝ E E).prod
        ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
      z₀ :=
    hstricta.congr_of_eventuallyEq hev.symm
  -- the pair map fixes the center
  have hZT1 : (Z z₀ T).1 = extChartAt I p p := by
    have h0 : G z₀ = Ga z₀ := hev.self_of_nhds
    have hTaIcc : Ta ∈ Icc (-εa) εa := ⟨by linarith, hTaεa.le⟩
    have hGa0 : Ga z₀ = ((extChartAt I p p, extChartAt I p p) : E × E) := by
      show ((z₀.1 : E), (Za ((z₀.1, Ta⁻¹ • z₀.2) : E × E) Ta).1) = _
      rw [hιa0, hzeroa Ta hTaIcc]
    have hG0 : G z₀ = ((z₀.1 : E), (Z z₀ T).1) := by
      show ((z₀.1 : E), (Z ((z₀.1, T⁻¹ • z₀.2) : E × E) T).1) = _
      rw [hι0]
    have := congrArg Prod.snd ((hG0.symm.trans h0).trans hGa0)
    simpa using this
  -- the admissible set is open and contains the center
  set S : Set (E × E) := {x : E × E | ((x.1, T⁻¹ • x.2) : E × E) ∈ ball z₀ r}
  have hSopen : IsOpen S := isOpen_ball.preimage hι
  have hz₀S : z₀ ∈ S := by
    show ((z₀.1, T⁻¹ • z₀.2) : E × E) ∈ ball z₀ r
    rw [hι0]
    exact mem_ball_self hr
  -- continuity of the derivative map on the admissible set
  have hcontf : ContinuousOn (fderiv ℝ G) S :=
    hGC1.continuousOn_fderiv_of_isOpen hSopen le_rfl
  -- the shear as a continuous linear equivalence
  let shear := ContinuousLinearEquiv.shearAddRight E
  have hshear_coe : (shear : (E × E) →L[ℝ] E × E)
      = (ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)) :=
    rfl
  have hfd0 : fderiv ℝ G z₀ = (shear : (E × E) →L[ℝ] E × E) := by
    rw [hshear_coe]
    exact hstrictG.hasFDerivAt.fderiv
  -- the Neumann radius: derivatives within `c₀` of the shear are invertible
  set c₀ : ℝ := (‖(shear.symm : (E × E) →L[ℝ] E × E)‖ + 1)⁻¹ with hc₀def
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]
    positivity
  have hat : ContinuousAt (fderiv ℝ G) z₀ :=
    hcontf.continuousAt (hSopen.mem_nhds hz₀S)
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.continuousAt_iff.mp hat c₀ hc₀pos
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.isOpen_iff.mp hSopen z₀ hz₀S
  refine ⟨r, ε, T, min ρ₁ ρ₂, Z, hr, hε, hT, hTε, lt_min hρ₁ hρ₂, hflow, hZT1,
    ?_, hGC1, hstrictG, ?_⟩
  · -- the `ρ`-ball is admissible
    intro x hx
    exact hρ₂sub (ball_subset_ball (min_le_right _ _) hx)
  · -- the Neumann perturbation of the shear at every point of the ball
    intro x hx
    have hx₁ : dist x z₀ < ρ₁ := lt_of_lt_of_le (mem_ball.mp hx) (min_le_left _ _)
    have hxS : x ∈ S := hρ₂sub (ball_subset_ball (min_le_right _ _) hx)
    have hstrictx : HasStrictFDerivAt G (fderiv ℝ G x) x :=
      (hGC1.contDiffAt (hSopen.mem_nhds hxS)).hasStrictFDerivAt one_ne_zero
    have hnear : ‖(shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x‖ < c₀ := by
      have h := hball hx₁
      rw [dist_eq_norm, hfd0] at h
      rwa [norm_sub_rev]
    set t : (E × E) →L[ℝ] E × E :=
      (shear.symm : (E × E) →L[ℝ] E × E).comp
        ((shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x) with htdef
    have htnorm : ‖t‖ < 1 := by
      have hle : ‖t‖ ≤ ‖(shear.symm : (E × E) →L[ℝ] E × E)‖ *
          ‖(shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      have h2 : ‖(shear.symm : (E × E) →L[ℝ] E × E)‖ *
          ‖(shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x‖
          ≤ ‖(shear.symm : (E × E) →L[ℝ] E × E)‖ * c₀ :=
        mul_le_mul_of_nonneg_left hnear.le (norm_nonneg _)
      have h3 : ‖(shear.symm : (E × E) →L[ℝ] E × E)‖ * c₀ < 1 := by
        rw [hc₀def, mul_inv_lt_iff₀ (by positivity)]
        linarith [norm_nonneg (shear.symm : (E × E) →L[ℝ] E × E)]
      exact lt_of_le_of_lt (hle.trans h2) h3
    set u : ((E × E) →L[ℝ] E × E)ˣ := Units.oneSub t htnorm with hudef
    refine ⟨(ContinuousLinearEquiv.unitsEquiv ℝ (E × E) u).trans shear, ?_⟩
    have hcoe : (((ContinuousLinearEquiv.unitsEquiv ℝ (E × E) u).trans shear :
        (E × E) ≃L[ℝ] E × E) : (E × E) →L[ℝ] E × E) = fderiv ℝ G x := by
      refine ContinuousLinearMap.ext fun v => ?_
      rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.unitsEquiv_apply]
      have h1 : (u : (E × E) →L[ℝ] E × E) v = v - t v := by
        rw [hudef]
        show (((1 : (E × E) →L[ℝ] E × E) - t) : (E × E) →L[ℝ] E × E) v = v - t v
        rw [sub_apply, one_apply_eq_self]
      rw [h1, map_sub]
      have h2 : shear (t v) =
          ((shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x) v := by
        rw [htdef]
        show shear ((shear.symm : (E × E) →L[ℝ] E × E)
          (((shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x) v)) = _
        rw [ContinuousLinearEquiv.coe_coe]
        exact shear.apply_symm_apply _
      rw [h2, sub_apply]
      have h3 : shear v = (shear : (E × E) →L[ℝ] E × E) v := rfl
      rw [h3]
      abel
    rw [hcoe]
    exact hstrictx
end Exponential
end Riemannian
