module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Exponential/TotallyNormal.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes and upstream package-option restoration.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.UniformExistence
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.FlowDependence
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.FlowC1Dependence
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.EquationTransfer
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Exponential.StrictDerivative
public import Mathlib
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain the upstream overlapping finite-dimensional instance binders.
set_option linter.overlappingInstances false
/-!
# Totally normal neighborhoods (do Carmo Ch. 3, Theorem 3.7)

do Carmo, *Riemannian Geometry*, Ch. 3, Theorem 3.7: for every `p ∈ M` there
are a neighborhood `W` of `p` and `δ > 0` such that every `q ∈ W` is the
center of a normal ball of radius `δ` whose image contains `W` — any two
points of `W` are joined by a geodesic segment of small initial velocity,
uniquely parametrized. do Carmo's proof applies the inverse function theorem
to the pair map `F(q, v) = (q, exp_q v)`, whose differential at `(p, 0)` is
the invertible block matrix `[[I, 0], [I, I]]`.

The formalization works in the chart at `p` throughout, so that a *single*
uniform velocity ball serves every base point `q ∈ W`:

* the geodesic with initial data `(q, v)` is realized as the flow line of the
  chart-`p` coordinate spray through `(φ_p(q), w)`, where `w` is the chart-`p`
  coordinate of the velocity (`exists_uniform_geodesic_flow` accepts arbitrary
  initial conditions near the zero section, not only those over `p`);
* `isGeodesicOn_uniform_flow_segment` — **descent**: such a flow line projects
  to a curve on `M` satisfying the *intrinsic* moving-foot geodesic equation
  (`IsGeodesicOn`, the predicate consumed by the Hopf–Rinow development),
  via the chart-independence of the geodesic ODE (`EquationTransfer.lean`).
  This sidesteps the chart-`q`-anchored witness framework of
  `MaximalInterval.lean`, which cannot support a `δ` uniform in `q` (the
  charts at nearby `q` have no common lower bound on their source size);
* `exists_pairMap_hasStrictFDerivAt` — the pair map
  `G(y, w) = (y, (Z(y, w/T) T).1)` (chart reading of
  `(q, v) ↦ (q, exp_q v)` under the time-rescaling `γ(1, q, v) = γ(T, q, v/T)`)
  is strictly differentiable at `(φ_p(p), 0)` with derivative the shear
  `(a, b) ↦ (a, a + b)` — do Carmo's matrix `[[I, 0], [I, I]]` read in the
  first components. The derivative is computed from the variational equation
  along the equilibrium, whose operator `A(u, w) = (w, 0)` is two-step
  nilpotent, exactly as in `StrictDerivative.lean` but keeping the base-point
  slot of the initial condition free;
* `exists_totallyNormal_neighborhood` — the theorem: the shear is invertible,
  so the inverse function theorem makes `G` a homeomorphism near `(φ_p(p), 0)`;
  a product ball inside its source and a square neighborhood
  `W' × W' ⊆ G(ball × ball)` produce `W` and `δ` with existence and uniqueness
  of the joining parameter.
-/
noncomputable section
open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal
namespace ContinuousLinearEquiv
/-- **Math.** The right additive shear map `(a, b) ↦ (a, a + b)` on `E × E`. -/
protected def shearAddRight (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × E) ≃L[ℝ] E × E :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.snd ℝ E E) - (ContinuousLinearMap.fst ℝ E E)))
    (fun _ => by simp [ContinuousLinearMap.prod_apply])
    (fun _ => by simp [ContinuousLinearMap.prod_apply])
end ContinuousLinearEquiv
namespace Riemannian
namespace Exponential
open Riemannian.Geodesic Riemannian.FlowDependence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]
omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **The pair map of the exponential is strictly differentiable at the
zero section, with derivative the unipotent shear `(a, b) ↦ (a, a + b)`**
(do Carmo Ch. 3, proof of Theorem 3.7: `dF_{(p,0)} = [[I, 0], [I, I]]`). Here
the pair map is realized on the chart of `p` as
`G(y, w) = (y, (Z(y, T⁻¹ • w) T)₁)`, where `Z` is the uniform local flow of the
chart-`p` coordinate spray and `T` is a short Picard time: by the degree-2
homogeneity of the spray, `(Z(y, T⁻¹ • w) T)₁` is the chart reading of the
time-`1` geodesic value `exp_q(v)` for the base point `q = φ_p⁻¹(y)` and the
velocity with chart-`p` coordinate `w` (`isGeodesicOn_uniform_flow_segment`).

The derivative is computed exactly as for `d(exp_p)_0 = id`
(`exists_hasStrictFDerivAt_extChartAt_expMap`): the flow is strictly
differentiable in its full initial condition `(y, u) ∈ E × E` at the
equilibrium, with derivative the solution `D = const + ramp ∘ A` of the
variational equation for the nilpotent linearization `A(u, w) = (w, 0)`;
composing with the rescaling `(y, w) ↦ (y, T⁻¹ • w)` and evaluating at time `T`
gives `(a, b) ↦ a + b` in the position component. The base-point slot, frozen
in `StrictDerivative.lean`, is kept free — that is the only difference. -/
theorem exists_pairMap_hasStrictFDerivAt (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E), 0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      (∀ t ∈ Icc (-ε) ε, Z ((extChartAt I p p, (0 : E)) : E × E) t =
        ((extChartAt I p p, (0 : E)) : E × E)) ∧
      HasStrictFDerivAt
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        ((ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
        ((extChartAt I p p, (0 : E)) : E × E) := by
  classical
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip, hZzero, _⟩ :=
    exists_uniform_geodesic_flow (I := I) g p
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set F : E × E → E × E := fun ζ => geodesicSprayCoord (I := I) g p ζ.1 ζ.2
  set A : E × E →L[ℝ] E × E :=
    (ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E)
  have hA2 : A.comp A = 0 := sprayLinearization_comp_self
  have hfd : fderiv ℝ F z₀ = A :=
    fderiv_geodesicSprayCoord_equilibrium (I := I) g p
  -- the short Picard time
  set T : ℝ := min (ε / 2) (1 / (2 * (‖A‖ + 1)))
  have hT : 0 < T := lt_min (by positivity) (by positivity)
  have hTε : T < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hTA : T * ‖A‖ < 1 := by
    have h1 : T ≤ 1 / (2 * (‖A‖ + 1)) := min_le_right _ _
    have h2 : (0 : ℝ) < 2 * (‖A‖ + 1) := by positivity
    have h3 : T * ‖A‖ ≤ (1 / (2 * (‖A‖ + 1))) * ‖A‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg A)
    have h4 : (1 / (2 * (‖A‖ + 1))) * (2 * (‖A‖ + 1)) = 1 :=
      one_div_mul_cancel (ne_of_gt h2)
    nlinarith [norm_nonneg A]
  have hIccTsub : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := fun t ht =>
    ⟨le_trans (neg_nonpos.mpr hε.le) ht.1, ht.2.trans hTε.le⟩
  set tT : Set.Icc (0 : ℝ) T := ⟨T, ⟨hT.le, le_rfl⟩⟩
  -- the solution family on `C([0,T], E × E)`
  set σ : E × E → C(Set.Icc (0 : ℝ) T, E × E) := fun x =>
    if hx : x ∈ closedBall z₀ r then
      ⟨fun t => Z x t.1, by
        have hcont : ContinuousOn (Z x) (Icc (-ε) ε) := fun s hs =>
          ((hflow x hx).2.1 s hs).continuousWithinAt
        exact hcont.comp_continuous continuous_subtype_val
          fun t => hIccTsub t.2⟩
    else ContinuousMap.const _ z₀ with hσdef
  have hσ_ball : ∀ x, x ∈ closedBall z₀ r → ∀ t : Set.Icc (0 : ℝ) T,
      σ x t = Z x t.1 := by
    intro x hx t
    simp only [hσdef, dif_pos hx]
    rfl
  have hσ0 : σ z₀ = ContinuousMap.const _ z₀ := by
    refine ContinuousMap.ext fun t => ?_
    rw [hσ_ball z₀ (mem_closedBall_self hr.le) t, ContinuousMap.const_apply]
    exact hZzero t.1 (hIccTsub t.2)
  have hσc : ContinuousAt σ z₀ := by
    have hlips : LipschitzOnWith L σ (closedBall z₀ r) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [ContinuousMap.dist_le (mul_nonneg L.coe_nonneg dist_nonneg)]
      intro t
      rw [hσ_ball x hx t, hσ_ball y hy t]
      exact (hLip t.1 (hIccTsub t.2)).dist_le_mul x hx y hy
    exact (hlips.continuousOn.continuousWithinAt
      (mem_closedBall_self hr.le)).continuousAt (closedBall_mem_nhds z₀ hr)
  -- differentiability data for the spray near the equilibrium
  have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  have hmemz₀ : z₀ ∈ (extChartAt I p).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target p, mem_univ _⟩
  have hFs : ContDiffOn ℝ ∞ F ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    contDiffOn_geodesicSprayCoord_prod (I := I) g p
  obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.isOpen_iff.mp hopen z₀ hmemz₀
  have hd : ∀ x ∈ ball z₀ ρ', HasFDerivAt F (fderiv ℝ F x) x := fun x hx =>
    ((hFs.contDiffAt (hopen.mem_nhds (hρ'sub hx))).differentiableAt
      (by simp)).hasFDerivAt
  have hc : ContinuousAt (fderiv ℝ F) z₀ :=
    (hFs.continuousOn_fderiv_of_isOpen hopen (by exact_mod_cast le_top)).continuousAt
      (hopen.mem_nhds hmemz₀)
  have heq : F z₀ = 0 := geodesicSprayCoord_zero_velocity (I := I) g p _
  have hTL : T * ‖fderiv ℝ F z₀‖ < 1 := by rw [hfd]; exact hTA
  -- the flow solutions satisfy the Picard integral equation
  have hσres : ∀ᶠ x in 𝓝 z₀, picardResidual hT.le F (x, σ x) = 0 := by
    filter_upwards [ball_mem_nhds z₀ hr] with x hx
    have hx' : x ∈ closedBall z₀ r := ball_subset_closedBall hx
    obtain ⟨h0, hdZ, hmemZ⟩ := hflow x hx'
    exact picardResidual_eq_zero_of_hasDerivWithinAt hT hFs.continuousOn h0
      (fun t ht => hmemZ t (hIccTsub ht))
      (fun t ht => (hdZ t (hIccTsub ht)).mono hIccTsub)
      (σ x) (fun t => hσ_ball x hx' t)
  -- the explicit derivative from the nilpotent linearization
  set D : E × E →L[ℝ] C(Set.Icc (0 : ℝ) T, E × E) :=
    ContinuousLinearMap.const ℝ (Set.Icc (0 : ℝ) T) + (linearRamp hT.le).comp A
  have hD : ∀ v : E × E, D v - intervalPrimitive hT.le
      (postcomp (fderiv ℝ F z₀) (D v)) = ContinuousMap.const _ v := by
    intro v
    rw [hfd]
    exact sub_intervalPrimitive_postcomp_ramp hT.le hA2 v
  -- strict differentiability of the flow in its initial condition
  have hmain : HasStrictFDerivAt σ D z₀ :=
    hasStrictFDerivAt_of_picardResidual hT hρ'pos heq hd hc hTL hσ0 hσc hσres hD
  have heval : HasStrictFDerivAt (fun y => σ y tT)
      ((ContinuousMap.evalCLM ℝ tT).comp D) z₀ :=
    (ContinuousMap.evalCLM ℝ tT).hasStrictFDerivAt.comp z₀ hmain
  have hfstσ : HasStrictFDerivAt (fun y => (σ y tT).1)
      ((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)) z₀ :=
    (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.comp z₀ heval
  -- the rescaling of the velocity slot, keeping the base slot free
  set ι₂ : E × E → E × E := fun x => ((x.1 : E), T⁻¹ • x.2) with hι₂def
  set Dι₂ : E × E →L[ℝ] E × E :=
    (ContinuousLinearMap.fst ℝ E E).prod
      (T⁻¹ • ContinuousLinearMap.snd ℝ E E) with hDι₂def
  have hι₂ : HasStrictFDerivAt ι₂ Dι₂ z₀ := by
    have : HasStrictFDerivAt (fun x : E × E => Dι₂ x) Dι₂ z₀ :=
      Dι₂.hasStrictFDerivAt
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    show ι₂ x = Dι₂ x
    rw [hι₂def, hDι₂def]
    rfl
  have hι₂0 : ι₂ z₀ = z₀ := by
    rw [hι₂def, hz₀def]
    show ((extChartAt I p p : E), T⁻¹ • (0 : E)) = (extChartAt I p p, (0 : E))
    rw [smul_zero]
  -- strict derivative of the σ-composite pair map
  have hcompσ : HasStrictFDerivAt (fun x : E × E => (σ (ι₂ x) tT).1)
      (((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂) z₀ := by
    have hfstσ' : HasStrictFDerivAt (fun y => (σ y tT).1)
        ((ContinuousLinearMap.fst ℝ E E).comp
          ((ContinuousMap.evalCLM ℝ tT).comp D)) (ι₂ z₀) := by
      rw [hι₂0]; exact hfstσ
    exact hfstσ'.comp z₀ hι₂
  have hGpair : HasStrictFDerivAt
      (fun x : E × E => ((x.1 : E), (σ (ι₂ x) tT).1))
      ((ContinuousLinearMap.fst ℝ E E).prod
        ((((ContinuousLinearMap.fst ℝ E E).comp
          ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂))) z₀ :=
    (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.prodMk hcompσ
  -- the total derivative is the unipotent shear
  have hDtot : ((ContinuousLinearMap.fst ℝ E E).prod
      ((((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂)))
      = (ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)) := by
    refine ContinuousLinearMap.ext fun q => ?_
    obtain ⟨a, b⟩ := q
    refine Prod.ext rfl ?_
    show ((D (Dι₂ ((a, b) : E × E))) tT).1 = a + b
    have hval : Dι₂ ((a, b) : E × E) = ((a, T⁻¹ • b) : E × E) := by
      rw [hDι₂def]
      rfl
    rw [hval]
    have hDval : D (((a, T⁻¹ • b)) : E × E)
        = ContinuousMap.const _ (((a, T⁻¹ • b)) : E × E)
          + linearRamp hT.le ((((T⁻¹ • b : E), (0 : E))) : E × E) := rfl
    rw [hDval]
    show ((((a, T⁻¹ • b)) : E × E)
      + (T : ℝ) • ((((T⁻¹ • b : E), (0 : E))) : E × E)).1 = a + b
    show a + (T : ℝ) • (T⁻¹ • b) = a + b
    rw [smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  rw [hDtot] at hGpair
  -- pass from the σ-composite to the flow composite
  have hev : (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
      =ᶠ[𝓝 z₀] (fun x : E × E => ((x.1 : E), (σ (ι₂ x) tT).1)) := by
    have hι₂cont : Continuous ι₂ := by
      rw [hι₂def]
      exact continuous_fst.prodMk (continuous_snd.const_smul T⁻¹)
    have hball : closedBall z₀ r ∈ 𝓝 (ι₂ z₀) := by
      rw [hι₂0]
      exact closedBall_mem_nhds z₀ hr
    filter_upwards [hι₂cont.continuousAt.preimage_mem_nhds hball] with x hx
    have hx' : ι₂ x ∈ closedBall z₀ r := hx
    refine Prod.ext rfl ?_
    show (Z ((x.1, T⁻¹ • x.2) : E × E) T).1 = (σ (ι₂ x) tT).1
    rw [hσ_ball _ hx' tT]
  exact ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hZzero,
    hGpair.congr_of_eventuallyEq hev.symm⟩
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
/-- **Math.** **The pair map is `C¹` on a ball around the zero section** (do Carmo
Ch. 3, Theorem 3.7, the regularity of `F(q, v) = (q, exp_q v)`; the joint
analogue of `exp_p`-regularity on a ball, `lem:dc-ch3-2-9-c1ball`). There are a
uniform flow `Z` of the chart-`p` spray and `T < ε` such that the pair map
`G(y, w) = (y, (Z(y, T⁻¹ • w) T)₁)` is `C¹` on the open set of admissible
initial conditions, and, slicing at each base point `y`, the chart exponential
`w ↦ (Z(y, T⁻¹ • w) T)₁` at the base point `φ_p⁻¹(y)` is `C¹` on the uniform
velocity ball of radius `T·r`. The strict derivative of the flow in its full
initial condition exists at every admissible point
(`exists_uniform_geodesic_flow_hasStrictFDerivAt`), and pointwise strict
differentiability on an open set upgrades to `C¹`
(`contDiffOn_one_of_forall_hasStrictFDerivAt`). -/
theorem exists_pairMap_contDiffOn (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E), 0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      ContDiffOn ℝ 1
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        {x : E × E | ((x.1, T⁻¹ • x.2) : E × E) ∈
          ball ((extChartAt I p p, (0 : E)) : E × E) r} ∧
      (∀ y ∈ ball (extChartAt I p p) r,
        ContDiffOn ℝ 1 (fun w : E => (Z ((y, T⁻¹ • w) : E × E) T).1)
          (ball (0 : E) (T * r))) := by
  obtain ⟨r, ε, T, Z, _, σ, hT, hr, hε, hTε, hflow, _, _, hσZ, hD⟩ :=
    exists_uniform_geodesic_flow_hasStrictFDerivAt (I := I) g p
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set tT : Set.Icc (0 : ℝ) T := ⟨T, ⟨hT.le, le_rfl⟩⟩
  set ι₂ : E × E → E × E := fun x => ((x.1 : E), T⁻¹ • x.2) with hι₂def
  set Dι₂ : E × E →L[ℝ] E × E :=
    (ContinuousLinearMap.fst ℝ E E).prod
      (T⁻¹ • ContinuousLinearMap.snd ℝ E E) with hDι₂def
  have hι₂eq : ι₂ = fun x : E × E => Dι₂ x := by
    funext x
    rw [hι₂def, hDι₂def]
    rfl
  have hι₂cont : Continuous ι₂ := by
    rw [hι₂eq]
    exact Dι₂.continuous
  set G : E × E → E × E :=
    fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1)
  set S : Set (E × E) := {x : E × E | ι₂ x ∈ ball z₀ r}
  have hSopen : IsOpen S := isOpen_ball.preimage hι₂cont
  -- pointwise strict differentiability of `G` on `S`
  have key : ∀ x : E × E, ∃ D' : E × E →L[ℝ] E × E,
      x ∈ S → HasStrictFDerivAt G D' x := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨D, _, _, _, hDstrict⟩ := hD (ι₂ x) hx
      refine ⟨(ContinuousLinearMap.fst ℝ E E).prod
        ((((ContinuousLinearMap.fst ℝ E E).comp
          ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂)), fun _ => ?_⟩
      -- the σ-composite is strictly differentiable at `x`
      have heval : HasStrictFDerivAt (fun y => σ y tT)
          ((ContinuousMap.evalCLM ℝ tT).comp D) (ι₂ x) :=
        (ContinuousMap.evalCLM ℝ tT).hasStrictFDerivAt.comp (ι₂ x) hDstrict
      have hfstσ : HasStrictFDerivAt (fun y => (σ y tT).1)
          ((ContinuousLinearMap.fst ℝ E E).comp
            ((ContinuousMap.evalCLM ℝ tT).comp D)) (ι₂ x) :=
        (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.comp (ι₂ x) heval
      have hι₂strict : HasStrictFDerivAt ι₂ Dι₂ x := by
        rw [hι₂eq]
        exact Dι₂.hasStrictFDerivAt
      have hcompσ : HasStrictFDerivAt (fun x' : E × E => (σ (ι₂ x') tT).1)
          (((ContinuousLinearMap.fst ℝ E E).comp
            ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂) x :=
        hfstσ.comp x hι₂strict
      have hGpair : HasStrictFDerivAt
          (fun x' : E × E => ((x'.1 : E), (σ (ι₂ x') tT).1))
          ((ContinuousLinearMap.fst ℝ E E).prod
            ((((ContinuousLinearMap.fst ℝ E E).comp
              ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂))) x :=
        (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.prodMk hcompσ
      -- pass to the flow composite near `x`
      have hev : G =ᶠ[𝓝 x]
          (fun x' : E × E => ((x'.1 : E), (σ (ι₂ x') tT).1)) := by
        filter_upwards [hι₂cont.continuousAt.preimage_mem_nhds
          (isOpen_ball.mem_nhds hx)] with x' hx'
        have hx'' : ι₂ x' ∈ closedBall z₀ r := ball_subset_closedBall hx'
        refine Prod.ext rfl ?_
        show (Z ((x'.1, T⁻¹ • x'.2) : E × E) T).1 = (σ (ι₂ x') tT).1
        rw [hσZ _ hx'' tT]
      exact hGpair.congr_of_eventuallyEq hev.symm
    · exact ⟨0, fun h => absurd h hx⟩
  choose D' hD' using key
  have hGC1 : ContDiffOn ℝ 1 G S :=
    contDiffOn_one_of_forall_hasStrictFDerivAt hSopen fun x hx => hD' x hx
  refine ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hGC1, ?_⟩
  -- slice at a fixed base point `y`
  intro y hy
  have hemb : ContDiff ℝ 1 (fun w : E => ((y, w) : E × E)) :=
    contDiff_const.prodMk contDiff_id
  have hmaps : MapsTo (fun w : E => ((y, w) : E × E)) (ball (0 : E) (T * r)) S := by
    intro w hw
    show ((y, T⁻¹ • w) : E × E) ∈ ball z₀ r
    rw [mem_ball, hz₀def, Prod.dist_eq]
    refine max_lt (mem_ball.mp hy) ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
    have hw' : ‖w‖ < T * r := by
      have := mem_ball.mp hw
      rwa [dist_zero_right] at this
    rw [inv_mul_lt_iff₀ hT]
    linarith [hw']
  have hcomp : ContDiffOn ℝ 1 (fun w : E => G ((y, w) : E × E))
      (ball (0 : E) (T * r)) :=
    hGC1.comp hemb.contDiffOn hmaps
  have hsnd : ContDiffOn ℝ 1 (fun w : E => (G ((y, w) : E × E)).2)
      (ball (0 : E) (T * r)) := contDiff_snd.comp_contDiffOn hcomp
  exact hsnd
end Exponential
end Riemannian
