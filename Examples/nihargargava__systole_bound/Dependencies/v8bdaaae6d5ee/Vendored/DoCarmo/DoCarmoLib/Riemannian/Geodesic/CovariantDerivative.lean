module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Geodesic/CovariantDerivative.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream options and proof-preserving API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Equation
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.LinearODE
public import Mathlib
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain upstream typeclass binders; this new linter changes no proof checks.
set_option linter.overlappingInstances false
/-!
# Covariant derivative of a vector field along a curve (do Carmo Ch. 2, §2)

For a Riemannian metric `g` on `M`, a chart basepoint `α : M`, a coordinate curve
`u : ℝ → E` (the chart image `φ_α ∘ c` of a curve `c : I → M`) and a coordinate
vector field `V : ℝ → E` along it, do Carmo's Proposition 2.2 gives the covariant
derivative `DV/dt` by the coordinate formula (do Carmo (1))
$$\frac{DV}{dt} = \dot V + \Gamma\big(\dot u, V\big)(u),$$
where `Γ(·,·)(y) = chartChristoffelContraction g α · · y` is the Christoffel
contraction already used by the geodesic pipeline (`Geodesic.Equation`).

This file records:

* `Riemannian.covariantDerivCoord g α u V` — the operator `DV/dt` in coordinates.
* `covariantDerivCoord_add` / `covariantDerivCoord_smul` — the two characterizing
  algebraic properties (do Carmo Prop. 2.2 (a) additivity and (b) the Leibniz
  rule), the content that makes `D/dt` a *bona fide* derivative of vector fields
  along curves.
* `Riemannian.IsParallelCoord g α u V` — do Carmo Def. 2.5: `V` is **parallel**
  along the curve when `DV/dt ≡ 0`.
* `covariantDerivCoord_eq_zero_iff` — the parallelism equation in solved ODE form
  `V' = −Γ(u', V)(u)`, the first-order linear system whose Picard–Lindelöf theory
  yields parallel transport (do Carmo Prop. 2.6).

Reference: do Carmo, *Riemannian Geometry*, Ch. 2 §2, Prop. 2.2, Def. 2.5, Prop. 2.6.
-/
open scoped Manifold Topology ContDiff
open Set
noncomputable section
namespace Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
/-- **Math.** do Carmo Ch. 2, Prop. 2.2, formula (1). The **covariant derivative**
`DV/dt` of a coordinate vector field `V : ℝ → E` along the coordinate curve
`u : ℝ → E`, read in the fixed chart at `α`:
`DV/dt = V' + Γ(u', V)(u)`, where `Γ` is `Geodesic.chartChristoffelContraction g α`.
This is the closed expression forced on any operator satisfying do Carmo's
axioms (a)–(c); the file proves it satisfies (a) and (b). -/
def covariantDerivCoord (g : RiemannianMetric I M) (α : M) (u V : ℝ → E) (t : ℝ) : E :=
  deriv V t + Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t)
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] theorem covariantDerivCoord_def (g : RiemannianMetric I M) (α : M)
    (u V : ℝ → E) (t : ℝ) :
    covariantDerivCoord (I := I) g α u V t =
      deriv V t
        + Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t) := rfl
theorem sum4_swap14 {α : Type*} [AddCommMonoid α] {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → α) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f d b c a := by
  have key : (∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2)
      = ∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.2.2 x.2.1 x.2.2.1 x.1 :=
    Fintype.sum_bijective (fun x => (x.2.2.2, x.2.1, x.2.2.1, x.1))
      (Function.Involutive.bijective (fun _ => rfl)) _ _ (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using key
/-- **Math.** Reindexing helper: a four-fold finite sum is invariant under swapping the
roles of its second and last summation index. -/
theorem sum4_swap24 {α : Type*} [AddCommMonoid α] {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → α) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f a d c b := by
  have key : (∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2)
      = ∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.2.2 x.2.2.1 x.2.1 :=
    Fintype.sum_bijective (fun x => (x.1, x.2.2.2, x.2.2.1, x.2.1))
      (Function.Involutive.bijective (fun _ => rfl)) _ _ (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using key
/-- **Math.** Chart coordinate `i` packaged as a continuous linear functional on `E`. -/
noncomputable def Geodesic.chartCoordFunctional (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  ((Module.finBasis ℝ E).coord i).toContinuousLinearMap
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] theorem Geodesic.chartCoordFunctional_apply (i : Fin (Module.finrank ℝ E)) (v : E) :
    Geodesic.chartCoordFunctional (E := E) i v = Geodesic.chartCoord (E := E) i v := by
  simp only [Geodesic.chartCoordFunctional, LinearMap.coe_toContinuousLinearMap',
    Module.Basis.coord_apply, Geodesic.chartCoord_def]
/-- **Math.** The chart Gram **inner product** of two coordinate vectors `a, b : E`
at the base point `y`, read in the chart at `α`:
`⟨a, b⟩_y = ∑_{i,j} G_{ij}(y)\, a^i\, b^j`, where `G_{ij} =` `chartGramOnE` and the
components `a^i, b^j` are taken in the chart-model basis. -/
def chartMetricInner (g : RiemannianMetric I M) (α : M) (y a b : E) : ℝ :=
  ∑ i, ∑ j, chartGramOnE (I := I) g α i j y
    * Geodesic.chartCoord (E := E) i a * Geodesic.chartCoord (E := E) j b
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] theorem chartMetricInner_def (g : RiemannianMetric I M) (α : M) (y a b : E) :
    chartMetricInner (I := I) g α y a b
      = ∑ i, ∑ j, chartGramOnE (I := I) g α i j y
          * Geodesic.chartCoord (E := E) i a * Geodesic.chartCoord (E := E) j b := rfl
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart Gram inner product is additive in its first vector argument. -/
theorem chartMetricInner_add_left (g : RiemannianMetric I M) (α : M) (y a a' b : E) :
    chartMetricInner (I := I) g α y (a + a') b
      = chartMetricInner (I := I) g α y a b + chartMetricInner (I := I) g α y a' b := by
  simp only [chartMetricInner_def, Geodesic.chartCoord_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart Gram inner product is additive in its second vector argument. -/
theorem chartMetricInner_add_right (g : RiemannianMetric I M) (α : M) (y a b b' : E) :
    chartMetricInner (I := I) g α y a (b + b')
      = chartMetricInner (I := I) g α y a b + chartMetricInner (I := I) g α y a b' := by
  simp only [chartMetricInner_def, Geodesic.chartCoord_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The `i`-th chart coordinate of the Christoffel contraction
`Γ(v, w)(y)` is the bilinear expression `∑_{a,b} Γ^i_{ab}(y)\, v^a\, w^b`. -/
theorem chartCoord_chartChristoffelContraction (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (v w y : E) :
    Geodesic.chartCoord (E := E) i (Geodesic.chartChristoffelContraction (I := I) g α v w y)
      = ∑ a, ∑ b, chartChristoffel (I := I) g α a b i y
          * Geodesic.chartCoord (E := E) a v * Geodesic.chartCoord (E := E) b w := by
  classical
  rw [← Geodesic.chartCoordFunctional_apply, Geodesic.chartChristoffelContraction_def, map_sum]
  have hb : ∀ k, Geodesic.chartCoordFunctional (E := E) i (Module.finBasis ℝ E k)
      = (if k = i then (1 : ℝ) else 0) := by
    intro k
    rw [Geodesic.chartCoordFunctional_apply, Geodesic.chartCoord_def, Module.Basis.repr_self,
      Finsupp.single_apply]
  simp only [map_smul, smul_eq_mul, hb, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ i]
  simp only [Finset.mem_univ, if_true]
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Expansion of a directional derivative in the chart-model basis:
`DG(y)·w = ∑_k w^k\, ∂_k G(y)`, the sum of partial derivatives weighted by the
components of the direction `w`. -/
theorem fderiv_apply_eq_sum_partialDeriv (G : E → ℝ) (y w : E) :
    fderiv ℝ G y w = ∑ k, Geodesic.chartCoord (E := E) k w * partialDeriv (E := E) k G y := by
  conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** do Carmo Ch. 2, §3, the algebraic heart of Prop. 3.2 (coordinate
form): the direction-derivative of the chart Gram inner product, expanded through
formula (10) `∇g = 0`, splits exactly into the two Christoffel-correction terms of
the covariant derivative. For every base point `y` in the chart domain,
`∑_{i,j}(∑_k (u')^k ∂_k G_{ij})\, V^i W^j
  = ⟨Γ(u',V), W⟩_y + ⟨V, Γ(u',W)⟩_y`. -/
theorem chartMetricInner_gram_deriv_balance (g : RiemannianMetric I M) (α : M)
    (y ud Vv Ww : E)
    (hbase : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (∑ i, ∑ j, (∑ k, Geodesic.chartCoord (E := E) k ud
          * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)
        * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww)
      = chartMetricInner (I := I) g α y
            (Geodesic.chartChristoffelContraction (I := I) g α ud Vv y) Ww
        + chartMetricInner (I := I) g α y Vv
            (Geodesic.chartChristoffelContraction (I := I) g α ud Ww y) := by
  classical
  -- substitute formula (10) for each partial derivative of the Gram matrix
  have hL : (∑ i, ∑ j, (∑ k, Geodesic.chartCoord (E := E) k ud
          * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)
        * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww)
      = (∑ i, ∑ j, ∑ k, ∑ m, Geodesic.chartCoord (E := E) k ud
            * chartGramOnE (I := I) g α m j y * chartChristoffel (I := I) g α k i m y
            * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww)
        + (∑ i, ∑ j, ∑ k, ∑ m, Geodesic.chartCoord (E := E) k ud
            * chartGramOnE (I := I) g α i m y * chartChristoffel (I := I) g α k j m y
            * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [partialDeriv_chartGramOnE_eq (I := I) g α i j k y hbase, Finset.mul_sum,
      Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hL]
  -- expand the two target inner products via `chartCoord` of the contraction
  have hR1 : chartMetricInner (I := I) g α y
        (Geodesic.chartChristoffelContraction (I := I) g α ud Vv y) Ww
      = ∑ i, ∑ j, ∑ a, ∑ b, chartGramOnE (I := I) g α i j y
          * chartChristoffel (I := I) g α a b i y
          * Geodesic.chartCoord (E := E) a ud * Geodesic.chartCoord (E := E) b Vv
          * Geodesic.chartCoord (E := E) j Ww := by
    simp only [chartMetricInner_def, chartCoord_chartChristoffelContraction,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hR2 : chartMetricInner (I := I) g α y Vv
        (Geodesic.chartChristoffelContraction (I := I) g α ud Ww y)
      = ∑ i, ∑ j, ∑ a, ∑ b, chartGramOnE (I := I) g α i j y
          * chartChristoffel (I := I) g α a b j y
          * Geodesic.chartCoord (E := E) a ud * Geodesic.chartCoord (E := E) b Ww
          * Geodesic.chartCoord (E := E) i Vv := by
    simp only [chartMetricInner_def, chartCoord_chartChristoffelContraction,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hR1, hR2]
  congr 1
  · -- SL1 = R1 : swap the first (V-index) and last (Gram/Christoffel-upper) indices
    rw [sum4_swap14 (fun i j k m => Geodesic.chartCoord (E := E) k ud
        * chartGramOnE (I := I) g α m j y * chartChristoffel (I := I) g α k i m y
        * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · -- SL2 = R2 : swap the second (W-index) and last (Gram/Christoffel-upper) indices
    rw [sum4_swap24 (fun i j k m => Geodesic.chartCoord (E := E) k ud
        * chartGramOnE (I := I) g α i m y * chartChristoffel (I := I) g α k j m y
        * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** do Carmo Ch. 2, §3, Prop. 3.2 (coordinate form / do Carmo eq. (3)):
the Levi-Civita covariant derivative along a curve is **compatible with the
metric**. For a coordinate curve `u` staying in the chart domain and coordinate
vector fields `V, W` along it, the chart Gram inner product obeys the product rule
`d/dt⟨V, W⟩ = ⟨DV/dt, W⟩ + ⟨V, DW/dt⟩`, with `D/dt = covariantDerivCoord`. The `hG`
hypothesis is the differentiability of the chart metric coefficients along the
curve (automatic for a curve in the chart domain, the metric being smooth there).
The proof combines the product/chain rule with do Carmo's formula (10)
(`chartMetricInner_gram_deriv_balance`). -/
theorem hasDerivAt_chartMetricInner_along (g : RiemannianMetric I M) (α : M)
    (u V W : ℝ → E) {t : ℝ}
    (hu : DifferentiableAt ℝ u t) (hV : DifferentiableAt ℝ V t) (hW : DifferentiableAt ℝ W t)
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    HasDerivAt (fun s => chartMetricInner (I := I) g α (u s) (V s) (W s))
      (chartMetricInner (I := I) g α (u t) (covariantDerivCoord (I := I) g α u V t) (W t)
        + chartMetricInner (I := I) g α (u t) (V t) (covariantDerivCoord (I := I) g α u W t)) t := by
  classical
  have ha : ∀ i j, HasDerivAt (fun s => chartGramOnE (I := I) g α i j (u s))
      (fderiv ℝ (chartGramOnE (I := I) g α i j) (u t) (deriv u t)) t :=
    fun i j => (hG i j).hasFDerivAt.comp_hasDerivAt t hu.hasDerivAt
  have hv : ∀ i, HasDerivAt (fun s => Geodesic.chartCoord (E := E) i (V s))
      (Geodesic.chartCoord (E := E) i (deriv V t)) t := by
    intro i
    simpa only [Geodesic.chartCoordFunctional_apply, Function.comp_def] using
      (Geodesic.chartCoordFunctional (E := E) i).hasFDerivAt.comp_hasDerivAt t hV.hasDerivAt
  have hw : ∀ j, HasDerivAt (fun s => Geodesic.chartCoord (E := E) j (W s))
      (Geodesic.chartCoord (E := E) j (deriv W t)) t := by
    intro j
    simpa only [Geodesic.chartCoordFunctional_apply, Function.comp_def] using
      (Geodesic.chartCoordFunctional (E := E) j).hasFDerivAt.comp_hasDerivAt t hW.hasDerivAt
  -- derivative of the along-curve inner product, via product rule on each `G_{ij} V^i W^j`
  have hsum : HasDerivAt (fun s => chartMetricInner (I := I) g α (u s) (V s) (W s))
      (∑ i, ∑ j, ((fderiv ℝ (chartGramOnE (I := I) g α i j) (u t) (deriv u t)
              * Geodesic.chartCoord (E := E) i (V t)
            + chartGramOnE (I := I) g α i j (u t) * Geodesic.chartCoord (E := E) i (deriv V t))
          * Geodesic.chartCoord (E := E) j (W t)
        + chartGramOnE (I := I) g α i j (u t) * Geodesic.chartCoord (E := E) i (V t)
          * Geodesic.chartCoord (E := E) j (deriv W t))) t := by
    have hfun : (fun s => chartMetricInner (I := I) g α (u s) (V s) (W s))
        = ∑ i, ∑ j, fun s => chartGramOnE (I := I) g α i j (u s)
            * Geodesic.chartCoord (E := E) i (V s) * Geodesic.chartCoord (E := E) j (W s) := by
      funext s; simp only [chartMetricInner_def, Finset.sum_apply]
    rw [hfun]
    apply HasDerivAt.sum
    intro i _
    apply HasDerivAt.sum
    intro j _
    exact ((ha i j).mul (hv i)).mul (hw j)
  -- identify that derivative with the covariant-derivative expression
  have hbalance := chartMetricInner_gram_deriv_balance (I := I) g α (u t) (deriv u t) (V t) (W t) hbase
  refine hsum.congr_deriv ?_
  rw [covariantDerivCoord_def, covariantDerivCoord_def, chartMetricInner_add_left,
    chartMetricInner_add_right]
  -- rewrite each `G_{ij}` direction-derivative through its partial derivatives, then formula (10)
  have hGram : (∑ i, ∑ j, ((fderiv ℝ (chartGramOnE (I := I) g α i j) (u t) (deriv u t)
              * Geodesic.chartCoord (E := E) i (V t)
            + chartGramOnE (I := I) g α i j (u t) * Geodesic.chartCoord (E := E) i (deriv V t))
          * Geodesic.chartCoord (E := E) j (W t)
        + chartGramOnE (I := I) g α i j (u t) * Geodesic.chartCoord (E := E) i (V t)
          * Geodesic.chartCoord (E := E) j (deriv W t)))
      = (∑ i, ∑ j, (∑ k, Geodesic.chartCoord (E := E) k (deriv u t)
            * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (u t))
          * Geodesic.chartCoord (E := E) i (V t) * Geodesic.chartCoord (E := E) j (W t))
        + chartMetricInner (I := I) g α (u t) (deriv V t) (W t)
        + chartMetricInner (I := I) g α (u t) (V t) (deriv W t) := by
    simp only [chartMetricInner_def, fderiv_apply_eq_sum_partialDeriv,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hGram, hbalance]
  ring
omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** do Carmo Ch. 3, §2, the geodesic definition's **constant-speed**
property. If `γ` satisfies the geodesic equation at `t` — read in the moving-foot
chart at `γ t` via `HasGeodesicEquationAt` — then the chart Gram squared speed
`s ↦ ⟨u'(s), u'(s)⟩`, where `u = chartLocalCurve γ t` is the chart image of `γ`
at the foot `γ t` and `⟨·,·⟩ = chartMetricInner g (γ t)`, has vanishing derivative
at `s = t`. This is do Carmo's computation
`d/dt⟨γ',γ'⟩ = 2⟨Dγ'/dt, γ'⟩ = 0`: it holds at each base time because the
covariant acceleration `Dγ'/dt = covariantDerivCoord g (γ t) u u'` of a geodesic
vanishes there, so the metric-compatibility product rule
`hasDerivAt_chartMetricInner_along` yields a zero derivative. -/
theorem hasDerivAt_chartMetricInner_geodesic_speed_zero
    (g : RiemannianMetric I M) [I.Boundaryless] {γ : ℝ → M} {t : ℝ}
    (hgeo : Geodesic.HasGeodesicEquationAt (I := I) g γ t) :
    HasDerivAt (fun s => chartMetricInner (I := I) g (γ t)
        (Geodesic.chartLocalCurve (I := I) γ t s)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) s)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) s)) 0 t := by
  classical
  set u : ℝ → E := Geodesic.chartLocalCurve (I := I) γ t with hu_def
  obtain ⟨v, a, hv_deriv, _h_ev, ha_deriv, hgeo_eq⟩ := hgeo
  -- regularity of the chart curve and its velocity at `t`
  have hu : DifferentiableAt ℝ u t := hv_deriv.differentiableAt
  have hV : DifferentiableAt ℝ (deriv u) t := ha_deriv.differentiableAt
  have hderiv_u : deriv u t = v := hv_deriv.deriv
  have hderiv2_u : deriv (deriv u) t = a := ha_deriv.deriv
  have hut : u t = extChartAt I (γ t) (γ t) := by
    rw [hu_def, Geodesic.chartLocalCurve_def]
  -- differentiability of the Gram coefficients at the base point
  have hy : extChartAt I (γ t) (γ t) ∈ (extChartAt I (γ t)).target :=
    (extChartAt I (γ t)).map_source (mem_extChartAt_source (I := I) (γ t))
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g (γ t) i j) (u t) := by
    intro i j
    rw [hut]
    exact ((chartGramOnE_contDiffOn (I := I) g (γ t) i j).contDiffAt
      (extChartAt_target_mem_nhds' (I := I) hy)).differentiableAt (by norm_num)
  -- base-set membership for the metric-compatibility product rule
  have hbase : (extChartAt I (γ t)).symm (u t) ∈
      (trivializationAt E (TangentSpace I) (γ t)).baseSet := by
    rw [hut, (extChartAt I (γ t)).left_inv (mem_extChartAt_source (I := I) (γ t))]
    exact FiberBundle.mem_baseSet_trivializationAt' (γ t)
  -- covariant acceleration of the geodesic vanishes at `t`
  have hcov : covariantDerivCoord (I := I) g (γ t) u (deriv u) t = 0 := by
    rw [covariantDerivCoord_def, hderiv2_u, hderiv_u, hut]
    exact hgeo_eq
  -- metric-compatibility product rule with `V = W = u'`, whose derivative reduces to
  -- `⟨Du'/dt, u'⟩ + ⟨u', Du'/dt⟩ = 0`
  refine (hasDerivAt_chartMetricInner_along (I := I) g (γ t) u (deriv u) (deriv u)
    hu hV hV hG hbase).congr_deriv ?_
  rw [hcov]
  simp [chartMetricInner_def]
/-! ## Uniqueness of the covariant derivative along a curve (do Carmo Prop. 2.2)

do Carmo's Proposition 2.2 asserts that the covariant derivative `D/dt` is the
*unique* correspondence on vector fields along a curve satisfying (a) additivity,
(b) the Leibniz rule, and (c) the induced-field rule `D(Y∘u)/dt = (∇_{u'}Y)(u)`. The
existence half is `covariantDerivCoord` together with `covariantDerivCoord_add` (a),
`covariantDerivCoord_smul` (b) and `covariantDerivCoord_induced` (c). The theorem
below is the uniqueness half: any operator `D` obeying (a), (b), (c) is forced to be
`covariantDerivCoord`, which is do Carmo's formula (1). -/
end Riemannian
