module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Geodesic/FiberScaling.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream options and proof-preserving API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Equation
public import Mathlib
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain upstream typeclass binders; this new linter changes no proof checks.
set_option linter.overlappingInstances false
/-!
# The fibre-scaling bundle map and the geodesic spray

For a smooth manifold `M` modelled on a normed space `E`, the *fibre-scaling*
map `fiberScaling a : TM → TM`, `⟨x, w⟩ ↦ ⟨x, a·w⟩`, scales each tangent
vector by the scalar `a` while fixing its foot point. It is the bundle-level
map underlying do Carmo's homogeneity lemma (Ch. 3, Lemma 2.6)
`γ(t, q, a v) = γ(a t, q, v)`: the geodesic spray `geodesicVectorFieldChart`
is *degree-2 homogeneous* under `fiberScaling a`, so an integral curve of the
spray, reparametrised in time by `a` and fibre-scaled by `a`, is again an
integral curve of the spray.

This file records the reusable bundle-level infrastructure:

* `fiberScaling a` — the map, with its projection/fibre unfolding lemmas.
* `chartFiberCoord_fiberScaling` — fibre linearity: the chart-`α` fibre
  coordinate of `fiberScaling a p` is `a` times that of `p` (on the chart
  domain, where the trivialisation is genuinely linear).
* `fiberScaling_contMDiff` — smoothness of the bundle map.
* `geodesicVectorFieldChartFiber_fiberScaling` — the coordinate pushforward:
  the chart-fibre spray value at `fiberScaling a p` is the spray coordinate
  map at the scaled velocity `a·v`, which by `geodesicSprayCoord_smul_velocity`
  scales the horizontal component by `a` and the vertical by `a²`.

On top of this, the file carries out the tangent-map (`mfderiv`) development on
`T(TM)`:

* `fiberScalingLinearMap a` (`Λ_a : (x, w) ↦ (x, a • w)`) — the common coordinate
  shadow of `fiberScaling a` in every tangent-bundle chart
  (`extChartAt_tangent_fiberScaling`), since `TM`-charts depend only on the foot
  point, which fibre scaling fixes.
* `hasMFDerivAt_fiberScaling` / `mfderiv_fiberScaling` — `d(fiberScaling a) = Λ_a`
  in the definitional `E × E` presentation of the double tangent spaces.
* `symmL_trivializationAt_tangent_fiberScaling` — the graded naturality `(★)` of
  the inverse trivialization of `T(TM)` under fibre scaling, proved by a
  conjugation trick (differentiate `Φ ∘ Λ_a = S_a ∘ Φ` for the inverse chart `Φ`).
* `geodesicVectorFieldChart_fiberScaling` / `mfderiv_fiberScaling_smul_spray` —
  the keystone: the chart-fixed geodesic spray is degree-2 homogeneous under fibre
  scaling in definitional coordinates, equivalently
  `d(fiberScaling a)(a • G) = G ∘ fiberScaling a`. This feeds the integral-curve
  homogeneity transform in `Geodesic/Homogeneity.lean` (do Carmo Ch. 3, Lemma 2.6).
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
section FibreLinearity
end FibreLinearity
section Smoothness
variable [I.Boundaryless]
end Smoothness
section CoordinatePushforward
end CoordinatePushforward
/-! ### The tangent map of the fibre-scaling bundle map, and graded naturality

In EVERY tangent-bundle chart (the chart of `TM` at a basepoint `b` depends only on
the foot point `b.proj`, which `fiberScaling a` fixes), the fibre-scaling map reads
as one and the same *linear* model map
`Λ_a := fiberScalingLinearMap a : (x, w) ↦ (x, a • w)` on `E × E`.

Two consequences, obtained purely by the chain rule (no block-matrix computation on
the double tangent bundle is needed):

* `hasMFDerivAt_fiberScaling` — `fiberScaling a` has manifold derivative `Λ_a` at
  every point of `TM`, in the definitional `E × E` presentation of the double
  tangent spaces.
* `symmL_trivializationAt_tangent_fiberScaling` — the **graded naturality** of the
  inverse trivialization of `T(TM)`: writing `e₀` for the trivialization of
  `T(TM)` at `⟨α, 0⟩` and `S_a` for `fiberScaling a`,
  `e₀.symmL (S_a q) ∘ Λ_a = Λ_a ∘ e₀.symmL q` over the chart domain. The proof is a
  conjugation trick: `S_a` reads as `Λ_a` in the chart at `⟨α, 0⟩`, so
  `Φ ∘ Λ_a = S_a ∘ Φ` near the chart image of `q`, where `Φ` is the inverse chart;
  differentiating both sides (with `Λ_a` linear) yields the naturality because
  `e₀.symmL` is the manifold derivative of `Φ`
  (`TangentBundle.symmL_trivializationAt`).

Combining with the coordinate pushforward `geodesicVectorFieldChartFiber_fiberScaling`
gives the keystone `geodesicVectorFieldChart_fiberScaling`: the chart-fixed geodesic
spray is degree-2 homogeneous under fibre scaling, **in definitional coordinates**,
which is the form consumed by the integral-curve homogeneity transform.
-/
section ChartReading
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The extended chart of the tangent bundle at a basepoint `b : TM` is the
product of the base chart at `b.proj` and the fibre trivialization at `b.proj`:
`φ_b(r) = (φ_{b.proj}(r.proj), (e_{b.proj} r).2)` for every `r` whose foot lies in
the trivialization base set. -/
lemma extChartAt_tangent_apply (b : TangentBundle I M) {r : TangentBundle I M}
    (hr : r.proj ∈ (trivializationAt E (TangentSpace I) b.proj).baseSet) :
    extChartAt I.tangent b r =
      (extChartAt I b.proj r.proj,
        (trivializationAt E (TangentSpace I) b.proj r).2) := by
  classical
  rw [FiberBundle.extChartAt (IB := I) (F := E) (E := TangentSpace I) b]
  have hr_src : r ∈ (trivializationAt E (TangentSpace I) b.proj).source :=
    (trivializationAt E (TangentSpace I) b.proj).mem_source.mpr hr
  have hfst : ((trivializationAt E (TangentSpace I) b.proj) r).1 = r.proj :=
    (trivializationAt E (TangentSpace I) b.proj).coe_fst hr_src
  simp only [PartialEquiv.coe_trans, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    Function.comp_apply]
  rfl
end ChartReading
section MFDerivFiberScaling
variable [I.Boundaryless]
end MFDerivFiberScaling
section SymmLNaturality
variable [I.Boundaryless]
end SymmLNaturality
section SprayKeystone
variable [I.Boundaryless]
end SprayKeystone
end Geodesic
end Riemannian
end
