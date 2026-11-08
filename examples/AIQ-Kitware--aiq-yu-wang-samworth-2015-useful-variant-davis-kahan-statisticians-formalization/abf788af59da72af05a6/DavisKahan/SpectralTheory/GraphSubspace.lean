/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.SpectralTheory.OperatorAngle
import ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit
import Mathlib
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Graph subspaces and angular operators

Literature writeup: local TeX, Sections 16--17.  This is the geometric bridge
between projection estimates and operator Riccati equations.
-/


/-! ## Construction plan

* Define the graph subspace as the range of `x |-> (x, X x)` under the
  orthogonal-sum equivalence; for an ambient decomposition, transport this
  construction through `U x Uperp ~= E`.
* Prove the graph projection formula by solving the normal equations.  The
  diagonal factors are `(1+X⋆X)^{-1}` and `(1+XX⋆)^{-1}` and are positive
  invertible.
* Derive the graph/angular correspondence from transversality of the first
  coordinate projection, then identify the graph norm with tangent of the
  operator angle.
-/


/-! ## Donor API audit and execution plan

The graph-subspace vendor survey is recorded in
`dev/graph-subspace-vendor-survey-2026-07-14.md`.  The immediate proof should
reuse the pinned Mathlib APIs below rather than rebuilding closed-range or
inverse-continuity arguments locally.

Work with subtype maps rather than ambient formulas first.  Define the graph
embedding from `U` to `E` by `u ↦ u + X u`, where `IsAngularOperator U X`
ensures `X u ∈ Uᗮ`.  The Pythagorean identity gives a one-antilipschitz bound.
Use `AntilipschitzWith.isClosed_range` to obtain closedness of the range, then
the standard closed-subspace projection instance.

For acute-to-graph, restrict `projection U` to `V`.  The preferred inverse
routes are:

* `ContinuousLinearMap.equivRange` after injectivity and closed range are known;
* `ContinuousLinearEquiv.ofBijective` after direct injectivity and surjectivity;
* `Units.oneSub` for the near-identity compression when the acute norm bound
  yields an operator of norm strictly below one.

`LinearPMap.graph` and `LinearPMap.IsClosed` are the canonical graph language
for later alignment with the unbounded appendix.  The bounded graph may be
implemented first as a continuous-map range, but its comparison with the
`LinearPMap` graph should be explicit rather than introducing a second
unrelated graph notion.

The current unconditional projection instance for `graphSubspace U X` is a
signature defect: an arbitrary ambient `X` need not give a closed graph range.
The implementation pass must either add `hX : IsAngularOperator U X` to that
instance or bundle angularity into the graph object before closing it.

For the projection formula, define
`G := I + X.adjoint ∘L X` on `U`.  Prove `G ≥ I`, hence invertible, before
mentioning `G⁻¹` or `G⁻¹/²`.  Construct the normalized graph isometry
`J := graphEmbedding ∘ G⁻¹/²`; then the projection is `J ∘L J.adjoint`.
Expand this identity blockwise and only afterward package the ambient
`graphProjectionFormula`.
-/

namespace TauCeti

open TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Graph subspace over `U` with angular operator `X`.

Defined as the topological closure of the parametrized graph range
`{P_U x + X (P_U x) | x}`, matching the range convention of
`acute_iff_exists_bounded_angularOperator`.  Taking the closure makes the
orthogonal-projection instance below unconditional; for an angular operator
the graph embedding is bounded below, its range is already closed, and the
closure adds nothing. -/
noncomputable def graphSubspace (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : E →L[𝕜] E) : Submodule 𝕜 E :=
  (LinearMap.range
    (projection U + X ∘L projection U).toLinearMap).topologicalClosure

/-- The graph of a bounded operator is orthogonally complemented, being closed. -/
noncomputable instance graphSubspace_hasOrthogonalProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) : (graphSubspace U X).HasOrthogonalProjection := by
  have : CompleteSpace (graphSubspace U X) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

omit [CompleteSpace E] in
/-- For an angular operator the graph embedding fixes the range pointwise
through `T ∘ P_U = T` and `P_U ∘ T = P_U`, so the parametrized graph range is
closed and the graph subspace is exactly that range. -/
theorem graphSubspace_eq_range (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] {X : E →L[𝕜] E}
    (hX : IsAngularOperator U X) :
    graphSubspace U X =
      LinearMap.range (projection U + X ∘L projection U).toLinearMap := by
  have hPX : ∀ y, projection U (X y) = 0 := fun y => by
    simpa using ContinuousLinearMap.ext_iff.mp hX.2 y
  have hidem : ∀ x, projection U (projection U x) = projection U x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  set T : E →L[𝕜] E := projection U + X ∘L projection U with hT
  have hPT : ∀ x, projection U (T x) = projection U x := by
    intro x
    simp only [hT, add_apply,
      ContinuousLinearMap.comp_apply, map_add]
    rw [hidem, hPX, add_zero]
  have hTP : ∀ x, T (projection U x) = T x := by
    intro x
    simp only [hT, add_apply,
      ContinuousLinearMap.comp_apply]
    rw [hidem]
  have hclosed :
      IsClosed ((LinearMap.range T.toLinearMap : Submodule 𝕜 E) : Set E) := by
    rw [← isSeqClosed_iff_isClosed]
    intro seq y hseq hlim
    have hfix : ∀ n, seq n = T (projection U (seq n)) := by
      intro n
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (hseq n)
      have hx' : T x = seq n := hx
      rw [← hx', hPT, hTP]
    have hlim2 : Filter.Tendsto seq Filter.atTop
        (nhds (T (projection U y))) := by
      refine Filter.Tendsto.congr (fun n => (hfix n).symm) ?_
      exact ((T ∘L projection U).continuous.tendsto y).comp hlim
    exact ⟨projection U y, (tendsto_nhds_unique hlim hlim2).symm⟩
  refine le_antisymm ?_ (Submodule.le_topologicalClosure _)
  exact Submodule.topologicalClosure_minimal _ le_rfl hclosed

/-- Closed formula for the projection onto a graph: with `A = P_U + X P_U`
the graph parametrization and `N = 1 + (X P_U)⋆ (X P_U)` the normal-equation
operator, the projection is `A N⁻¹ A⋆`.  The inverse is taken through
`Ring.inverse` so the definition is total in `X`; for an angular operator `N`
is coercive, `Ring.inverse` is a genuine inverse, and the formula is the
orthogonal projection onto the graph subspace
(`projection_graphSubspace_formula`). -/
noncomputable def graphProjectionFormula
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) : E →L[𝕜] E :=
  (projection U + X * projection U) *
    Ring.inverse (1 + star (X * projection U) * (X * projection U)) *
    star (projection U + X * projection U)

/-! ### Basic consequences of `IsAngularOperator`

The definition gives `X P = X` and `P X = 0`.  The four facts below are what
every argument about the graph actually uses, and **both theorems in this
section derived all four inline**, so a third one would have derived them a
third time.  See `{lane:DK-LONGPROOF-8}`. -/

variable {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] {X : E →L[𝕜] E}

/-- `X` maps into `Uᗮ`, so its adjoint kills `U`. -/
theorem star_mul_projection_of_isAngularOperator (hX : IsAngularOperator U X) :
    star X * projection U = 0 := by
  have hPX : projection U * X = 0 := hX.2
  have h := congrArg star hPX
  rwa [star_mul, (isSelfAdjoint_starProjection U).star_eq, star_zero] at h

/-- Dually, `P` fixes the range of `X⋆`. -/
theorem projection_mul_star_of_isAngularOperator (hX : IsAngularOperator U X) :
    projection U * star X = star X := by
  have hXP : X * projection U = X := hX.1
  have h := congrArg star hXP
  rwa [star_mul, (isSelfAdjoint_starProjection U).star_eq] at h

/-- The graph denominator `1 + X⋆X` commutes with `P`. -/
theorem projection_commute_one_add_star_mul_self_of_isAngularOperator
    (hX : IsAngularOperator U X) :
    projection U * (1 + star X * X) = (1 + star X * X) * projection U := by
  have hXP : X * projection U = X := hX.1
  rw [mul_add, add_mul, mul_one, one_mul]
  congr 1
  calc projection U * (star X * X) = (projection U * star X) * X := by rw [mul_assoc]
    _ = star X * X := by rw [projection_mul_star_of_isAngularOperator hX]
    _ = star X * (X * projection U) := by rw [hXP]
    _ = (star X * X) * projection U := by rw [mul_assoc]

/-- The graph parametrisation `A = P + X` has `A⋆A = (1 + X⋆X) P`. -/
theorem star_mul_self_of_isAngularOperator (hX : IsAngularOperator U X) :
    star (projection U + X) * (projection U + X) =
      (1 + star X * X) * projection U := by
  have hPP : projection U * projection U = projection U :=
    (U.isIdempotentElem_starProjection).eq
  have hXP : X * projection U = X := hX.1
  have hPX : projection U * X = 0 := hX.2
  simp only [star_add, (isSelfAdjoint_starProjection U).star_eq, add_mul, mul_add, mul_add,
    hPP, hPX, star_mul_projection_of_isAngularOperator hX, add_mul, one_mul,
    mul_assoc, hXP, add_zero, zero_add]

/-- Projection onto a graph subspace in terms of the angular operator.

The proof avoids functional-calculus square roots entirely: with
`A = P + X` (`P = P_U`; angularity gives `X P = X`) and `N = 1 + X⋆X`, the
normal-equation operator `N` is coercive, hence a unit by the operator
Lax–Milgram lemma, and it commutes with `P`.  The candidate `Q = A N⁻¹ A⋆`
then satisfies `A⋆ A = N P` and `A⋆ Q = A⋆`, so for every `z` the vector
`Q z` lies on the graph while `z - Q z` is orthogonal to it; the
characterization of the orthogonal projection finishes the proof. -/
theorem projection_graphSubspace_formula
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : IsAngularOperator U X) :
    projection (graphSubspace U X) = graphProjectionFormula U X := by
  set P : E →L[𝕜] E := projection U with hPdef
  have hXP : X * P = X := hX.1
  have hPX : P * X = 0 := hX.2
  have hPP : P * P = P := (U.isIdempotentElem_starProjection).eq
  have hsP : star P = P := (isSelfAdjoint_starProjection U).star_eq
  have hsXP : star X * P = 0 := star_mul_projection_of_isAngularOperator hX
  have hPsX : P * star X = star X := projection_mul_star_of_isAngularOperator hX
  set A : E →L[𝕜] E := P + X * P with hAdef
  set N : E →L[𝕜] E := 1 + star (X * P) * (X * P) with hNdef
  set R : E →L[𝕜] E := Ring.inverse N with hRdef
  have hA : A = P + X := by rw [hAdef, hXP]
  have hN : N = 1 + star X * X := by rw [hNdef, hXP]
  have hformula : graphProjectionFormula U X = A * R * star A := rfl
  have hNcoer : ∀ z, (1 : ℝ) * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜 := by
    intro z
    have hNz : N z = z + star X (X z) := by rw [hN]; rfl
    have hinner : ⟪N z, z⟫_𝕜 = ⟪z, z⟫_𝕜 + ⟪X z, X z⟫_𝕜 := by
      rw [hNz, inner_add_left, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    rw [hinner, map_add, inner_self_eq_norm_sq, inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖X z‖]
  have hNunit : IsUnit N :=
    TauCeti.ContinuousLinearMap.isUnit_of_coercive one_pos hNcoer
  have hNR : N * R = 1 := Ring.mul_inverse_cancel N hNunit
  have hRN : R * N = 1 := Ring.inverse_mul_cancel N hNunit
  have hPN : P * N = N * P := by
    rw [hN]
    exact projection_commute_one_add_star_mul_self_of_isAngularOperator hX
  have hPR : P * R = R * P := TauCeti.ringInverse_semiconj hNunit hNunit hPN
  have hsA : star A = P + star X := by rw [hA, star_add, hsP]
  have hPsA : P * star A = star A := by rw [hsA, mul_add, hPP, hPsX]
  have hsAA : star A * A = N * P := by
    rw [hA, hN]
    exact star_mul_self_of_isAngularOperator hX
  have hsAQ : star A * (A * R * star A) = star A := by
    have h1 : star A * (A * R * star A) = (star A * A) * (R * star A) := by
      simp only [mul_assoc]
    simp only [h1, hsAA, mul_assoc N P (R * star A), ← mul_assoc P R (star A), hPR,
      mul_assoc R P (star A), hPsA, ← mul_assoc, hNR, one_mul]
  rw [hformula]
  refine ContinuousLinearMap.ext fun z => ?_
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [graphSubspace_eq_range U hX]
    exact ⟨R (star A z), rfl⟩
  · intro w hw
    rw [graphSubspace_eq_range U hX] at hw
    obtain ⟨y, hy⟩ := hw
    rw [← hy]
    show ⟪z - (A * R * star A) z, A y⟫_𝕜 = 0
    rw [inner_eq_zero_symm]
    have hadj :=
      ContinuousLinearMap.adjoint_inner_right A y (z - (A * R * star A) z)
    rw [← hadj, ← ContinuousLinearMap.star_eq_adjoint, map_sub]
    have happ : star A ((A * R * star A) z) = star A z := by
      have h := congrArg (fun T : E →L[𝕜] E => T z) hsAQ
      simpa using h
    rw [happ, sub_self, inner_zero_right]

-- Measured after the extractions below: 400000 fails, 800000 succeeds.  The
-- previous value was 1600000; heartbeats count allocations and are
-- deterministic, so this is a reproducible bound rather than a machine-
-- dependent one.
set_option maxHeartbeats 800000 in
/-- The operator-norm gap between a base subspace and the graph of an
angular operator has the exact value `‖X‖ / √(1 + ‖X‖ ^ 2)`.

Both one-sided blocks `P (1 - Q)` and `(1 - P) Q` of the projector
difference collapse, through the projection formula, to operators of the
shape `1 - (1 + B)⁻¹` with `B = X⋆X` respectively `B = X X⋆`, whose exact
norm `‖B‖ / (1 + ‖B‖)` is `norm_one_sub_inverse_one_add`; the `U`-blockwise
Pythagoras estimate then pins the full difference at the common value. -/
theorem norm_projection_sub_projection_graphSubspace
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : IsAngularOperator U X) :
    ‖projection U - projection (graphSubspace U X)‖
      = ‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2) := by
  set P : E →L[𝕜] E := projection U with hPdef
  have hXP : X * P = X := hX.1
  have hPX : P * X = 0 := hX.2
  have hPP : P * P = P := (U.isIdempotentElem_starProjection).eq
  have hsP : star P = P := (isSelfAdjoint_starProjection U).star_eq
  have hsXP : star X * P = 0 := star_mul_projection_of_isAngularOperator hX
  have hPsX : P * star X = star X := projection_mul_star_of_isAngularOperator hX
  set A : E →L[𝕜] E := P + X * P with hAdef
  set N : E →L[𝕜] E := 1 + star (X * P) * (X * P) with hNdef
  set R : E →L[𝕜] E := Ring.inverse N with hRdef
  have hA : A = P + X := by rw [hAdef, hXP]
  have hN : N = 1 + star X * X := by rw [hNdef, hXP]
  set M : E →L[𝕜] E := 1 + X * star X with hMdef
  set R' : E →L[𝕜] E := Ring.inverse M with hR'def
  have hQF : projection (graphSubspace U X) = A * R * star A :=
    projection_graphSubspace_formula U X hX
  -- units and inverses
  have hNunit : IsUnit N := by
    rw [hN]
    exact TauCeti.ContinuousLinearMap.isUnit_one_add_star_mul_self X
  have hMunit : IsUnit M := by
    have h := TauCeti.ContinuousLinearMap.isUnit_one_add_star_mul_self (star X)
    rwa [star_star, ← hMdef] at h
  have hNR : N * R = 1 := Ring.mul_inverse_cancel N hNunit
  have hRN : R * N = 1 := Ring.inverse_mul_cancel N hNunit
  have hMR' : M * R' = 1 := Ring.mul_inverse_cancel M hMunit
  have hR'M : R' * M = 1 := Ring.inverse_mul_cancel M hMunit
  -- self-adjointness of the inverse
  have hNsa : star N = N := by
    rw [hN, star_add, star_one, star_mul, star_star]
  -- `IsSelfAdjoint a` is by definition `star a = a`, so `hNsa` is already the
  -- hypothesis Mathlib's `IsSelfAdjoint.ringInverse` wants.
  have hRsa : star R = R := IsSelfAdjoint.ringInverse hNsa
  -- commutation of `P` with `N` and `R`
  have hPN : P * N = N * P := by
    rw [hN]
    exact projection_commute_one_add_star_mul_self_of_isAngularOperator hX
  have hPR : P * R = R * P := TauCeti.ringInverse_semiconj hNunit hNunit hPN
  -- graph parametrization algebra
  have hsA : star A = P + star X := by rw [hA, star_add, hsP]
  have hPA : P * A = P := by rw [hA, mul_add, hPP, hPX, add_zero]
  have hPsA : P * star A = star A := by rw [hsA, mul_add, hPP, hPsX]
  have hsAP : star A * P = P := by rw [hsA, add_mul, hPP, hsXP, add_zero]
  have hsAA : star A * A = N * P := by
    rw [hA, hN]
    exact star_mul_self_of_isAngularOperator hX
  -- the two one-sided blocks
  have hPQ : P * (A * R * star A) = R * star A := by
    calc P * (A * R * star A) = ((P * A) * R) * star A := by
          rw [← mul_assoc P (A * R) (star A), ← mul_assoc P A R]
      _ = (P * R) * star A := by rw [hPA]
      _ = (R * P) * star A := by rw [hPR]
      _ = R * (P * star A) := by rw [mul_assoc]
      _ = R * star A := by rw [hPsA]
  have h1PA : (1 - P) * A = X := by
    rw [sub_mul, one_mul, hPA, hA, add_sub_cancel_left]
  have hT2 : (1 - P) * (A * R * star A) = X * R * star A := by
    calc (1 - P) * (A * R * star A) = ((1 - P) * A) * (R * star A) := by
          rw [mul_assoc A R (star A), ← mul_assoc (1 - P) A (R * star A)]
      _ = X * (R * star A) := by rw [h1PA]
      _ = X * R * star A := by rw [mul_assoc]
  -- `1 - R = (X⋆X) R` absorbed on `P`, and the `T₁` square
  have h1RP : (1 - R) * P = 1 - R := by
    have hBR : (star X * X) * R = 1 - R := by
      have h1 : R + (star X * X) * R = 1 := by
        calc R + (star X * X) * R = (1 + star X * X) * R := by
              rw [add_mul, one_mul]
          _ = 1 := by rw [← hN, hNR]
      calc (star X * X) * R = (R + (star X * X) * R) - R := by abel
        _ = 1 - R := by rw [h1]
    calc (1 - R) * P = ((star X * X) * R) * P := by rw [hBR]
      _ = star X * (X * (R * P)) := by simp only [mul_assoc]
      _ = star X * (X * (P * R)) := by rw [← hPR]
      _ = star X * ((X * P) * R) := by rw [← mul_assoc X P R]
      _ = star X * (X * R) := by rw [hXP]
      _ = (star X * X) * R := by rw [← mul_assoc]
      _ = 1 - R := hBR
  have hT1sq : (P - R * star A) * star (P - R * star A) = 1 - R := by
    have hstarT1 : star (P - R * star A) = P - A * R := by
      rw [star_sub, hsP, star_mul, star_star, hRsa]
    rw [hstarT1]
    have hexp : (P - R * star A) * (P - A * R)
        = P - (R * P + R * P) + R * (N * P) * R := by
      rw [mul_sub, sub_mul, sub_mul]
      have e1 : P * P = P := hPP
      have e2 : P * (A * R) = P * R := by
        rw [← mul_assoc, hPA]
      have e3 : (R * star A) * P = R * P := by
        rw [mul_assoc, hsAP]
      have e4 : (R * star A) * (A * R) = R * (N * P) * R := by
        rw [mul_assoc R (star A) (A * R), ← mul_assoc (star A) A R, hsAA,
          ← mul_assoc R (N * P) R]
      rw [e1, e2, e3, e4, hPR]
      abel
    rw [hexp]
    have e5 : R * (N * P) * R = P * R := by
      rw [← mul_assoc R N P, hRN, one_mul, hPR]
    rw [e5, hPR]
    calc P - (R * P + R * P) + R * P = P - R * P := by abel
      _ = (1 - R) * P := by rw [sub_mul, one_mul]
      _ = 1 - R := h1RP
  -- intertwining and the `T₂` square
  have hXN : X * N = M * X := by
    -- The `rw` chain this replaced ran `← mul_assoc` then `mul_assoc`, two directed
    -- steps; to `simp only` they are one rule reaching a normal form, so the
    -- reversed copy is dead.
    simp only [hN, hMdef, mul_add, mul_one, add_mul, one_mul, mul_assoc]
  have hXR : X * R = R' * X := TauCeti.ringInverse_semiconj hNunit hMunit hXN
  have hRsAA : R * (star A * A) = P := by
    rw [hsAA, ← mul_assoc, hRN, one_mul]
  have hT2sq : (X * R * star A) * star (X * R * star A) = 1 - R' := by
    have hstarT2 : star (X * R * star A) = A * (R * star X) := by
      rw [star_mul, star_star, star_mul, hRsa]
    rw [hstarT2]
    have hcontract : R * (star A * (A * (R * star X))) = P * (R * star X) := by
      calc R * (star A * (A * (R * star X)))
          = R * ((star A * A) * (R * star X)) := by
            rw [← mul_assoc (star A) A (R * star X)]
        _ = (R * (star A * A)) * (R * star X) := by rw [← mul_assoc]
        _ = P * (R * star X) := by rw [hRsAA]
    calc (X * R * star A) * (A * (R * star X))
        = X * (R * (star A * (A * (R * star X)))) := by simp only [mul_assoc]
      _ = X * (P * (R * star X)) := by rw [hcontract]
      _ = (X * P) * (R * star X) := by rw [← mul_assoc]
      _ = X * (R * star X) := by rw [hXP]
      _ = (X * R) * star X := by rw [← mul_assoc]
      _ = (R' * X) * star X := by rw [hXR]
      _ = R' * (X * star X) := by rw [mul_assoc]
      _ = 1 - R' := by
          have h1 : R' + R' * (X * star X) = 1 := by
            calc R' + R' * (X * star X) = R' * (1 + X * star X) := by
                  rw [mul_add, mul_one]
              _ = 1 := by rw [← hMdef, hR'M]
          calc R' * (X * star X) = (R' + R' * (X * star X)) - R' := by abel
            _ = 1 - R' := by rw [h1]
  -- exact norms of the two inverse defects
  have hBsa : IsSelfAdjoint (star X * X) := IsSelfAdjoint.star_mul_self X
  have hBpos : ∀ z, 0 ≤ RCLike.re ⟪(star X * X) z, z⟫_𝕜 := by
    intro z
    have h : (star X * X) z = star X (X z) := rfl
    rw [h, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
    positivity
  have hB'sa : IsSelfAdjoint (X * star X) := IsSelfAdjoint.mul_star_self X
  have hB'pos : ∀ z, 0 ≤ RCLike.re ⟪(X * star X) z, z⟫_𝕜 := by
    intro z
    have h : (X * star X) z = X (star X z) := rfl
    rw [h, ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq]
    positivity
  have hnormB : ‖star X * X‖ = ‖X‖ * ‖X‖ := CStarRing.norm_star_mul_self
  have h1Rnorm : ‖(1 : E →L[𝕜] E) - R‖ = ‖X‖ ^ 2 / (1 + ‖X‖ ^ 2) := by
    have h := TauCeti.ContinuousLinearMap.norm_one_sub_inverse_one_add
      hBsa hBpos
    rw [← hN, ← hRdef, hnormB] at h
    rw [h]
    ring
  have h1R'norm : ‖(1 : E →L[𝕜] E) - R'‖ = ‖X‖ ^ 2 / (1 + ‖X‖ ^ 2) := by
    have h := TauCeti.ContinuousLinearMap.norm_one_sub_inverse_one_add
      hB'sa hB'pos
    rw [← hMdef, ← hR'def] at h
    have h2 : ‖X * star X‖ = ‖X‖ * ‖X‖ := CStarRing.norm_self_mul_star
    rw [h2] at h
    rw [h]
    ring
  -- the common norm value
  set g : ℝ := ‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2) with hgdef
  have hsq1 : (0 : ℝ) < 1 + ‖X‖ ^ 2 := by positivity
  have hgsq : g ^ 2 = ‖X‖ ^ 2 / (1 + ‖X‖ ^ 2) := by
    rw [hgdef, div_pow, Real.sq_sqrt hsq1.le]
  have hg0 : 0 ≤ g := by rw [hgdef]; positivity
  have hnorm_sq_eq : ∀ T : E →L[𝕜] E, ‖T * star T‖ = ‖T‖ ^ 2 := fun T => by
    have h : ‖T * star T‖ = ‖T‖ * ‖T‖ := CStarRing.norm_self_mul_star
    rw [h, pow_two]
  have hT1norm : ‖P - R * star A‖ = g := by
    have hsq : ‖P - R * star A‖ ^ 2 = g ^ 2 := by
      rw [← hnorm_sq_eq (P - R * star A), hT1sq, h1Rnorm, hgsq]
    exact (sq_eq_sq₀ (norm_nonneg _) hg0).mp hsq
  have hT2norm : ‖X * R * star A‖ = g := by
    have hsq : ‖X * R * star A‖ ^ 2 = g ^ 2 := by
      rw [← hnorm_sq_eq (X * R * star A), hT2sq, h1R'norm, hgsq]
    exact (sq_eq_sq₀ (norm_nonneg _) hg0).mp hsq
  -- identify the blocks with `P (1 - Q)` and `(1 - P) Q`
  set Q : E →L[𝕜] E := projection (graphSubspace U X) with hQdef
  have hQQ : ∀ x, Q (Q x) = Q x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr
      ((graphSubspace U X).starProjection_apply_mem x)
  have hQmem : ∀ x, Q x ∈ graphSubspace U X := fun x =>
    (graphSubspace U X).starProjection_apply_mem x
  have hT1opQ : P * (1 - Q) = P - R * star A := by
    rw [mul_sub, mul_one, hQF, hPQ]
  have hT2opQ : (1 - P) * Q = X * R * star A := by
    rw [hQF, hT2]
  -- Pythagoras upper bound
  have hbound : ∀ x, ‖(P - Q) x‖ ≤ g * ‖x‖ := by
    intro x
    have hu1mem : P (x - Q x) ∈ U := U.starProjection_apply_mem _
    have hu2mem : Q x - P (Q x) ∈ Uᗮ :=
      Submodule.sub_starProjection_mem_orthogonal (K := U) (Q x)
    have hdec : (P - Q) x = P (x - Q x) - (Q x - P (Q x)) := by
      simp only [sub_apply, map_sub]
      abel
    have horth : ⟪P (x - Q x), Q x - P (Q x)⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal hu1mem hu2mem
    have hpyth : ‖(P - Q) x‖ ^ 2
        = ‖P (x - Q x)‖ ^ 2 + ‖Q x - P (Q x)‖ ^ 2 := by
      rw [hdec, norm_sub_sq (𝕜 := 𝕜), horth]
      simp
    have hb1 : ‖P (x - Q x)‖ ≤ g * ‖x - Q x‖ := by
      have hQw : Q (x - Q x) = 0 := by
        rw [map_sub, hQQ x, sub_self]
      have h1 : (1 - Q) (x - Q x) = x - Q x := by
        show (x - Q x) - Q (x - Q x) = x - Q x
        rw [hQw, sub_zero]
      have happ : (P * (1 - Q)) (x - Q x) = P (x - Q x) := by
        calc (P * (1 - Q)) (x - Q x) = P ((1 - Q) (x - Q x)) := rfl
          _ = P (x - Q x) := by rw [h1]
      calc ‖P (x - Q x)‖ = ‖(P * (1 - Q)) (x - Q x)‖ := by rw [happ]
        _ ≤ ‖P * (1 - Q)‖ * ‖x - Q x‖ := ContinuousLinearMap.le_opNorm _ _
        _ = g * ‖x - Q x‖ := by rw [hT1opQ, hT1norm]
    have hb2 : ‖Q x - P (Q x)‖ ≤ g * ‖Q x‖ := by
      have happ : ((1 - P) * Q) (Q x) = Q x - P (Q x) := by
        show (1 - P) (Q (Q x)) = Q x - P (Q x)
        rw [hQQ x]
        rfl
      calc ‖Q x - P (Q x)‖ = ‖((1 - P) * Q) (Q x)‖ := by rw [happ]
        _ ≤ ‖(1 - P) * Q‖ * ‖Q x‖ := ContinuousLinearMap.le_opNorm _ _
        _ = g * ‖Q x‖ := by rw [hT2opQ, hT2norm]
    have hQorth : ⟪Q x, x - Q x⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hQmem x)
        (Submodule.sub_starProjection_mem_orthogonal
          (K := graphSubspace U X) x)
    have hxsq : ‖x‖ ^ 2 = ‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2 := by
      have hx : x = Q x + (x - Q x) := by abel
      calc ‖x‖ ^ 2 = ‖Q x + (x - Q x)‖ ^ 2 := by rw [← hx]
        _ = ‖Q x‖ ^ 2 + 2 * RCLike.re ⟪Q x, x - Q x⟫_𝕜 + ‖x - Q x‖ ^ 2 :=
            norm_add_sq (𝕜 := 𝕜) _ _
        _ = ‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2 := by
            rw [hQorth]
            simp
    have hfin : ‖(P - Q) x‖ ^ 2 ≤ (g * ‖x‖) ^ 2 := by
      have e1 : ‖P (x - Q x)‖ ^ 2 ≤ (g * ‖x - Q x‖) ^ 2 := by
        nlinarith [norm_nonneg (P (x - Q x)), hb1]
      have e2 : ‖Q x - P (Q x)‖ ^ 2 ≤ (g * ‖Q x‖) ^ 2 := by
        nlinarith [norm_nonneg (Q x - P (Q x)), hb2]
      calc ‖(P - Q) x‖ ^ 2
          = ‖P (x - Q x)‖ ^ 2 + ‖Q x - P (Q x)‖ ^ 2 := hpyth
        _ ≤ (g * ‖x - Q x‖) ^ 2 + (g * ‖Q x‖) ^ 2 := by linarith
        _ = g ^ 2 * (‖Q x‖ ^ 2 + ‖x - Q x‖ ^ 2) := by ring
        _ = g ^ 2 * ‖x‖ ^ 2 := by rw [← hxsq]
        _ = (g * ‖x‖) ^ 2 := by ring
    nlinarith [hfin, norm_nonneg ((P - Q) x), mul_nonneg hg0 (norm_nonneg x)]
  have hupper : ‖P - Q‖ ≤ g :=
    ContinuousLinearMap.opNorm_le_bound _ hg0 hbound
  -- lower bound through the factorization `P (1 - Q) = (P - Q)(1 - Q)`
  have hQQop : Q * Q = Q :=
    ((graphSubspace U X).isIdempotentElem_starProjection).eq
  have hfactor : (P - Q) * (1 - Q) = P * (1 - Q) := by
    rw [sub_mul, mul_sub, mul_sub, mul_one, mul_one, hQQop]
    abel
  have h1Qnorm : ‖(1 : E →L[𝕜] E) - Q‖ ≤ 1 := by
    have h := (graphSubspace U X)ᗮ.starProjection_norm_le
    rwa [Submodule.starProjection_orthogonal'] at h
  have hlower : g ≤ ‖P - Q‖ := by
    calc g = ‖P * (1 - Q)‖ := by rw [hT1opQ, hT1norm]
      _ = ‖(P - Q) * (1 - Q)‖ := by rw [hfactor]
      _ ≤ ‖P - Q‖ * ‖1 - Q‖ := norm_mul_le _ _
      _ ≤ ‖P - Q‖ * 1 := mul_le_mul_of_nonneg_left h1Qnorm (norm_nonneg _)
      _ = ‖P - Q‖ := mul_one _
  exact le_antisymm hupper hlower

                                                                        
                                      
                                 
                                                   
                                                  
                                                                        
                                                     


                         
                                                                     
                                                       
                                      
                                          
                                                     
                                                                 
                                                 
                
                                  
                                               
                                                         
                                                               
                                                         
                                        
                                                                         
                                                
                                                 
               
                                            
           

                                                                            
                                                        
                                              
                                                     
                                                                               
                                     
                                                                                    
                

                                                          
                                         
                                                     
                                                                 
                                                           
                         
                                                                                          
                                              
                                              
                                                                
                                                     
                                                
                                                                           
                                                                   
                                                                   
                                                                           
                                   
                                                   
                                                    
                                   
                                        
                
                                               
                                                                     
                                  
                                                                        
                                 
                                                    
                                                               
                                                                      
                              
            
                                                            
                              
             
                                       
                                                          
                                                          
                                          
                                                
                                      
                                              
                       
                                
                                                                           
                                
                                                          
                                                                               
                                            
                                                                               
                                       
                                                                                 
                                       
                                             
                                                             
                                             
                                      
                                         
                                       
                                                        
                                                
                                       
                                      
                 
                                  
                                                               
                              
                                      
                                                             
                                          
                                              
                    
                                           
                                                                  
                       
                                                
                                                                                         
                                                    
                                                       
                                             
        
                       
              
             
              
             
                                                                         
                                                                                
                  
                 
             
                
            
                            
                
                                                
                                         
                                                   
                    
                                      
                        
                                             
                              
                            
                                          
                                                                    
                                     
                       
                          
                                        

                                                                                  
                                                                      
                                                             
                          
                                              
                                                                                
             
                
                                                                 
                                                         
                         
                                          
             
                                                 
             
                                                      
                                                      
                                         
                          
                                                                           
                                      
                                                           
                                                           
                                              
               
              

                                                                              
                                    
                                                     
                                                                 
                     
                                                         
                               
                                                            
                                                                              
                                                                           
                             
                                       
                      
                             
                                                         
                                                          
                                                         
                                                          
                  
                                                                        
                                                                              
                                                             
                                                                 
             
                                                       
                                                                              
                      
                      
                            
                                                      
                                                   
                                                         
                                                            
                      
                                      
         
        
                                    
                                                      
                                     
                                                                  

                                                                          
                                                                          
                                                
                                                   
                                                  
                                                             
                                               
                                                    
                                                                        
                                          
                                                                               
                                      
                                                                 
              
        
                                     
            

                                                                    
           
                                       
                                                   
                                                  
                                                                    
                                               
                                                    
                                                                        
                         
                                                               
                               
                                                                                 
             
                                                                     
                                                                                 
                                      
                                                                       
               
              
                         
                                                                          
                                             
                                                         
                                                          
                                                                  
               
              
               
                                                     
                                                  
                                                          
            
                                                        
             
           
                                                                                
                                                                        
                               
                              
           
                                                                                
                              
                                                                             
                             

end DavisKahanExt
end TauCeti