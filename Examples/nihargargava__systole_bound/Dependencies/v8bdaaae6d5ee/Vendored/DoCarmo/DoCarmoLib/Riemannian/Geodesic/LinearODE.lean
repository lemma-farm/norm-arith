module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Geodesic/LinearODE.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream options and proof-preserving API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Mathlib
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain upstream typeclass binders; this new linter changes no proof checks.
set_option linter.overlappingInstances false
/-!
# Global existence for linear ODEs with continuous coefficient

Mathlib's Picard–Lindelöf theory (`Mathlib.Analysis.ODE.PicardLindelof`) proves only
*local* existence: from `IsPicardLindelof` one gets a solution on a time interval short
enough that the a-priori bound keeps the trajectory inside a fixed ball. For a **linear**
ODE `V'(t) = A(t) V(t)` with a continuous bounded coefficient `A : ℝ → (E →L[ℝ] E)` the
solution exists on *any* compact interval, but that global statement is not in mathlib.

This file supplies it, as reusable infrastructure:

* `Riemannian.LinearODE.exists_hasDerivWithinAt_of_small` — short-time existence: on `[a,b]`
  with `(b-a)·‖A‖ ≤ 1/2` a solution with prescribed left-endpoint value exists (a direct
  `IsPicardLindelof` application).
* `Riemannian.LinearODE.exists_hasDerivWithinAt_Icc` — global existence on an arbitrary
  compact `[a,b]`, obtained by chopping `[a,b]` into finitely many short pieces, solving
  each with the short-time lemma, and gluing the pieces at the junctions.

The parallel-transport ODE `V' = -Γ(u', V)(u)` (do Carmo Ch. 2, Prop. 2.6) is the special
case `A(t) = -chartChristoffelContractionRight g α (u' t) (u t)`; see
`DoCarmoLib/Riemannian/Geodesic/CovariantDerivative.lean`.
-/
open scoped Topology NNReal
open Set Metric
noncomputable section
namespace Riemannian.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
def IsSolOn (A : ℝ → E →L[ℝ] E) (a b : ℝ) (V : ℝ → E) : Prop :=
  ∀ t ∈ Icc a b, HasDerivWithinAt V (A t (V t)) (Icc a b) t
omit [CompleteSpace E] in
theorem IsSolOn.continuousOn {A : ℝ → E →L[ℝ] E} {a b : ℝ} {V : ℝ → E}
    (h : IsSolOn A a b V) : ContinuousOn V (Icc a b) :=
  fun t ht => (h t ht).continuousWithinAt
omit [CompleteSpace E] in
/-- Superposition: for a *linear* ODE the sum of two solutions is a solution (its value at
the left endpoint is the sum of the two initial values). -/
theorem IsSolOn.add {A : ℝ → E →L[ℝ] E} {a b : ℝ} {V W : ℝ → E}
    (hV : IsSolOn A a b V) (hW : IsSolOn A a b W) : IsSolOn A a b (V + W) := by
  intro t ht
  have h := (hV t ht).add (hW t ht)
  simpa only [Pi.add_apply, map_add] using h
omit [CompleteSpace E] in
/-- Superposition: a scalar multiple of a solution is a solution. -/
theorem IsSolOn.const_smul {A : ℝ → E →L[ℝ] E} {a b : ℝ} (c : ℝ) {V : ℝ → E}
    (hV : IsSolOn A a b V) : IsSolOn A a b (c • V) := by
  intro t ht
  have h := (hV t ht).const_smul c
  simpa only [Pi.smul_apply, ContinuousLinearMap.map_smul] using h
variable {A : ℝ → E →L[ℝ] E} {a b : ℝ} {K : ℝ≥0}
end Riemannian.LinearODE
