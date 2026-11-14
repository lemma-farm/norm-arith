module

public import Mathlib
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Choose
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Separation.Regular
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.Sobolev.WeakGradient ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# The actual weak-gradient graph

Spatial coordinates use the usual finite product, with its sup norm. Gradient
energy will use the sum of squared coordinate L2 norms, not that sup norm.
The graph below imposes the distributional derivative identity against every
smooth function compactly supported in the open domain. It does not assume
an abstract space has the properties of a Sobolev space.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
namespace SubdiffusiveProcess
noncomputable section
abbrev SpatialCoordinates (d : ℕ) := Fin d → ℝ
abbrev DomainL2 {d : ℕ} (Ω : Opens (SpatialCoordinates d)) :=
  Lp ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))
abbrev SobolevData {d : ℕ} (Ω : Opens (SpatialCoordinates d)) :=
  DomainL2 Ω × (Fin d → DomainL2 Ω)
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- A smooth compactly supported test, as an actual scalar L2 equivalence class. -/
noncomputable def testL2 (φ : 𝓓(Ω, ℝ)) : DomainL2 Ω :=
  (φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ
/-- The coordinate derivative of a test is also an actual L2 function. -/
noncomputable def testPartialL2 (φ : 𝓓(Ω, ℝ)) (i : Fin d) : DomainL2 Ω :=
  ((φ.contDiff.continuous_fderiv_apply (by simp)).comp
    (continuous_id.prodMk continuous_const) |>.memLp_of_hasCompactSupport
      (φ.hasCompactSupport.fderiv_apply ℝ (Pi.single i 1))).toLp
    (fun x => fderiv ℝ φ x (Pi.single i 1))
noncomputable def weakGradientTest (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    SobolevData Ω →L[ℝ] ℝ :=
  ((innerSL ℝ (testL2 φ)).comp
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _))) +
  ((innerSL ℝ (testPartialL2 φ i)).comp (ContinuousLinearMap.fst ℝ _ _))
/-- The graph of weak first derivatives on the open domain. -/
noncomputable def weakSobolevGraph (Ω : Opens (SpatialCoordinates d)) :
    Submodule ℝ (SobolevData Ω) :=
  ⨅ (φ : 𝓓(Ω, ℝ)) (i : Fin d), LinearMap.ker (weakGradientTest φ i).toLinearMap
end
end SubdiffusiveProcess

end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.Sobolev.GradientRange ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Closed gradient ranges and volume loads

Only the finite tuple of scalar L2 spaces receives a Hilbert norm. Spatial
coordinates retain their ordinary product norm; no vector-valued Lp coercion
through a Euclidean-space wrapper occurs. The Poincare estimate below is an
explicit foundational input on a concrete closed subspace of the weak graph.
It is not a model convergence or regularity assumption.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- Coordinatewise square-integrable gradients, with the sum-of-squares Hilbert norm. -/
abbrev HilbertGradient (Ω : Opens (SpatialCoordinates d)) :=
  PiLp 2 (fun _ : Fin d => DomainL2 Ω)
/-- The actual coordinate gradient projection from function/gradient data. -/
def sobolevGradient : SobolevData Ω →L[ℝ] HilbertGradient Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => DomainL2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.snd ℝ _ _)
def subspaceGradient (V : Submodule ℝ (SobolevData Ω)) : V →L[ℝ] HilbertGradient Ω :=
  sobolevGradient.comp V.subtypeL

/-- L2 volume pairing on actual function/gradient data. -/
def sobolevVolumeLoad (f : DomainL2 Ω) : SobolevData Ω →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (ContinuousLinearMap.fst ℝ _ _)
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.Variational.WeightedL2 ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Weighted integral forms on vector fields

The bilinear form is the actual integral of a bounded scalar weight times
the pointwise inner product. With base measure A dx and vectors equal to
Sobolev gradients this is the finite-cutoff energy. The identification of
the admissible Sobolev gradient spaces is a separate obligation.
-/
open MeasureTheory InnerProductSpace Filter
open scoped ENNReal
namespace SubdiffusiveProcess
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The actual integral form on square-integrable vector fields with a bounded scalar weight. -/
noncomputable def weightedL2Form (a : Lp ℝ ∞ μ) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ →L[ℝ] ℝ :=
  (innerSL ℝ).comp ((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holderL μ ∞ 2 2 a)

end SubdiffusiveProcess

end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.Sobolev.WeightedGradient ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# The finite-cutoff coefficient form on actual gradients

The energy is the sum of the coordinate weighted L2 pairings. Thus it is
exactly the scalar coefficient times the Euclidean dot product of weak
gradients, with no factor 1/2. Positive bounded coefficients and Poincare
on a concrete closed variation space give the actual volume-source equation.
-/
open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- Sum of scalar coordinate energies, on the Hilbert space of gradients. -/
def weightedGradientForm (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    HilbertGradient Ω →L[ℝ] HilbertGradient Ω →L[ℝ] ℝ :=
  ∑ i : Fin d, (weightedL2Form (E := ℝ) a).bilinearComp (PiLp.proj 2 _ i) (PiLp.proj 2 _ i)

end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.Sobolev.ResponseSpace ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Concrete spaces and coefficients for finite responses

The space is a closed subspace of the actual distributional H1 graph,
with ordinary Poincare stated explicitly. The coefficient is an actual L∞
class bounded away from zero. No response or limiting theorem is a field.
-/
open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- A concrete Sobolev variation space on which ordinary Poincare holds. -/
structure ResponseSpace (Ω : Opens (SpatialCoordinates d)) where
  space : Submodule ℝ (SobolevData Ω)
  le_weak : space ≤ weakSobolevGraph Ω
  closed : IsClosed (space : Set (SobolevData Ω))
  poincare : ∃ K : ℝ≥0, ∀ z : space,
    ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient space z‖
def PositiveCoefficient (Ω : Opens (SpatialCoordinates d)) :=
  {a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) //
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a x}
/-- The bilinear energy on the concrete Sobolev variation space. -/
def responseForm (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) :
    S.space →L[ℝ] S.space →L[ℝ] ℝ :=
  (weightedGradientForm a.val).bilinearComp (subspaceGradient S.space) (subspaceGradient S.space)

set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.existsUnique_responseForm_solution : ∀ {d : ℕ} {Ω : TopologicalSpace.Opens (SubdiffusiveProcess.SpatialCoordinates d)}
  (S : SubdiffusiveProcess.ResponseSpace Ω) (a : SubdiffusiveProcess.PositiveCoefficient Ω)
  (L : ↥S.space →L[ℝ] ℝ),
  ∃! u : ↥S.space,
    ∀ (v : ↥S.space),
      ((SubdiffusiveProcess.responseForm S a : ↥S.space → ↥S.space →L[ℝ] ℝ) u : ↥S.space → ℝ) v =
        (L : ↥S.space → ℝ) v
/-- The unique weak source solution; no fallback value is used. -/
def responseSolution (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) :
    S.space := Classical.choose (existsUnique_responseForm_solution S a L)

def inverseResponse (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) : ℝ :=
  responseForm S a (responseSolution S a L) (responseSolution S a L)

end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.VariationalResponses.LimitForm ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}
/-- `E(u)` of `eq:mfd-18`:
the dual energy of the killed inverse `G`. -/
def limitFormEnergy (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) : EReal :=
  ⨆ f : DomainL2 Q, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.Basic ====
public section
/-
# Closed symmetric forms and Dirichlet forms on `L²`

This file is the base of a self-contained, reusable Dirichlet-form library.  It
imports only Mathlib, uses no carrier of the ambient project, and is written so
that the directory `SubdiffusiveProcess/DirichletForm/` can be lifted into a
standalone Lake package without changes.
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Closed symmetric forms and Dirichlet forms

Let `m` be a measure on a measurable space `X`.  A **closed form** on `L²(X, m)`
is a densely defined, symmetric, nonnegative bilinear form `E` whose domain
`D(E)` is a submodule of `L²(X, m)` complete for the energy norm
`E₁(u) = E(u, u) + ‖u‖²`.  A **Dirichlet form** is a closed form on which the
unit contraction `t ↦ (t ⊓ 1) ⊔ 0` operates.

## Main definitions

* `SubdiffusiveProcess.DirichletForm.ClosedForm m`: a densely defined, symmetric, nonnegative,
  closed bilinear form on `L²(X, m)`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.energyInner`, `SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq`:
  the energy inner product `E₁(u, v) = E(u, v) + ⟪u, v⟫` and `E₁(u) = E₁(u, u)`.
* `SubdiffusiveProcess.DirichletForm.IsNormalContraction`: `T : ℝ → ℝ` with `T 0 = 0` and
  `|T s - T t| ≤ |s - t|`.
* `SubdiffusiveProcess.DirichletForm.unitTruncation`: the unit contraction `t ↦ (t ⊓ 1) ⊔ 0`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.OperatesOn`: `T` operates on `E`, i.e. `T ∘ u` stays
  in `D(E)` and does not increase the energy.
* `SubdiffusiveProcess.DirichletForm`: a closed form on which `unitTruncation` operates.
* `SubdiffusiveProcess.DirichletForm.HasNormalContractions`: the Fukushima–Oshima–Takeda statement
  that *every* normal contraction operates on a Dirichlet form.

## Implementation notes

The bilinear form is carried as a total function `Lp ℝ 2 m → Lp ℝ 2 m → ℝ`; every
axiom is restricted to the domain, so the values off the domain carry no
information.  This keeps statements free of subtype coercions and matches the
way a form defined by a dual (resolvent) expression is met in practice.

## References

* M. Fukushima, Y. Oshima, M. Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, 2nd edition, de Gruyter, 2011.
-/
open MeasureTheory Filter Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]
namespace SubdiffusiveProcess.DirichletForm

structure ClosedForm (m : Measure X) where
  /-- The form domain `D(E)`, a linear subspace of `L²(X, m)`. -/
  domain : Submodule ℝ (Lp ℝ 2 m)
  /-- The bilinear form `E(u, v)`.  Values outside `domain` carry no
  information: every axiom below is restricted to `domain`. -/
  form : Lp ℝ 2 m → Lp ℝ 2 m → ℝ
  /-- `D(E)` is dense in `L²(X, m)`. -/
  denseDomain : Dense (domain : Set (Lp ℝ 2 m))
  /-- `E(u, v) = E(v, u)`. -/
  form_symm : ∀ u ∈ domain, ∀ v ∈ domain, form u v = form v u
  /-- `E` is additive in its first argument. -/
  form_add_left : ∀ u ∈ domain, ∀ v ∈ domain, ∀ w ∈ domain,
    form (u + v) w = form u w + form v w
  /-- `E` is homogeneous in its first argument. -/
  form_smul_left : ∀ c : ℝ, ∀ u ∈ domain, ∀ v ∈ domain, form (c • u) v = c * form u v
  /-- `E(u, u) ≥ 0`. -/
  form_nonneg : ∀ u ∈ domain, 0 ≤ form u u
  /-- `E` is closed: `D(E)` is complete for the energy norm
  `E₁(u) = E(u, u) + ‖u‖²`. -/
  complete : ∀ u : ℕ → Lp ℝ 2 m, (∀ n, u n ∈ domain) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      form (u p - u q) (u p - u q) + ‖u p - u q‖ ^ 2 < ε) →
    ∃ w ∈ domain, Tendsto
      (fun n => form (u n - w) (u n - w) + ‖u n - w‖ ^ 2) atTop (𝓝 0)
namespace ClosedForm
variable {m : Measure X} (E : ClosedForm m)

end ClosedForm
end SubdiffusiveProcess.DirichletForm

namespace SubdiffusiveProcess.DirichletForm
variable {m : Measure X}
end SubdiffusiveProcess.DirichletForm

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.Energy ====
public section
/-
# The extended energy functional, the order on forms, and Mosco convergence
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Extended energy, order of forms, Mosco convergence

For a closed form `E` we extend `u ↦ E(u, u)` to all of `L²(X, m)` by `⊤`
outside the domain (`SubdiffusiveProcess.DirichletForm.ClosedForm.energy`).  This makes the domain
readable off the functional and lets the order of forms and Mosco convergence be
stated without side conditions.

## Main definitions

* `SubdiffusiveProcess.DirichletForm.ClosedForm.energy`: `E(u) ∈ EReal`, equal to `⊤` off `D(E)`.
* the `Preorder` on `ClosedForm m` given by `E ≤ F ↔ ∀ u, E(u) ≤ F(u)`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.LEWithConst`: `E ≤ C · F` on `D(F)`.
* `SubdiffusiveProcess.DirichletForm.TendstoWeakly`: weak convergence in `L²(X, m)`.
* `SubdiffusiveProcess.DirichletForm.MoscoConverges`: Mosco convergence (weak liminf bound and
  existence of a strong recovery sequence).

## References

* U. Mosco, *Composite media and asymptotic Dirichlet forms*, J. Funct. Anal.
  123 (1994).
-/
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
variable {X : Type*} [MeasurableSpace X] {m : Measure X}
namespace SubdiffusiveProcess.DirichletForm
namespace ClosedForm
open scoped Classical in
/-- The energy functional extended to all of `L²(X, m)` by `⊤` off the domain. -/
noncomputable def energy (E : ClosedForm m) (u : Lp ℝ 2 m) : EReal :=
  if u ∈ E.domain then (E.form u u : EReal) else ⊤
variable (E F : ClosedForm m)
set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem.{w_u_1} : ∀ {X : Type w_u_1} [inst : MeasurableSpace X] {m : MeasureTheory.Measure X}
  (E : SubdiffusiveProcess.DirichletForm.ClosedForm m) {u : ↥(MeasureTheory.Lp ℝ 2 m)},
  u ∈ E.domain → E.energy u = (↑(E.form u u) : EReal)

set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.mem_domain_of_energy_lt_top.{w_u_1} : ∀ {X : Type w_u_1} [inst : MeasurableSpace X] {m : MeasureTheory.Measure X}
  (E : SubdiffusiveProcess.DirichletForm.ClosedForm m) {u : ↥(MeasureTheory.Lp ℝ 2 m)},
  E.energy u < ⊤ → u ∈ E.domain

end ClosedForm
end SubdiffusiveProcess.DirichletForm

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_8dc26e31829e298e1c5e_ResponseTraceLimit ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-! Finite response witnesses pass to the form defined by a limiting killed inverse.
The energy estimate here bounds the total energy; it does not assert a localized
liminf theorem or construct the finite witnesses.
-/
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace SubdiffusiveProcess
set_option linter.unusedVariables false in
/-- A uniformly bounded response-energy sequence has a limit in the inverse-limit form domain. -/
theorem form_bound_of_response_limits
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hE : ∀ v, E.energy v = limitFormEnergy G v)
    (hresponse : ∀ f : DomainL2 Q,
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (𝓝 (inner ℝ f (G f))))
    (un : ℕ → S.space) (u : DomainL2 Q)
    (hL2 : Tendsto (fun n => (un n).val.1) atTop (𝓝 u))
    (K : ℝ) (hK : ∀ n, responseForm S (a n) (un n) (un n) ≤ K) 
    (h_SubdiffusiveProcess_quadraticDual_le_liminf_responseForm : ∀ {d : ℕ} {Ω : TopologicalSpace.Opens (SubdiffusiveProcess.SpatialCoordinates d)}
      (S : SubdiffusiveProcess.ResponseSpace Ω) (a : ℕ → SubdiffusiveProcess.PositiveCoefficient Ω)
      (G : ↥(SubdiffusiveProcess.DomainL2 Ω) →L[ℝ] ↥(SubdiffusiveProcess.DomainL2 Ω))
      (uN : ℕ → ↥S.space) (u : ↥(SubdiffusiveProcess.DomainL2 Ω)),
      (∀ (f : ↥(SubdiffusiveProcess.DomainL2 Ω)),
          Filter.Tendsto (fun (n : ℕ) ↦ Inner.inner ℝ f (↑(uN n) : SubdiffusiveProcess.SobolevData Ω).1)
            Filter.atTop (nhds (Inner.inner ℝ f u))) →
        (∀ (f : ↥(SubdiffusiveProcess.DomainL2 Ω)),
            Filter.Tendsto
              (fun (n : ℕ) ↦
                SubdiffusiveProcess.inverseResponse S (a n)
                  (SubdiffusiveProcess.sobolevVolumeLoad f ∘SL S.space.subtypeL))
              Filter.atTop
              (nhds
                (Inner.inner ℝ f
                  ((G : ↥(SubdiffusiveProcess.DomainL2 Ω) → ↥(SubdiffusiveProcess.DomainL2 Ω)) f)))) →
          ⨆ (f : ↥(SubdiffusiveProcess.DomainL2 Ω)),
              (↑(2 * Inner.inner ℝ f u -
                    Inner.inner ℝ f
                      ((G : ↥(SubdiffusiveProcess.DomainL2 Ω) → ↥(SubdiffusiveProcess.DomainL2 Ω)) f)) :
                EReal) ≤
            Filter.liminf
              (fun (n : ℕ) ↦
                (↑(((SubdiffusiveProcess.responseForm S (a n) : ↥S.space → ↥S.space →L[ℝ] ℝ) (uN n) :
                        ↥S.space → ℝ)
                      (uN n)) :
                  EReal))
              Filter.atTop)
    :
    u ∈ E.domain ∧ E.form u u ≤ K := by
  have hweak : ∀ f : DomainL2 Q,
      Tendsto (fun n => inner ℝ f (un n).val.1) atTop (𝓝 (inner ℝ f u)) := by
    intro f
    exact tendsto_const_nhds.inner hL2
  have hlower := h_SubdiffusiveProcess_quadraticDual_le_liminf_responseForm S a G un u hweak hresponse
  have hupper : E.energy u ≤ (K : EReal) := by
    rw [hE]
    exact hlower.trans ((liminf_le_liminf
      (Eventually.of_forall fun n => EReal.coe_le_coe_iff.mpr (hK n))).trans_eq
        (liminf_const (K : EReal)))
  have hu := E.mem_domain_of_energy_lt_top (hupper.trans_lt (EReal.coe_lt_top K))
  refine ⟨hu, ?_⟩
  rw [E.energy_of_mem hu] at hupper
  exact EReal.coe_le_coe_iff.mp hupper
end SubdiffusiveProcess
