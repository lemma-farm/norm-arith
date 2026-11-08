-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Statements.FlowDefs.FlowIsFlow
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Statements.FlowDefs.FlowInv
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Construction.LimitFieldBounds
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Construction.ExplicitBarNorm
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Construction.LimitFieldRegularity
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Construction.Scalars
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Ingredients.TimeScaleBounds
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.Liouville
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.SpatialRegularity
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Flow.InverseC1
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Section3.CorrectorBounds
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Section4.LocalFinite
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Time regularity ingredients for the limit stream.

The flow/material estimates of §2 are carried as explicit source-form data;
the recursion estimate differentiates the finite-overlap stream update and
then applies the mean-value theorem in time.
-/
@[expose] public section
open MeasureTheory Homogenization Filter Topology
open scoped ContDiff
noncomputable section
namespace AVenhance
/-- The canonical smooth periodic flow associated with one member of a stream
sequence. -/
noncomputable def constructionFlow {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ) :
    ℝ → Vec 2 → ℝ → Vec 2 := by
  let hφ := streamSeq_isAdmissible hseq m
  exact flow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
/-- The inverse-flow map for `constructionFlow`, with arguments ordered as in
the `flowInv`. -/
noncomputable def constructionFlowInv {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ) :
    ℝ → Vec 2 → ℝ → Vec 2 := by
  let hφ := streamSeq_isAdmissible hseq m
  exact flowInv (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
/-- The spatial Jacobian of the `m`th flow at offset `t` from start time `s`. -/
noncomputable def constructionFlowJacobian {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ)
    (t s : ℝ) (x : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y : Vec 2 => constructionFlow hseq m (s + t) y s) x
/-- The spatial Jacobian of the inverse flow at offset `t` from start time `s`. -/
noncomputable def constructionFlowInvJacobian {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ)
    (t s : ℝ) (x : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y : Vec 2 => constructionFlowInv hseq m (s + t) y s) x
/-- The forward spatial Jacobian pulled back by its inverse, as in
`c.material.DX.Xinv` and `c.flowreg` display 2. -/
noncomputable def constructionComposedFlowJacobian {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ)
    (s r : ℝ) (x : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  constructionFlowJacobian hseq m r s
    (constructionFlowInv hseq m (s + r) x s)
/-- Componentwise version of the source spatial seminorm for a matrix field.
Each entry is measured by the scalar `barNorm`. -/
def flowJacobianBarNorm (n : ℕ) (R : ℝ)
    (J : Vec 2 → Vec 2 →L[ℝ] Vec 2) : ENNReal :=
  ⨆ i : Fin 2, ⨆ j : Fin 2,
    barNorm n R (fun x : Vec 2 => J x (basisVec j) i)
/-- One material derivative along a time-dependent vector field, matching
`D_{t,m} = ∂ₜ + b_m·∇` in the source. -/
def constructionMaterialDerivative (b : ℝ → Vec 2 → Vec 2)
    (F : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ :=
  fun t x => deriv (fun r : ℝ => F r x) t + fderiv ℝ (F t) x (b t x)
/-- Iterates of the source material derivative. -/
def constructionMaterialIterate (b : ℝ → Vec 2 → Vec 2) :
    ℕ → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ
  | 0, F => F
  | n + 1, F => constructionMaterialDerivative b (constructionMaterialIterate b n F)
/-- Explicit source-form flow and material bounds used in the differentiated
stream recursion. The seminorm fields transcribe e.Xm.regbounds and all four
displays of c.flowreg componentwise; `material_jacobian` transcribes
c.material.DX.Xinv. The final field records e.PDE.backwards for the inverse
flow. -/
structure FlowBoundsData {β : ℝ} (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsStreamSeq I Φ) (Cmat : ℝ) : Prop where
  /-- The source constant in c.material.DX.Xinv is at least one. -/
  material_constant_ge_one : 1 ≤ Cmat
  /-- e.Xm.regbounds, componentwise for every derivative order n. -/
  inverse_regbounds : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ,
      flowJacobianBarNorm n (2 ^ 11 * (epsilon β I.Λ m)⁻¹)
        (fun x => constructionFlowInvJacobian hseq m t s x -
          ContinuousLinearMap.id ℝ (Vec 2))
        ≤ ENNReal.ofReal (2 ^ 23 * |t| * a β I.Λ m)
  /-- c.flowreg display e.Xm.bound.1. -/
  flow_close : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ x : Vec 2,
      ‖constructionFlowJacobian hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
        2 ^ 23 * |t| * a β I.Λ m ∧
      2 ^ 23 * |t| * a β I.Λ m ≤ 1 / 4
  /-- c.flowreg display e.Xm.bound.2. -/
  flow_jacobian_composed : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ,
      flowJacobianBarNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
        (fun x => constructionComposedFlowJacobian hseq m s t x -
          ContinuousLinearMap.id ℝ (Vec 2))
        ≤ ENNReal.ofReal 40
  /-- Smooth spatial representative used to evaluate the essential-supremum
  seminorm bounds pointwise. This is qualitative flow regularity from §2. -/
  composed_jacobian_smooth : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ →
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 =>
        constructionComposedFlowJacobian hseq m s t x)
  /-- c.flowreg display e.Xm.bound.3. -/
  flow_jacobian : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
      flowJacobianBarNorm n (2 ^ 14 * (epsilon β I.Λ m)⁻¹)
        (constructionFlowJacobian hseq m t s) ≤ ENNReal.ofReal 12
  /-- Corrected c.flowreg derivative bound. The printed radius coefficient
  `2^13` fails at order seven (checked against the source); `Scalars.flow_derivative_bound`
  proves the corresponding conversion with `2^14`. -/
  flow_higher_derivative : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
      ∀ x : Vec 2, ∀ J : Fin n → Fin 2,
      ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
        constructionFlow hseq m (s + t) y s) x (fun k => basisVec (J k))‖ ≤
          2 * n.factorial * (2 ^ 14 * (epsilon β I.Λ m)⁻¹) ^ (n - 1)
  /-- c.material.DX.Xinv, in its pointwise derivative form. -/
  material_jacobian : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n ell : ℕ,
      n + ell ≤ Nstar β → ∀ i j : Fin 2, ∀ x : Vec 2,
        ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n
          (fun y => constructionMaterialIterate
            (fun r z => streamVel (Φ m) (s + r) z) ell
            (fun r z => constructionComposedFlowJacobian hseq m s r z
              (basisVec j) i) t y)
          x (fun k => basisVec (J k))‖ ≤
          Cmat * (epsilon β I.Λ m)⁻¹ ^ n *
            (epsilon β I.Λ m ^ (β - 2)) ^ ell
  /-- Classical differentiability in target time of the entries appearing in
  c.material.DX.Xinv; this is the regularity implicit in that display's
  partial-time derivatives. -/
  material_jacobian_time_diff : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ i j : Fin 2, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => constructionComposedFlowJacobian hseq m s r x (basisVec j) i) t
  /-- Classical target-time differentiability of the spatial inverse-flow
  Jacobian. This is the mixed regularity needed when differentiating the
  inverse transport equation in space. -/
  inverse_jacobian_time_diff : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => constructionFlowInvJacobian hseq m r s x) t
  /-- e.PDE.backwards for each stream flow. -/
  inverse_transport : ∀ m : ℕ, 1 ≤ m → ∀ t s : ℝ, ∀ x : Vec 2,
    HasDerivAt (fun r : ℝ => constructionFlowInv hseq m r x s)
      (-(constructionFlowInvJacobian hseq m (t - s) s x)
        (streamVel (Φ m) t x)) t
end AVenhance
