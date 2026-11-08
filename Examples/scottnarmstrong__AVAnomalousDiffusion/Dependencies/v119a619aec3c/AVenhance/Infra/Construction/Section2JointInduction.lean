-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Construction.RecursionIncrement
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Construction.FlowTransport
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The analytic induction behind the first stream-regularity increment estimate. -/
@[expose] public section
open MeasureTheory Homogenization Topology
open scoped ContDiff
noncomputable section
namespace AVenhance.Infra.Construction
structure Section2FlowBoundsAtScale {β : ℝ} (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsStreamSeq I Φ) (Cmat : ℝ)
    (m : ℕ) : Prop where
  inverse_regbounds : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ,
    flowJacobianBarNorm n (2 ^ 11 * (epsilon β I.Λ m)⁻¹)
      (fun x => constructionFlowInvJacobian hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)) ≤
      ENNReal.ofReal (2 ^ 23 * |t| * a β I.Λ m)
  flow_close : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ x : Vec 2,
      ‖constructionFlowJacobian hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 2 ^ 23 * |t| * a β I.Λ m ∧
      2 ^ 23 * |t| * a β I.Λ m ≤ 1 / 4
  flow_jacobian_composed : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ,
    flowJacobianBarNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
      (fun x => constructionComposedFlowJacobian hseq m s t x -
        ContinuousLinearMap.id ℝ (Vec 2)) ≤ ENNReal.ofReal 40
  composed_jacobian_smooth : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ →
    ContDiff ℝ (⊤ : ℕ∞) (fun x => constructionComposedFlowJacobian hseq m s t x)
  flow_jacobian : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
    flowJacobianBarNorm n (2 ^ 14 * (epsilon β I.Λ m)⁻¹)
      (constructionFlowJacobian hseq m t s) ≤ ENNReal.ofReal 12
  flow_higher_derivative : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
    ∀ x : Vec 2, ∀ J : Fin n → Fin 2,
      ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
        constructionFlow hseq m (s + t) y s) x (fun k => basisVec (J k))‖ ≤
          2 * n.factorial * (2 ^ 14 * (epsilon β I.Λ m)⁻¹) ^ (n - 1)
  material_jacobian : ∀ s t : ℝ,
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
  material_jacobian_time_diff : ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ i j : Fin 2, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => constructionComposedFlowJacobian hseq m s r x (basisVec j) i) t
  inverse_jacobian_time_diff : ∀ s t : ℝ, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => constructionFlowInvJacobian hseq m r s x) t
end AVenhance.Infra.Construction
