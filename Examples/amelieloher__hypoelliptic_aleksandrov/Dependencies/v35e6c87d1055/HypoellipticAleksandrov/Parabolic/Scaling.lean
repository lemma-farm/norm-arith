module
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Parabolic.LocalClassical
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Parabolic affine scaling

This file records the exact translation and parabolic-dilation identities for
the forward time--velocity operator.  The affine map itself is defined in
`HarnackGeometry`; this module supplies its differential and the induced local
classical pullback API.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Filter Set
open scoped MatrixOrder Topology
theorem contDiff_infty_parabolicAffine {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d)
    (r : ℝ) : ContDiff ℝ (⊤ : WithTop ℕ∞) (parabolicAffine t₀ v₀ r) := by
  change ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z : TimeVelocity d ↦
    (t₀ + r ^ 2 * z.1, v₀ + r • z.2))
  fun_prop
end HypoellipticAleksandrov.Parabolic
