module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Examples.Example_d204755c60f5d83ec67d_StationaryJetComparison ====
set_option autoImplicit false
set_option backward.privateInPublic true
@[expose] public section
/-! Quantitative comparison of the genuine first two stationary jets.  The
input errors concern the actual Jacobians of the two gradient maps at their
selected graph points. Scalar-potential errors and a fixed fourth-jet bound
can supply these errors by a mean-value estimate. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
variable {Θ E : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 64


set_option linter.unusedVariables false in
private theorem norm_bilinear_difference_le {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (M N : X→L[ℝ] X→L[ℝ] Y) (a b c d : X) {η A K e : ℝ}
    (hη : 0≤η) (hA : 0≤A) (hK : 0≤K) (he : 0≤e)
    (hMN : ‖M-N‖ ≤ η) (hN : ‖N‖ ≤ K)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ A) (hc : ‖c‖ ≤ A) (hd : ‖d‖ ≤ A)
    (hac : ‖a-c‖ ≤ e) (hbd : ‖b-d‖ ≤ e) 
    (h_DepthPaper_norm_curried_bilinear_apply_le : ∀ {X Y : Type u_3} {Z : Type u_4} [inst : NormedAddCommGroup X] [inst_1 : NormedSpace ℝ X]
      [inst_2 : NormedAddCommGroup Y] [inst_3 : NormedSpace ℝ Y] [inst_4 : NormedAddCommGroup Z]
      [inst_5 : NormedSpace ℝ Z] (M : X →L[ℝ] Y →L[ℝ] Z) (x : X) (y : Y),
      ‖((M : X → Y →L[ℝ] Z) x : Y → Z) y‖ ≤ ‖M‖ * ‖x‖ * ‖y‖)
    :
    ‖M a b-N c d‖ ≤ η*A^2+2*K*A*e := by
  have hid : M a b-N c d=(M-N) a b+N (a-c) b+N c (b-d) := by
    simp only [sub_apply,map_sub]
    abel
  rw [hid]
  apply (norm_add_le _ _).trans
  have hleft := (norm_add_le _ _).trans (add_le_add
    ((h_DepthPaper_norm_curried_bilinear_apply_le _ _ _).trans
      (mul_le_mul (mul_le_mul hMN ha (norm_nonneg _) hη) hb (norm_nonneg _) (mul_nonneg hη hA)))
    ((h_DepthPaper_norm_curried_bilinear_apply_le _ _ _).trans
      (mul_le_mul (mul_le_mul hN hac (norm_nonneg _) hK) hb (norm_nonneg _) (mul_nonneg hK he))))
  have hright := (h_DepthPaper_norm_curried_bilinear_apply_le N c (b-d)).trans
    (mul_le_mul (mul_le_mul hN hc (norm_nonneg _) hK) hbd (norm_nonneg _) (mul_nonneg hK hA))
  have hh := add_le_add hleft hright
  convert hh using 1 <;> ring

end DepthPaper
