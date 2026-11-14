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

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve88867d50b46.DepthPaper.ImplicitStationaryJets ====
public section
set_option autoImplicit false
set_option backward.privateInPublic true
@[expose] public section
/-! Actual first and second differentiated stationarity equations.  These
are identities for genuine smooth functions, rather than prescribed jets. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
variable {Θ E : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

def stationaryGraph (q : Θ→E) (θ : Θ) : Θ×E := (θ,q θ)

axiom stationary_second_equation
    {G : Θ×E→E→L[ℝ]ℝ} {q : Θ→E} {θ : Θ}
    (hG : ContDiffAt ℝ ∞ G (stationaryGraph q θ))
    (hq : ContDiffAt ℝ ∞ q θ)
    (heq : ∀ᶠu in 𝓝 θ,G (stationaryGraph q u)=0) (v w : Θ) :
    fderiv ℝ G (stationaryGraph q θ) (0,fderiv ℝ (fderiv ℝ q) θ v w)=
      -fderiv ℝ (fderiv ℝ G) (stationaryGraph q θ)
        (v,fderiv ℝ q θ v) (w,fderiv ℝ q θ w)
/-- Quantitative inversion of a coercive map into the continuous dual. -/
axiom coercive_linear_vector_bound (B : E→L[ℝ] E→L[ℝ]ℝ) {κ : ℝ}
    (hκ : 0<κ) (hB : ∀v:E,κ*‖v‖^2 ≤ B v v) (v : E) :
    ‖v‖ ≤ ‖B v‖/κ
axiom norm_curried_bilinear_apply_le {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (M : X→L[ℝ] Y→L[ℝ] Z) (x : X) (y : Y) :
    ‖M x y‖ ≤ ‖M‖*‖x‖*‖y‖
/-- A true first stationary jet is bounded by the inverse coercivity. -/
axiom stationary_first_norm_bound
    {G : Θ×E→E→L[ℝ]ℝ} {q : Θ→E} {θ : Θ} {κ : ℝ}
    (hG : ContDiffAt ℝ ∞ G (stationaryGraph q θ))
    (hq : ContDiffAt ℝ ∞ q θ)
    (heq : ∀ᶠu in 𝓝 θ,G (stationaryGraph q u)=0)
    (hκ : 0<κ)
    (hB : ∀z:E,κ*‖z‖^2 ≤ fderiv ℝ G (stationaryGraph q θ) (0,z) z) :
    ‖fderiv ℝ q θ‖ ≤ ‖fderiv ℝ G (stationaryGraph q θ)‖/κ
/-- The second stationary jet is obtained from the actual twice-differentiated
equation and has a uniform quantitative bound. -/
axiom stationary_second_norm_bound
    {G : Θ×E→E→L[ℝ]ℝ} {q : Θ→E} {θ : Θ} {κ D : ℝ}
    (hG : ContDiffAt ℝ ∞ G (stationaryGraph q θ))
    (hq : ContDiffAt ℝ ∞ q θ)
    (heq : ∀ᶠu in 𝓝 θ,G (stationaryGraph q u)=0)
    (hκ : 0<κ) (hD : 0≤D)
    (hB : ∀z:E,κ*‖z‖^2 ≤ fderiv ℝ G (stationaryGraph q θ) (0,z) z)
    (h1 : ‖fderiv ℝ G (stationaryGraph q θ)‖ ≤ D)
    (h2 : ‖fderiv ℝ (fderiv ℝ G) (stationaryGraph q θ)‖ ≤ D) :
    ‖fderiv ℝ (fderiv ℝ q) θ‖ ≤ D*(max 1 (D/κ))^2/κ
end DepthPaper

end
end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Examples.Example_7ed54fc39e40a6a41ced_StationaryJetComparison ====
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
private axiom tangent_norm_le {q : Θ→E} {θ : Θ} {A : ℝ}
    (hA : 1≤A) (hD : ‖fderiv ℝ q θ‖ ≤ A) {v : Θ} (hv : ‖v‖=1) :
    ‖(v,fderiv ℝ q θ v)‖ ≤ A
private axiom tangent_difference_norm_le {q r : Θ→E} {θ : Θ} {D : ℝ}
    (hD : ‖fderiv ℝ q θ-fderiv ℝ r θ‖ ≤ D) {v : Θ} (hv : ‖v‖=1) :
    ‖(v,fderiv ℝ q θ v)-(v,fderiv ℝ r θ v)‖ ≤ D
/-- Comparison of the true first derivatives; no implicit derivative formula
is supplied as an assumption. -/
axiom stationary_first_comparison
    {F G : Θ×E→E→L[ℝ]ℝ} {q r : Θ→E} {θ : Θ} {κ D η : ℝ}
    (hF : ContDiffAt ℝ ∞ F (stationaryGraph q θ))
    (hG : ContDiffAt ℝ ∞ G (stationaryGraph r θ))
    (hq : ContDiffAt ℝ ∞ q θ) (hr : ContDiffAt ℝ ∞ r θ)
    (heq : ∀ᶠu in 𝓝 θ,F (stationaryGraph q u)=0)
    (her : ∀ᶠu in 𝓝 θ,G (stationaryGraph r u)=0)
    (hκ : 0<κ) (hD : 0≤D) (hη : 0≤η)
    (hBF : ∀z:E,κ*‖z‖^2 ≤ fderiv ℝ F (stationaryGraph q θ) (0,z) z)
    (hBG : ∀z:E,κ*‖z‖^2 ≤ fderiv ℝ G (stationaryGraph r θ) (0,z) z)
    (hG1 : ‖fderiv ℝ G (stationaryGraph r θ)‖ ≤ D)
    (hdiff : ‖fderiv ℝ F (stationaryGraph q θ)-fderiv ℝ G (stationaryGraph r θ)‖ ≤ η) :
    ‖fderiv ℝ q θ-fderiv ℝ r θ‖ ≤ η*max 1 (D/κ)/κ
private axiom norm_bilinear_difference_le {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (M N : X→L[ℝ] X→L[ℝ] Y) (a b c d : X) {η A K e : ℝ}
    (hη : 0≤η) (hA : 0≤A) (hK : 0≤K) (he : 0≤e)
    (hMN : ‖M-N‖ ≤ η) (hN : ‖N‖ ≤ K)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ A) (hc : ‖c‖ ≤ A) (hd : ‖d‖ ≤ A)
    (hac : ‖a-c‖ ≤ e) (hbd : ‖b-d‖ ≤ e) :
    ‖M a b-N c d‖ ≤ η*A^2+2*K*A*e
/-- A genuine second-derivative comparison, derived by differentiating the
two stationarity equations twice. -/
theorem stationary_second_comparison
    {F G : Θ×E→E→L[ℝ]ℝ} {q r : Θ→E} {θ : Θ} {κ D η : ℝ}
    (hF : ContDiffAt ℝ ∞ F (stationaryGraph q θ))
    (hG : ContDiffAt ℝ ∞ G (stationaryGraph r θ))
    (hq : ContDiffAt ℝ ∞ q θ) (hr : ContDiffAt ℝ ∞ r θ)
    (heq : ∀ᶠu in 𝓝 θ,F (stationaryGraph q u)=0)
    (her : ∀ᶠu in 𝓝 θ,G (stationaryGraph r u)=0)
    (hκ : 0<κ) (hD : 0≤D) (hη : 0≤η)
    (hBF : ∀z:E,κ*‖z‖^2 ≤ fderiv ℝ F (stationaryGraph q θ) (0,z) z)
    (hBG : ∀z:E,κ*‖z‖^2 ≤ fderiv ℝ G (stationaryGraph r θ) (0,z) z)
    (hF1 : ‖fderiv ℝ F (stationaryGraph q θ)‖ ≤ D)
    (hG1 : ‖fderiv ℝ G (stationaryGraph r θ)‖ ≤ D)
    (hG2 : ‖fderiv ℝ (fderiv ℝ G) (stationaryGraph r θ)‖ ≤ D)
    (hdiff1 : ‖fderiv ℝ F (stationaryGraph q θ)-fderiv ℝ G (stationaryGraph r θ)‖ ≤ η)
    (hdiff2 : ‖fderiv ℝ (fderiv ℝ F) (stationaryGraph q θ)-
      fderiv ℝ (fderiv ℝ G) (stationaryGraph r θ)‖ ≤ η) :
    ‖fderiv ℝ (fderiv ℝ q) θ-fderiv ℝ (fderiv ℝ r) θ‖ ≤
      η*(max 1 (D/κ))^2/κ*(1+3*D/κ) := by
  let L := fderiv ℝ F (stationaryGraph q θ)
  let N := fderiv ℝ G (stationaryGraph r θ)
  let M := fderiv ℝ (fderiv ℝ F) (stationaryGraph q θ)
  let P := fderiv ℝ (fderiv ℝ G) (stationaryGraph r θ)
  let A := max 1 (D/κ)
  have hA : 0≤A := (show (0:ℝ)≤1 by norm_num).trans (le_max_left _ _)
  have hq1 := (stationary_first_norm_bound hF hq heq hκ hBF).trans
    (div_le_div_of_nonneg_right hF1 hκ.le)
  have hr1 := (stationary_first_norm_bound hG hr her hκ hBG).trans
    (div_le_div_of_nonneg_right hG1 hκ.le)
  have hr2 := stationary_second_norm_bound hG hr her hκ hD hBG hG1 hG2
  have hfirst := stationary_first_comparison hF hG hq hr heq her hκ hD hη hBF hBG hG1 hdiff1
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro w hw
  let a := (v,fderiv ℝ q θ v)
  let b := (w,fderiv ℝ q θ w)
  let c := (v,fderiv ℝ r θ v)
  let d := (w,fderiv ℝ r θ w)
  let y := (fderiv ℝ (fderiv ℝ q) θ-fderiv ℝ (fderiv ℝ r) θ) v w
  let z := fderiv ℝ (fderiv ℝ r) θ v w
  have hf2 : L (0,fderiv ℝ (fderiv ℝ q) θ v w)=-M a b :=
    stationary_second_equation hF hq heq v w
  have hg2 : N (0,z)=-P c d := stationary_second_equation hG hr her v w
  have hid : L (0,y)=-(M a b-P c d)-(L-N) (0,z) := by
    have hy : ((0:Θ),y)=(0,fderiv ℝ (fderiv ℝ q) θ v w)-(0,z) := by ext <;> simp [y,z]
    rw [hy,map_sub,hf2,sub_apply,hg2]
    abel
  have hc := coercive_linear_vector_bound (L.comp (ContinuousLinearMap.inr ℝ Θ E)) hκ hBF y
  change ‖y‖ ≤ ‖L (0,y)‖/κ at hc
  rw [hid] at hc
  have hm := norm_bilinear_difference_le M P a b c d hη hA hD (by positivity)
    hdiff2 hG2
    (tangent_norm_le (le_max_left 1 (D/κ)) (hq1.trans (le_max_right _ _)) hv)
    (tangent_norm_le (le_max_left 1 (D/κ)) (hq1.trans (le_max_right _ _)) hw)
    (tangent_norm_le (le_max_left 1 (D/κ)) (hr1.trans (le_max_right _ _)) hv)
    (tangent_norm_le (le_max_left 1 (D/κ)) (hr1.trans (le_max_right _ _)) hw)
    (tangent_difference_norm_le hfirst hv) (tangent_difference_norm_le hfirst hw)
  have hzb : ‖z‖ ≤ D*A^2/κ := by
    have hh := norm_curried_bilinear_apply_le (fderiv ℝ (fderiv ℝ r) θ) v w
    simpa only [hv,hw,mul_one] using hh.trans
      (by simpa only [hv,hw,mul_one] using hr2)
  have hl : ‖(L-N) (0,z)‖ ≤ η*(D*A^2/κ) := by
    apply ((L-N).le_opNorm (0,z)).trans
    rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg z)]
    exact mul_le_mul hdiff1 hzb (norm_nonneg _) hη
  apply hc.trans
  have hsum := (norm_sub_le (-(M a b-P c d)) ((L-N) (0,z))).trans (add_le_add (by simpa only [norm_neg] using hm) hl)
  convert div_le_div_of_nonneg_right hsum hκ.le using 1 <;> dsimp only [A] <;> ring
end DepthPaper
