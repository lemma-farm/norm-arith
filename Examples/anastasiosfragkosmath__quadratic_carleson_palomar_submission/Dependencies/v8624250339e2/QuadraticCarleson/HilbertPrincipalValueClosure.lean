import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.OscillatoryReductionLimit
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v8624250339e2.QuadraticCarleson.HilbertFiniteTruncationWeakOneOne
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Topology.MetricSpace.Cauchy
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Principal-value closure from the uniform maximal weak estimate

Smooth compactly supported functions are approximated using Mathlib's actual
`L¹` density theorem. The sole classical input is the uniform weak estimate
for the genuine ordinary Hilbert maximal truncation on `L0Infinity`.
-/
open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology
namespace QuadraticCarleson
namespace HilbertPrincipalValueClosure
open HilbertFiniteTruncationWeakOneOne OscillatoryReduction
set_option autoImplicit false
noncomputable def schwartzResidual (f : L0Infinity) (g : 𝓢(ℝ, ℂ))
    (hg : HasCompactSupport (g : ℝ → ℂ)) : L0Infinity where
  toFun := fun x ↦ f x - g x
  measurable_toFun := f.measurable_toFun.sub g.continuous.measurable
  bounded_toFun := by
    obtain ⟨A, hA⟩ := f.bounded_toFun
    refine ⟨A + SchwartzMap.seminorm ℂ 0 0 g, fun x ↦ ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add (hA x) (g.norm_le_seminorm ℂ x))
  hasCompactSupport_toFun := f.hasCompactSupport_toFun.sub hg
theorem zeroHilbertTrunc_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    quadraticHilbertTrunc 0 ε (fun y ↦ f y - g y) x =
      quadraticHilbertTrunc 0 ε f x - quadraticHilbertTrunc 0 ε g x := by
  unfold quadraticHilbertTrunc
  simp only [zero_mul, phase_zero, mul_one, sub_div]
  exact integral_sub (integrableOn_zeroHilbertTail hε hf x)
    (integrableOn_zeroHilbertTail hε hg x)
theorem norm_zeroHilbertTrunc_le_of_maximal_le
    (f : ℝ → ℂ) {a : ℝ} (ha : 0 ≤ a) {x ε : ℝ} (hε : 0 < ε)
    (hmax : quadraticHilbertMaximalTruncation 0 f x ≤ ENNReal.ofReal a) :
    ‖quadraticHilbertTrunc 0 ε f x‖ ≤ a := by
  apply (ENNReal.ofReal_le_ofReal_iff ha).mp
  rw [ofReal_norm]
  exact (le_iSup (fun δ : {δ : ℝ // 0 < δ} ↦
    ‖quadraticHilbertTrunc 0 δ.1 f x‖ₑ) ⟨ε, hε⟩).trans hmax
/-- A positive tail-oscillation obstruction to the Cauchy property. Its
outer measure suffices; no measurability of the uncountable quantifiers is
assumed. -/
def badHilbertCauchySet (f : ℝ → ℂ) (η : ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → ∃ s : ℝ, 0 < s ∧ s < δ ∧
    ∃ t : ℝ, 0 < t ∧ t < δ ∧
      η < ‖quadraticHilbertTrunc 0 s f x - quadraticHilbertTrunc 0 t f x‖}
theorem principalValue_tail_pair_small
    {g : ℝ → ℂ} {x : ℝ} {w : ℂ}
    (hg : HasQuadraticPrincipalValue 0 g x w) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      ∀ t : ℝ, 0 < t → t < δ →
        ‖quadraticHilbertTrunc 0 s g x - quadraticHilbertTrunc 0 t g x‖ < η := by
  have he := hg (Metric.ball_mem_nhds w (by positivity : 0 < η / 2))
  obtain ⟨δ, hδ, hδsub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (by norm_num : (0 : ℝ) < 1)).mp he
  refine ⟨δ, hδ, fun s hs hsδ t ht htδ ↦ ?_⟩
  have hsclose := hδsub ⟨hs, hsδ⟩
  have htclose := hδsub ⟨ht, htδ⟩
  change dist (quadraticHilbertTrunc 0 s g x) w < η / 2 at hsclose
  change dist (quadraticHilbertTrunc 0 t g x) w < η / 2 at htclose
  rw [← dist_eq_norm]
  have hh := dist_triangle (quadraticHilbertTrunc 0 s g x) w
    (quadraticHilbertTrunc 0 t g x)
  rw [dist_comm w] at hh
  linarith
/-- Smooth convergence and a uniformly small maximal residual exclude a
tail-oscillation obstruction for the original input. -/
theorem badHilbertCauchySet_subset_maximal_residual
    (f : L0Infinity) (g : 𝓢(ℝ, ℂ)) (hg : HasCompactSupport (g : ℝ → ℂ))
    {η : ℝ} (hη : 0 < η) :
    badHilbertCauchySet f η ⊆
      {x | ENNReal.ofReal (η / 4) < quadraticHilbertMaximalTruncation 0
        (schwartzResidual f g hg) x} := by
  intro x hx
  by_contra hnot
  change ¬ ENNReal.ofReal (η / 4) < quadraticHilbertMaximalTruncation 0
    (schwartzResidual f g hg) x at hnot
  have hmax := le_of_not_gt hnot
  obtain ⟨δ, hδ, hsmall⟩ := principalValue_tail_pair_small
    (hasQuadraticPrincipalValue_schwartz 0 g x) (by positivity : 0 < η / 2)
  obtain ⟨s, hs, hsδ, t, ht, htδ, hbad⟩ := hx δ hδ
  have hresS := norm_zeroHilbertTrunc_le_of_maximal_le (schwartzResidual f g hg)
    (by positivity : 0 ≤ η / 4) hs hmax
  have hresT := norm_zeroHilbertTrunc_le_of_maximal_le (schwartzResidual f g hg)
    (by positivity : 0 ≤ η / 4) ht hmax
  have hgs := hsmall s hs hsδ t ht htδ
  have heqS : quadraticHilbertTrunc 0 s (schwartzResidual f g hg) x =
      quadraticHilbertTrunc 0 s f x - quadraticHilbertTrunc 0 s g x :=
    zeroHilbertTrunc_sub f.integrable g.integrable hs x
  have heqT : quadraticHilbertTrunc 0 t (schwartzResidual f g hg) x =
      quadraticHilbertTrunc 0 t f x - quadraticHilbertTrunc 0 t g x :=
    zeroHilbertTrunc_sub f.integrable g.integrable ht x
  have hbound : ‖quadraticHilbertTrunc 0 s f x - quadraticHilbertTrunc 0 t f x‖ ≤
      ‖quadraticHilbertTrunc 0 s (schwartzResidual f g hg) x‖ +
        ‖quadraticHilbertTrunc 0 t (schwartzResidual f g hg) x‖ +
          ‖quadraticHilbertTrunc 0 s g x - quadraticHilbertTrunc 0 t g x‖ := by
    calc
      _ = ‖(quadraticHilbertTrunc 0 s (schwartzResidual f g hg) x -
          quadraticHilbertTrunc 0 t (schwartzResidual f g hg) x) +
            (quadraticHilbertTrunc 0 s g x - quadraticHilbertTrunc 0 t g x)‖ := by
        rw [heqS, heqT]
        congr 1
        ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  linarith
end HilbertPrincipalValueClosure
end QuadraticCarleson
