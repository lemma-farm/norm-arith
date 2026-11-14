module

public import Mathlib
public import Mathlib.Tactic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Order.ProjIcc

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Examples.Example_c56a44d18b25033161b6_DiracState ====
set_option autoImplicit false
@[expose] public section
/-!
# Pathwise state equation for a Dirac Parisi measure

For a continuous noise path `W`, subtracting the additive term `β W` from the
post-interface state reduces the equation to an ordinary differential equation.
The bounded globally Lipschitz tanh drift gives existence on the full finite
time interval and pathwise uniqueness, using Picard–Lindelöf.
-/
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal Topology
namespace Paper
/-- The pathwise drift after the additive noise is subtracted. -/
def diracNoiseDrift (β : ℝ) (W : ℝ → ℝ) (t y : ℝ) : ℝ :=
  β ^ 2 * Real.tanh (y + β * W t)

/-- A pathwise solution of the drift ODE on the post-interface interval. -/
structure IsDiracNoiseSolution (β h q : ℝ) (W Y : ℝ → ℝ) : Prop where
  initial : Y q = h
  hasDerivWithinAt : ∀ t ∈ Icc q (1 : ℝ),
    HasDerivWithinAt Y (diracNoiseDrift β W t (Y t)) (Icc q (1 : ℝ)) t
namespace IsDiracNoiseSolution
variable {β h q : ℝ} {W Y Z : ℝ → ℝ}

end IsDiracNoiseSolution
set_option linter.unusedVariables false in
axiom _root_.Paper.exists_diracNoiseSolution : ∀ (β h q : ℝ),
  q ≤ 1 → ∀ (W : ℝ → ℝ), Continuous W → ∃ (Y : ℝ → ℝ), Paper.IsDiracNoiseSolution β h q W Y
def diracNoiseSolution (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) : ℝ → ℝ :=
  Classical.choose (exists_diracNoiseSolution β h q hq W hW)

/-- Constant extension of the correction outside `[q,1]`; it is globally continuous. -/
def diracCorrection (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) (t : ℝ) : ℝ :=
  diracNoiseSolution β h q hq W hW (projIcc q 1 hq t)

set_option linter.unusedVariables false in
axiom _root_.Paper.continuous_diracCorrection : ∀ (β h q : ℝ) (hq : q ≤ 1) (W : ℝ → ℝ) (hW : Continuous W),
  Continuous (Paper.diracCorrection β h q hq W hW)

set_option linter.unusedVariables false in
axiom _root_.Paper.IsDiracNoiseSolution.noise_dependence : ∀ {β h q : ℝ} {W V Y Z : ℝ → ℝ},
  Paper.IsDiracNoiseSolution β h q W Y →
    Paper.IsDiracNoiseSolution β h q V Z →
      ∀ {D : ℝ},
        (∀ t ∈ Set.Icc q 1, Dist.dist (W t) (V t) ≤ D) →
          ∀ {t : ℝ},
            t ∈ Set.Icc q 1 →
              Dist.dist (Y t) (Z t) ≤ gronwallBound 0 (β ^ 2) (β ^ 2 * |β| * D) (t - q)
def diracCorrectionConstant (β q : ℝ) : ℝ :=
  gronwallBound 0 (β ^ 2) (β ^ 2 * |β|) (1 - q)

/-- Extend a compact continuous noise path constantly beyond its endpoints. -/
def compactNoiseExtension (a b : ℝ) (hab : a ≤ b) (w : C(Icc a b, ℝ)) : ℝ → ℝ :=
  fun t => w (projIcc a b hab t)
set_option linter.unusedVariables false in
axiom _root_.Paper.continuous_compactNoiseExtension : ∀ (a b : ℝ) (hab : a ≤ b) (w : C((↑(Set.Icc a b) : Type), ℝ)),
  Continuous (Paper.compactNoiseExtension a b hab w)
/-- The correction as a continuous map on the post-interface time interval. -/
def diracCorrectionPath (β h q : ℝ) (hq : q ≤ 1) (w : C(Icc q (1 : ℝ), ℝ)) :
    C(Icc q (1 : ℝ), ℝ) :=
  ⟨fun t => diracCorrection β h q hq (compactNoiseExtension q 1 hq w)
    (continuous_compactNoiseExtension q 1 hq w) t,
    (continuous_diracCorrection β h q hq (compactNoiseExtension q 1 hq w)
      (continuous_compactNoiseExtension q 1 hq w)).comp continuous_subtype_val⟩
set_option linter.unusedVariables false in
/-- Picard–Lindelöf selection defines a globally Lipschitz map of the noise path. -/
theorem lipschitzWith_diracCorrectionPath (β h q : ℝ) (hq : q ≤ 1) 
    (h_Paper_diracCorrectionConstant_nonneg : ∀ (β q : ℝ), q ≤ 1 → 0 ≤ Paper.diracCorrectionConstant β q)
    (h_Paper_gronwallBound_scale_zero : ∀ (K ε D x : ℝ), gronwallBound 0 K (ε * D) x = gronwallBound 0 K ε x * D)
    (h_Paper_diracCorrection_spec : ∀ (β h q : ℝ) (hq : q ≤ 1) (W : ℝ → ℝ) (hW : Continuous W),
      Paper.IsDiracNoiseSolution β h q W (Paper.diracCorrection β h q hq W hW))
    :
    LipschitzWith ⟨diracCorrectionConstant β q, h_Paper_diracCorrectionConstant_nonneg β q hq⟩
      (diracCorrectionPath β h q hq) := by
  apply LipschitzWith.of_dist_le_mul
  intro w v
  apply (ContinuousMap.dist_le (mul_nonneg (h_Paper_diracCorrectionConstant_nonneg β q hq)
    (dist_nonneg : 0 ≤ dist w v))).mpr
  intro t
  have hd : ∀ s ∈ Icc q (1 : ℝ),
      dist (compactNoiseExtension q 1 hq w s) (compactNoiseExtension q 1 hq v s) ≤
        dist w v := fun s _ => ContinuousMap.dist_apply_le_dist (projIcc q 1 hq s)
  have hb := (h_Paper_diracCorrection_spec β h q hq (compactNoiseExtension q 1 hq w)
    (continuous_compactNoiseExtension q 1 hq w)).noise_dependence
    (h_Paper_diracCorrection_spec β h q hq (compactNoiseExtension q 1 hq v)
      (continuous_compactNoiseExtension q 1 hq v)) hd t.property
  rw [h_Paper_gronwallBound_scale_zero] at hb
  have hm := gronwallBound_mono (δ := (0 : ℝ)) (K := β ^ 2)
    (ε := β ^ 2 * |β|) le_rfl (by positivity) (sq_nonneg β)
    (sub_le_sub_right t.property.2 q)
  exact hb.trans (mul_le_mul_of_nonneg_right hm dist_nonneg)

end Paper
