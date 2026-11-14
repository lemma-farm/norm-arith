module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v418de092c8df.HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTestsTruncation ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Truncated dual powers for occupation densities

Measure-generic bounded tests and their exact conjugate norms. Adapted from the
`PDEFoundation.Measure.SignedTruncatedDualPower` infrastructure; no additional duality
theorem is assumed.
-/
@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open MeasureTheory Set
open scoped ENNReal
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
/-- The absolute value of `g`, truncated to the set where it is at most
`n + 1`. -/
def truncatedAbs (g : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  {x | |g x| ≤ n + 1}.indicator (fun x => |g x|) x
/-- The signed conjugate power of the bounded absolute-value truncation. -/
def signedTruncatedDualPower (g : α → ℝ) (r : ℝ) (n : ℕ) (x : α) : ℝ :=
  if 0 ≤ g x then (truncatedAbs g n x) ^ (r - 1)
  else -(truncatedAbs g n x) ^ (r - 1)

end
end HypoellipticAleksandrov.KineticAleksandrov.Occupation

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_0aea8b20aa89b9e8a636_DensityFromTestsBounded ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Sharp density norm bounds from bounded conjugate tests

This is the finite-measure restriction step of smooth-test duality. The density is
already given here; existence and absolute continuity are separate steps.
Adapted from `PDEFoundation.Measure.LpConjugateBoundFromTests`.
-/
@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
set_option linter.unusedVariables false in
/-- A sharp bound against every bounded measurable conjugate test forces the
tested function to belong to `Lʳ`, with the same norm bound. -/
theorem memLp_and_eLpNorm_le_of_bounded_conjugate_tests
    [IsFiniteMeasure μ] {r M : ℝ} (hr : 1 < r) (hM : 0 ≤ M)
    {g : α → ℝ} (hgMeas : Measurable g) (_hgInt : Integrable g μ)
    (htest : ∀ φ : α → ℝ, Measurable φ →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, |φ x| ≤ C) →
      |∫ x, φ x * g x ∂μ| ≤
        M * (eLpNorm φ (ENNReal.ofReal (r / (r - 1))) μ).toReal) 
    (h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_eLpNorm_signedTruncatedDualPower : ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {g : α → ℝ},
      Measurable g →
        ∀ {r : ℝ},
          1 < r →
            ∀ (n : ℕ),
              MeasureTheory.eLpNorm
                  (HypoellipticAleksandrov.KineticAleksandrov.Occupation.signedTruncatedDualPower g r n)
                  (ENNReal.ofReal (r / (r - 1))) μ =
                MeasureTheory.eLpNorm
                    (HypoellipticAleksandrov.KineticAleksandrov.Occupation.truncatedAbs g n)
                    (ENNReal.ofReal r) μ ^
                  (r - 1))
    (h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_integral_signedTruncatedDualPower_mul : ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
      [MeasureTheory.IsFiniteMeasure μ] {g : α → ℝ},
      Measurable g →
        ∀ {r : ℝ},
          1 < r →
            ∀ (n : ℕ),
              ∫ (x : α),
                  HypoellipticAleksandrov.KineticAleksandrov.Occupation.signedTruncatedDualPower g r n
                      x *
                    g x ∂μ =
                (MeasureTheory.eLpNorm
                      (HypoellipticAleksandrov.KineticAleksandrov.Occupation.truncatedAbs g n)
                      (ENNReal.ofReal r) μ).toReal ^
                  r)
    (h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_signedTruncatedDualPower_measurable_bounded : ∀ {α : Type u_1} [inst : MeasurableSpace α] {g : α → ℝ},
      Measurable g →
        ∀ {r : ℝ},
          1 < r →
            ∀ (n : ℕ),
              Measurable
                  (HypoellipticAleksandrov.KineticAleksandrov.Occupation.signedTruncatedDualPower g r
                    n) ∧
                ∀ (x : α),
                  |HypoellipticAleksandrov.KineticAleksandrov.Occupation.signedTruncatedDualPower g r n
                        x| ≤
                    ((↑n : ℝ) + 1) ^ (r - 1))
    (h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_measurable_truncatedAbs : ∀ {α : Type u_1} [inst : MeasurableSpace α] {g : α → ℝ},
      Measurable g →
        ∀ (n : ℕ), Measurable (HypoellipticAleksandrov.KineticAleksandrov.Occupation.truncatedAbs g n))
    (h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_memLp_truncatedAbs : ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
      [MeasureTheory.IsFiniteMeasure μ] {g : α → ℝ},
      Measurable g →
        ∀ (n : ℕ) (p : ENNReal),
          MeasureTheory.MemLp (HypoellipticAleksandrov.KineticAleksandrov.Occupation.truncatedAbs g n) p
            μ)
    :
    MemLp g (ENNReal.ofReal r) μ ∧
      (eLpNorm g (ENNReal.ofReal r) μ).toReal ≤ M := by
  have hnormTrunc (n : ℕ) :
      (eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ).toReal ≤ M := by
    let N := (eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ).toReal
    have htestn := htest (signedTruncatedDualPower g r n)
      (h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_signedTruncatedDualPower_measurable_bounded hgMeas hr n).1
      ⟨(n + 1 : ℝ) ^ (r - 1),
        Real.rpow_nonneg (by positivity) _,
        h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_signedTruncatedDualPower_measurable_bounded hgMeas hr n |>.2⟩
    rw [h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_integral_signedTruncatedDualPower_mul hgMeas hr n,
      h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_eLpNorm_signedTruncatedDualPower hgMeas hr n] at htestn
    rw [← ENNReal.toReal_rpow] at htestn
    change |N ^ r| ≤ M * N ^ (r - 1) at htestn
    have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
    rw [abs_of_nonneg (Real.rpow_nonneg hN0 _)] at htestn
    by_cases hNz : N = 0
    · simpa [N, hNz] using hM
    · have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNz)
      have hsplit : N ^ r = N * N ^ (r - 1) := by
        calc
          N ^ r = N ^ (1 + (r - 1)) := by
            congr 1
            ring
          _ = N ^ (1 : ℝ) * N ^ (r - 1) := Real.rpow_add hNpos _ _
          _ = N * N ^ (r - 1) := by rw [Real.rpow_one]
      rw [hsplit] at htestn
      exact le_of_mul_le_mul_right htestn (Real.rpow_pos_of_pos hNpos _)
  have htruncNormENN (n : ℕ) :
      eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal M := by
    apply (ENNReal.toReal_le_toReal
      (h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_memLp_truncatedAbs hgMeas n _).eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hM]
    exact hnormTrunc n
  have hlim (x : α) :
      Tendsto (fun n => truncatedAbs g n x) atTop (𝓝 |g x|) := by
    apply tendsto_atTop_of_eventually_const
      (i₀ := Nat.ceil |g x|)
    intro n hn
    rw [truncatedAbs, Set.indicator_of_mem]
    have hceil : |g x| ≤ Nat.ceil |g x| := Nat.le_ceil _
    exact hceil.trans (by exact_mod_cast (hn.trans (Nat.le_add_right n 1)))
  have habsNorm : eLpNorm (fun x => |g x|) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal M := by
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_measurable_truncatedAbs hgMeas n).aestronglyMeasurable)
      (fun x => |g x|) (continuous_abs.measurable.comp hgMeas).aestronglyMeasurable
      (ae_of_all _ hlim)).trans ?_
    exact liminf_le_of_frequently_le (Frequently.of_forall htruncNormENN)
  have habsLp : MemLp (fun x => |g x|) (ENNReal.ofReal r) μ := by
    exact habsNorm.trans_lt ENNReal.ofReal_lt_top
  have hnormEq : eLpNorm g (ENNReal.ofReal r) μ =
      eLpNorm (fun x => |g x|) (ENNReal.ofReal r) μ := by
    apply eLpNorm_congr_norm_ae hgMeas.aestronglyMeasurable
      (continuous_abs.measurable.comp hgMeas).aestronglyMeasurable
    exact ae_of_all _ fun x => by simp [Real.norm_eq_abs]
  have hgLp : MemLp g (ENNReal.ofReal r) μ := by
    rw [memLp_iff, hnormEq]
    exact habsLp.eLpNorm_lt_top
  refine ⟨hgLp, ?_⟩
  rw [hnormEq]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top habsNorm
  simpa [ENNReal.toReal_ofReal hM] using hreal
end
end HypoellipticAleksandrov.KineticAleksandrov.Occupation
