module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.HolderCalc
/-!
# Lemma 4.6: regularity of the fixed horizontal force

The force `g_ω` is a sum of rescaled pulses supported in disjoint open subintervals of the
pulse intervals `I_j`.  Its `r`-th time derivative is the corresponding sum of the pieces
`(k_j δ_j^{r+2})⁻¹ (∂ₛ^{r+1} b_{ω_j})((t - s_j)/δ_j, k_j x)`.  Each piece is bounded in `C^α`
by `C k_j^{α-1} δ_j^{-r-2}`, which tends to zero (even after division by `η_j`), so all time
derivatives extend by zero across the accumulation time `T_*`.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss
/-! ### The pieces -/
lemma holderNorm_zero' {d : ℕ} {E : Type*} [NormedAddCommGroup E] (α : ℝ) :
    holderNorm α (0 : Pt d → E) = 0 := by
  simp [holderNorm]
lemma holderNorm_add_le {d : ℕ} {E : Type*} [NormedAddCommGroup E] (α : ℝ) (f g : Pt d → E) :
    holderNorm α (f + g) ≤ holderNorm α f + holderNorm α g := by
  unfold holderNorm
  calc (⨆ x, ‖(f + g) x‖ₑ) + ⨆ x, ⨆ y, ‖(f + g) x - (f + g) y‖ₑ / ‖x - y‖ₑ ^ α
      ≤ ((⨆ x, ‖f x‖ₑ) + ⨆ x, ‖g x‖ₑ) + ((⨆ x, ⨆ y, ‖f x - f y‖ₑ / ‖x - y‖ₑ ^ α) +
          ⨆ x, ⨆ y, ‖g x - g y‖ₑ / ‖x - y‖ₑ ^ α) := by
        gcongr
        · exact iSup_le fun x => (enorm_add_le _ _).trans (add_le_add
            (le_iSup (fun x => ‖f x‖ₑ) x) (le_iSup (fun x => ‖g x‖ₑ) x))
        · refine iSup₂_le fun x y => ?_
          have e : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by
            simp only [Pi.add_apply]; abel
          rw [e]
          calc ‖(f x - f y) + (g x - g y)‖ₑ / ‖x - y‖ₑ ^ α
              ≤ (‖f x - f y‖ₑ + ‖g x - g y‖ₑ) / ‖x - y‖ₑ ^ α := by
                gcongr; exact enorm_add_le _ _
            _ = ‖f x - f y‖ₑ / ‖x - y‖ₑ ^ α + ‖g x - g y‖ₑ / ‖x - y‖ₑ ^ α := ENNReal.add_div
            _ ≤ _ := add_le_add
                (le_iSup₂ (f := fun x y => ‖f x - f y‖ₑ / ‖x - y‖ₑ ^ α) x y)
                (le_iSup₂ (f := fun x y => ‖g x - g y‖ₑ / ‖x - y‖ₑ ^ α) x y)
    _ = _ := add_add_add_comm _ _ _ _
end AnomDiss
