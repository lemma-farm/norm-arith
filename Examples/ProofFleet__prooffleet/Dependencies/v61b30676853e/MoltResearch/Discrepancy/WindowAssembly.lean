import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.ParsevalBridge
import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.TypicalFactorization
import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.HalaszComplex
import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.HalaszAssembly
/-!
# Track C: the window assembly (Track R, A.2 leg, G-ladder)

The end-to-end assembly of the log-averaged window bound
`∑_{n ∈ (x/w, x]} ‖W_n‖/(H·n) ≤ ε·log w` from the in-tree pieces: the
Parseval bridge's time side (`slice_time_side`), the Plancherel
harness's regime split, the `𝒰`-recursion band energies, the typical
factorization density, and the ℂ-valued plain-sum Halász.  Units are
the G-ladder of the A2-II/III design (state file): G1–G5 glue the
frequency side, G6 expands the major arc, G7 supplies the Halász sup,
G8–G10 aggregate and close.
-/
namespace MoltResearch
namespace ExpSums
open Real MeasureTheory
open scoped FourierTransform ContDiff
open MeasureTheory in
/-- **A2-III VI-1c-2 — the `L²` triangle inequality on an abstract frequency set.**

The set-integral counterpart of `intervalIntegral_norm_add_sq_le`.  The interval
version is what the `[MR]` collar telescoping needed; the capstone needs the same
inequality over the abstract frequency sets `𝒯_j` and `𝒰`, which are never
intervals and are only ever available as measurable subsets of `Ioc (-T) T`.

This is the join that lets `sum_eq_cell_rep_add_cell_error` be used: that
identity writes a level's contribution as a main term plus a replacement error,
and the two are priced by different lemmas
(`setIntegral_norm_sq_cell_block_sum_le` and
`intervalIntegral_norm_sq_cell_replace_le`) at different anchors, so their
energies cannot be merged into one mean value theorem application.  Splitting
the square is the honest price, and the factor `2` is absorbed by the `1/N` the
collars carry — exactly as in the interval version. -/
theorem setIntegral_norm_add_sq_le (F H : ℝ → ℂ) (hF : Continuous F)
    (hH : Continuous H) (T : ℝ) (G : Set ℝ) (hGm : MeasurableSet G)
    (hGT : G ⊆ Set.Ioc (-T) T) :
    (∫ ξ in G, ‖F ξ + H ξ‖^2)
      ≤ 2 * (∫ ξ in G, ‖F ξ‖^2) + 2 * (∫ ξ in G, ‖H ξ‖^2) := by
  have hFi : IntegrableOn (fun ξ => ‖F ξ‖^2) G :=
    ((hF.norm.pow 2).integrableOn_Ioc (a := -T) (b := T)).mono_set hGT
  have hHi : IntegrableOn (fun ξ => ‖H ξ‖^2) G :=
    ((hH.norm.pow 2).integrableOn_Ioc (a := -T) (b := T)).mono_set hGT
  have hsum : IntegrableOn (fun ξ => ‖F ξ + H ξ‖^2) G :=
    ((((hF.add hH).norm).pow 2).integrableOn_Ioc (a := -T) (b := T)).mono_set hGT
  have hbig : IntegrableOn (fun ξ => 2 * ‖F ξ‖^2 + 2 * ‖H ξ‖^2) G :=
    (hFi.const_mul 2).add (hHi.const_mul 2)
  have hptwise : ∀ ξ : ℝ, ‖F ξ + H ξ‖^2 ≤ 2 * ‖F ξ‖^2 + 2 * ‖H ξ‖^2 := by
    intro ξ
    have htri : ‖F ξ + H ξ‖ ≤ ‖F ξ‖ + ‖H ξ‖ := norm_add_le _ _
    nlinarith [norm_nonneg (F ξ + H ξ), norm_nonneg (F ξ), norm_nonneg (H ξ),
      sq_nonneg (‖F ξ‖ - ‖H ξ‖)]
  calc (∫ ξ in G, ‖F ξ + H ξ‖^2)
      ≤ ∫ ξ in G, (2 * ‖F ξ‖^2 + 2 * ‖H ξ‖^2) :=
        setIntegral_mono_on hsum hbig hGm (fun ξ _ => hptwise ξ)
    _ = 2 * (∫ ξ in G, ‖F ξ‖^2) + 2 * (∫ ξ in G, ‖H ξ‖^2) := by
        rw [integral_add (hFi.const_mul 2) (hHi.const_mul 2),
          integral_const_mul, integral_const_mul]
end ExpSums
end MoltResearch
