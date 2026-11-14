module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v3bcafbcaf327.SubdiffusiveProcess.CoarseGrainingVocab.Concentration.Defs ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Concentration for scale arrays — definitions and constants

## Provenance

This support subtree mirrors the proof-role decomposition in the read-only
Algsuperdiff analogue
`Section4/Probability/ScalesConcentration/`.  GMC changes the sharp weight
constant, the one-row endpoint, and translated-window packaging.

This module formalizes the setup of Proposition `p.concentration.for.scales`
(ABK26, Appendix D): a concentration inequality for exceedance counts in a
triangular array `{X_{k,j}}` with geometric weights within rows and column-wise
`r`-dependence.

We work over an abstract probability space `(Ω, P)` with a nonnegative array
`X : ℤ → ℤ → Ω → ℝ`.  This file collects:

* the geometric weights `wt s k j = 3^{-s|k-j|}` and the weighted row sums
  `Yk` (the paper's `Y_k`);
* the exceedance thresholds `thr` and the column exceedance counts `Zcount`
  (the paper's `Z_j`);
* the universal constants `C₂`, `C₃`, and the exponential-moment rate `mgfRate`
  (`a = ⅛ (log 3) s p`);
* the positivity facts `one_sub_rpow_pos`, `C₂_pos`, `C₃_pos` and
  `mgfRate_pos` those constants need.  The geometric row-sum bound that Step 1
  uses is `Reduction.sum_wt_half_le`, one module on.

## Design of the independence hypothesis

The paper assumes `r`-dependence across columns
(`e.independent.columns.twosided`): for `I, J ⊆ ℤ` with `dist(I,J) ≥ r`, the
families `{X_{·,j} : j ∈ I}` and `{X_{·,j} : j ∈ J}` are independent.  What the
proof actually uses (Step 4) is the mutual independence, *within each residue
class* `b` modulo `r`, of the columns `{X_{·, jr+b} : j ∈ ℤ}` — these columns
are pairwise at distance `≥ r`, and `{i}` is at distance `≥ r` from
`{i', i'', …}` for any earlier members, so the paper's two-set hypothesis
yields mutual independence by induction.  We therefore take as the hypothesis
the mutual independence of each residue class, phrased with mathlib's
`iIndepFun` over the whole columns viewed as `(ℤ → ℝ)`-valued random variables:

  `∀ b : ℤ, iIndepFun (fun j : ℤ => fun ω k => X k (j * r + b) ω) P`.

This is the weakest faithful hypothesis mathlib's independence A supports
cleanly; it is implied by `e.independent.columns.twosided`.  Since `Zcount j`
is a measurable function of column `j` alone, `iIndepFun.comp` transports this
to independence of the `Z`'s within each residue class.
-/
namespace SubdiffusiveProcess.Concentration
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
/-- Real distance between integer indices, `|k - j|`. -/
noncomputable def idist (k j : ℤ) : ℝ := |(k : ℝ) - (j : ℝ)|
noncomputable def wt (s : ℝ) (k j : ℤ) : ℝ := (3 : ℝ) ^ (-(s * idist k j))

/-- The weighted row sum `Y_k = ∑_j 3^{-s|k-j|} X_{k,j}`. -/
noncomputable def Yk {Ω : Type*} (X : ℤ → ℤ → Ω → ℝ) (s : ℝ) (k : ℤ) (ω : Ω) : ℝ :=
  ∑' j : ℤ, wt s k j * X k j ω
/-- The Step-1/Step-2 exceedance threshold `½ λ 3^{(s/2)|k-j|}`. -/
noncomputable def thr (s lam : ℝ) (k j : ℤ) : ℝ :=
  (lam / 2) * (3 : ℝ) ^ ((s / 2) * idist k j)
end SubdiffusiveProcess.Concentration

end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_3eec703c445cfa6fab66_Reduction ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Concentration for scale arrays — Step 1 (reduction to a counting problem)

This module formalizes Step 1 of the proof: the
deterministic reduction of the weighted-row exceedance
`𝟙{Y_k > 2 λ s⁻¹}` to the column exceedance counts `Z_j`.

We use the paper's threshold `2 λ s⁻¹`, from the sharp geometric constant
`4/s` proved in `Weights.lean`.

Main results:

* `sum_wt_half_le`: `∑_j 3^{-(s/2)|k-j|} ≤ 4/s`;
* `Yk_le_of_pointwise`: the pointwise implication of Step 1;
* `exists_exceed_of_Yk_gt`: contrapositive — a large `Y_k` forces a column
  exceedance;
* `indicator_Yk_le_tsum`: the pointwise `ℝ≥0∞` counting bound, the row
  indicator `𝟙{Y_k > 2λs⁻¹}` below the tsum of the column indicators;
* `sum_indicator_Yk_le_tsum_Zcount`: summed over `k ∈ {0,…,m}`.
-/
namespace SubdiffusiveProcess.Concentration
open MeasureTheory Finset Real
open scoped ENNReal NNReal
variable {Ω : Type*}


set_option linter.unusedVariables false in
/-- **Step 1, pointwise bound.**  If every column at row `k` is below its
threshold, then the weighted row `Y_k` is at most `2 λ s⁻¹`. -/
lemma Yk_le_of_pointwise {s lam : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (X : ℤ → ℤ → Ω → ℝ) (k : ℤ) (ω : Ω) (hlam : 0 ≤ lam)
    (hXnn : ∀ j, 0 ≤ X k j ω)
    (hbound : ∀ j, X k j ω ≤ thr s lam k j) 
    (h_SubdiffusiveProcess_Concentration_wt_mul_le_of_bound : ∀ {Ω : Type u_1} {s lam : ℝ} (X : ℤ → ℤ → Ω → ℝ) (k j : ℤ) (ω : Ω),
      X k j ω ≤ SubdiffusiveProcess.Concentration.thr s lam k j →
        SubdiffusiveProcess.Concentration.wt s k j * X k j ω ≤
          lam / 2 * SubdiffusiveProcess.Concentration.wt (s / 2) k j)
    (h_SubdiffusiveProcess_Concentration_summable_wt_mul_of_le : ∀ {Ω : Type u_1} {s lam : ℝ},
      0 < s →
        s ≤ 1 →
          ∀ (X : ℤ → ℤ → Ω → ℝ) (k : ℤ) (ω : Ω),
            (∀ (j : ℤ), 0 ≤ X k j ω) →
              (∀ (j : ℤ), X k j ω ≤ SubdiffusiveProcess.Concentration.thr s lam k j) →
                Summable fun (j : ℤ) ↦ SubdiffusiveProcess.Concentration.wt s k j * X k j ω)
    (h_SubdiffusiveProcess_Concentration_sum_wt_half_le : ∀ {s : ℝ},
      0 < s → s ≤ 1 → ∀ (k : ℤ), ∑' (j : ℤ), SubdiffusiveProcess.Concentration.wt (s / 2) k j ≤ 4 / s)
    (h_SubdiffusiveProcess_Concentration_summable_wt_half : ∀ {s : ℝ},
      0 < s → s ≤ 1 → ∀ (k : ℤ), Summable fun (j : ℤ) ↦ SubdiffusiveProcess.Concentration.wt (s / 2) k j)
    :
    Yk X s k ω ≤ 2 * lam / s := by
  have hsum1 := h_SubdiffusiveProcess_Concentration_summable_wt_mul_of_le hs hs1 X k ω hXnn hbound
  have hsum2 : Summable (fun j : ℤ => (lam / 2) * wt (s / 2) k j) :=
    (h_SubdiffusiveProcess_Concentration_summable_wt_half hs hs1 k).mul_left (lam / 2)
  have hle : Yk X s k ω ≤ ∑' j : ℤ, (lam / 2) * wt (s / 2) k j := by
    unfold Yk
    exact hsum1.tsum_le_tsum (fun j => h_SubdiffusiveProcess_Concentration_wt_mul_le_of_bound X k j ω (hbound j)) hsum2
  refine hle.trans ?_
  rw [tsum_mul_left]
  have hbound' : ∑' j : ℤ, wt (s / 2) k j ≤ 4 / s := h_SubdiffusiveProcess_Concentration_sum_wt_half_le hs hs1 k
  have : (lam / 2) * ∑' j : ℤ, wt (s / 2) k j ≤ (lam / 2) * (4 / s) :=
    mul_le_mul_of_nonneg_left hbound' (by linarith)
  refine this.trans (le_of_eq ?_)
  field_simp
  ring
end SubdiffusiveProcess.Concentration
