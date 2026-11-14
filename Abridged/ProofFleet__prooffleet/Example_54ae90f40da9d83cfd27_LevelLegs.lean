import Mathlib
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Push
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Data.Nat.Factorization.Induction

-- ==== Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.MultiplicativeC ====
section
/-!
# Discrepancy: ℂ-valued completely multiplicative language layer

First language-layer module for the Tao 2015 analytic core
(`Problems/tao2015_analytic_core.md`): the ℂ-valued predicates the Fourier-reduction and
log-Elliott interfaces are stated over, plus the coercion bridge from the existing ℤ-valued
substrate.

Definitions:
- `CompletelyMultiplicativeC g` — `g (a * b) = g a * g b` for **all** `a b : ℕ` (no coprimality
  hypothesis, mirroring the ℤ-valued `CompletelyMultiplicative`).
- `Unimodular g` — `‖g n‖ = 1` for all `n` (the "valued in the unit circle `S¹`" hypothesis of
  Tao's interfaces, arXiv:1509.05363 §2).

Bridges (the ℤ-valued substrate embeds in the ℂ-valued language):
- `CompletelyMultiplicative.toC` — a ℤ-valued completely multiplicative sequence is completely
  multiplicative after coercion to ℂ.
- `IsSignSequence.unimodularC` — sign sequences are unimodular after coercion to ℂ.

Partial sums:
- `apSumC g d n` — ℂ-valued homogeneous AP partial sum, mirroring `apSum`.
- `CompletelyMultiplicativeC.apSumC_eq_mul_apSumC_one` — the multiplicative collapse
  `apSumC g d n = g d * apSumC g 1 n` (port of `CompletelyMultiplicative.apSum_eq_mul_apSum_one`).
- `CompletelyMultiplicativeC.norm_apSumC_eq_norm_apSumC_one` — its norm-level corollary for
  unimodular `g`: partial-sum growth along any step `d` is the step-one growth.

Design note (from the card's decision record): interfaces for the analytic core must be stated
over ℂ-valued unimodular functions — the ±1 subclass loses the character-modulated cases. The
ℤ-valued bridge below is the hand-off *into* that subclass once a reduction produces candidates,
not a substitute for it.
-/
namespace MoltResearch
/-- A ℂ-valued completely multiplicative sequence: `g (a * b) = g a * g b` for all **nonzero**
`a b : ℕ` (no coprimality hypothesis).

ℂ-valued analogue of `CompletelyMultiplicative`. As there, we do not bake in `g 1 = 1`: it
follows for unimodular sequences (`CompletelyMultiplicativeC.map_one_of_unimodular`), and keeping
the definition minimal makes it easier to produce.

The `a ≠ 0 → b ≠ 0` guards are load-bearing (issue #2879): the literature defines completely
multiplicative functions on `{1, 2, ...}`, and an unguarded law instantiated at `b = 0` gives
`g 0 = g a * g 0` for every `a`, which under any nonvanishing-at-`0` condition (`Unimodular`)
collapses the class to the constant-1 function and vacates every theorem quantifying over it.
With the guards, `g 0` is genuinely unconstrained junk.
-/
def CompletelyMultiplicativeC (g : ℕ → ℂ) : Prop :=
  ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → g (a * b) = g a * g b

namespace Unimodular
variable {g : ℕ → ℂ}
end Unimodular
namespace CompletelyMultiplicativeC
variable {g : ℕ → ℂ}
end CompletelyMultiplicativeC
namespace CompletelyMultiplicative
variable {f : ℕ → ℤ}
end CompletelyMultiplicative
namespace IsSignSequence
variable {f : ℕ → ℤ}
end IsSignSequence
end MoltResearch

end

-- ==== Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.TypicalFactorization ====
section
/-!
# Track C: typical factorization — the [mrt] 𝒮-set (Track R, A.2 leg, A2-I)

The set `𝒮` of integers with at least one prime factor in each of a
family of prime blocks `[P_j, Q_j]` — the typical-factorization
restriction of [MR]/[mrt, Appendix A], in the idiom of the Ramaré
`𝒰`-machinery: a level is a `Finset ℕ` of primes, a family is a
`List (Finset ℕ)` (the slot `RamareIdentity.uBound` recurses over),
and membership at one level is the `𝒰`-filter's
`0 < (P.filter (· ∣ n)).card`.
-/
namespace MoltResearch
/-- `n` has at least one divisor in every level of the family.  (For
prime levels: at least one prime factor in each block — the [mrt]
`𝒮`-membership.) -/
def HasFactorInAll (levels : List (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ P ∈ levels, 0 < (P.filter (· ∣ n)).card
instance (levels : List (Finset ℕ)) (n : ℕ) :
    Decidable (HasFactorInAll levels n) :=
  List.decidableBAll _ levels

def typicalS (a b : ℕ) (levels : List (Finset ℕ)) : Finset ℕ :=
  (Finset.Ioc a b).filter (HasFactorInAll levels)

noncomputable def eadicCell (P : Finset ℕ) (N v : ℕ) : Finset ℕ :=
  P.filter (fun p => ⌊(N:ℝ) * Real.log p⌋₊ = v)

end MoltResearch

end

-- ==== Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.BandSchedule ====
section
/-!
# The band schedule (Track R, `[mrt]` A.2, §4)

The `[mrt]` A.2 inner-band estimate is assembled from legs that each produce an
explicit real bound; `MoltResearch.Discrepancy.BandCapstone` composes them.  What
remains after that composition is *numerical*: each leg's bound must be shown to
fit inside its share of the band's slice budget

  `𝔅 = c₃ ε² (Δ/A) / 8`     (design report §4.1),

and the schedule `S1–S7` of §4.4 is exactly a choice of parameters making every
leg fit at once.  This module is that arithmetic.  It is deliberately free of
measure theory and of every in-tree dependency: each statement is an inequality
between real expressions, whose left-hand side is the *literal* right-hand side
of a merged band lemma, so a consumer composes with `le_trans` and nothing else.

**Why the conditions are hypotheses.**  §4.3 does not prove the legs fit; it
derives, leg by leg, the condition under which they do (`N_j ≥ C/ε³`,
`P₁ ≥ C/ε³`, a lower bound on `γ`, …).  Each lemma here takes that condition in
explicit form and concludes the fit.  Discharging all of them simultaneously
from a concrete `W`-schedule is a separate, self-contained computation.

## The collar leg (§4.3(a)), and one correction to the report

The report prices a collar as `e^π(T/A + 2)·Σ_{collar} 1/n ≈ 3e^π/N_j`, compares
that to `𝔅`, and reads off `N_j ≥ C/ε³` with an absolute `C`.  That is the cost
of **one** collar.  The quantity the tree actually produces — the error half of
`setIntegral_norm_sq_cell_prime_block_le` — is the assembled one, and it carries
two factors the report's estimate does not:

* the Cauchy–Schwarz factor `#I` over cells (the cell contributions are not
  orthogonal on `G`), and
* the weight `∑_v (∑_{p ∈ 𝒞_v} 1/p)²`, from the outer prime mass of each cell.

Both are exposed here as parameters rather than absorbed, because their product
is *not* absolutely bounded: `#I` grows linearly in the e-adic resolution `N`,
which cancels the `1/N` the collar ratio buys.  What saves the leg is that the
second factor is small — each `e`-adic cell has multiplicative width `e^{1/(2N)}`,
so `∑_v σ_v² ≤ (max_v σ_v)·∑_v σ_v` decays in `N` as well.  The honest condition
is therefore `N ≥ 64·#I·X·S₂/(κc₃ε³)` with `X` and `S₂` as below, not
`N ≥ C/ε³` at absolute `C`.
-/
namespace MoltResearch
/-- **The band's share of the slice budget** (Track R, A2-III, §4.1).

For the *normalised* integrand `F(ξ) = ∑ (g m/m)·e(−ξ log m)`, the prior slice
arithmetic gives the band `∫_band |F|² ≤ c₃ε²(Δ/A)/8`.  The third argument is
the ratio `ρ = Δ/A`; keeping it as one parameter is what makes the `Δ/A`
cancellation of §4.1 visible — the trivial bound carries the same factor, so the
requirement is a saving of `ε²` and nothing else. -/
noncomputable def bandBudget (c₃ ε ρ : ℝ) : ℝ := c₃ * ε ^ 2 * ρ / 8

end MoltResearch

end

-- ==== Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.BandCapstone ====
section
/-!
# The band-energy capstone (Track R, `[mrt]` A.2, Phase VI)

The `[mrt]` A.2 band estimate is assembled from legs that live in two
*import-sibling* modules.  `WindowAssembly` carries the level-one estimate
`band_energy_level_one_le`, the cell/block mean value
`setIntegral_norm_sq_cell_block_sum_le`, the outer band `band_energy_outer_le`
and the capstone glue (`setIntegral_le_sum_of_cover`, `setIntegral_weight_mono`,
`setIntegral_norm_add_sq_le`, `setIntegral_norm_sq_sum_le_card_mul`).
`WindowTK` carries the level-`j` estimate `band_energy_level_le_of_prev_large`,
the collar cost `intervalIntegral_norm_sq_cell_replace_le` and the elementary
large-values count `card_large_prime_poly_le`.

**Neither module imports the other** — they meet only in
`MoltResearch.DiscrepancyAnalytic` — so no composition of a `WindowAssembly` leg
with a `WindowTK` leg can be stated in either file.  That is the whole reason
this module exists.  It is the first place in the tree where both halves of the
band machinery are simultaneously in scope.

The remaining leg, the exceptional band `𝒰`, is *not* here: it is conditional on
`HalaszLargeValuesAssumption` and `PrimeLargeValuesAssumption`, and
`scripts/check_layering.sh` forbids `MoltResearch/` from importing the
`Conjectures/` tree where those classes live.  So the capstone splits at the
same seam that split IV-3 — an elementary half here, a conditional half in
`Conjectures/C0002_erdos_discrepancy/src/`.
-/
namespace MoltResearch
def bandPart (P : ℕ → Set ℝ) (J : ℕ) (j : ℕ) : Set ℝ :=
  if j < J then P j \ ⋃ i ∈ Finset.range j, P i
  else (⋃ i ∈ Finset.range J, P i)ᶜ

def bandPartOn (P : ℕ → Set ℝ) (J : ℕ) (G : Set ℝ) (j : ℕ) : Set ℝ :=
  G ∩ bandPart P J j

end MoltResearch

end

-- ==== Examples.ProofFleet__prooffleet.Examples.Example_54ae90f40da9d83cfd27_LevelLegs ====
/-!
# The level legs of the `[mrt]` A.2 inner band (Track R, A2-III, VI-2)

The A.2 capstone takes the first-index partition abstractly.  This module binds
that partition to the small-value sets of the e-adic cell polynomials and then
composes the already proved level estimates with the schedule arithmetic.
-/
namespace MoltResearch
/-- The prime polynomial carried by one e-adic cell of a level. -/
noncomputable def levelCellPoly (P : Finset ℕ) (N v : ℕ) (g : ℕ → ℂ)
    (xi : ℝ) : ℂ :=
  ∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
    * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)
/-! ## The exact level decomposition -/

/-- The repeated-prime fibre left by the Ramaré decomposition. -/
noncomputable def typicalSCollision (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (xi : ℝ) : ℂ :=
  ∑ p ∈ P, ∑ m ∈ (((typicalS A B rest).filter
      (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
    ((g (p * m) / ((p * m : ℕ) : ℂ))
        * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ))
      / (((P.filter (· ∣ (p * m))).card : ℂ))

noncomputable def typicalSQuotCoeff (g : ℕ → ℂ) (P S : Finset ℕ)
    (m : ℕ) : ℂ :=
  if m ∈ S then g m / (((P.filter (· ∣ m)).card : ℂ) + 1) else 0

/-- The `p ∣ m` terms added when a noncollision fibre is enlarged to its full
quotient support, grouped over the same e-adic cells as the main term. -/
noncomputable def typicalSAddedTerms (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (xi : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
    ((g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
      * ∑ m ∈ (((typicalS A B rest).filter
          (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
        ((g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          / (((P.filter (· ∣ m)).card : ℂ) + 1)

/-- The adjusted collision: N3-f's repeated-prime term minus the terms added
to make every main fibre a full quotient block. -/
noncomputable def typicalSAdjustedCollision (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (xi : ℝ) : ℂ :=
  typicalSCollision g A B P rest xi - typicalSAddedTerms g A B P rest N v₀ v₁ xi

noncomputable def typicalSCellUniformMain (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (q : ℕ → ℕ) (xi : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
    levelCellPoly P N v g xi
      * (∑ m ∈ Finset.Ioc (A / q v) (B / q v),
          (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
/-- The endpoint-replacement error between every prime's quotient block and
its cell representative's block. -/
noncomputable def typicalSCellReplacement (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (q : ℕ → ℕ) (xi : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
    ((g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
      * ((∑ m ∈ Finset.Ioc (A / p) (B / p),
            (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
        - (∑ m ∈ Finset.Ioc (A / q v) (B / q v),
            (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))

open MeasureTheory in
set_option linter.unusedVariables false in
/-- **The complete capstone-facing level leg, with the three analytic costs
separated.**

The exact decomposition supplies a cell-uniform main, the II-2e endpoint
replacement, and the adjusted repeated-prime collision.  If their square-split
energies cost shares `κ_main`, `κ_replace`, and `κ_collision`, then the two
successive `L²` triangles make the total unweighted cost
`2(κ_main+κ_replace+κ_collision)`.  Multiplying once by `(4H/A)²` and
checking that against `2⁻⁽ʲ⁺¹⁾` gives exactly the `hleg` shape of
`band_energy_typicalS_le`.

`band_energy_level_one_main_le_budget` or the later-level ladder supplies
`hmain`; `setIntegral_norm_sq_typicalSCellReplacement_le` followed by
`eadic_replacement_error_le_budget` supplies `hreplacement`.  The remaining
`hcollision` is deliberately separate because M-10 is a collar theorem, not a
repeated-prime theorem.
-/
theorem typicalS_level_leg_le_budget
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta H : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ)
    (K₁ K₂ T : ℝ) (J j : ℕ) (Pset : ℕ → Set ℝ)
    (hPset : ∀ i, MeasurableSet (Pset i))
    (hpartT : bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
      ⊆ Set.Ioc (-T) T)
    (kappaMain kappaReplacement kappaCollision c₃ eps : ℝ)
    (hc₃ : 0 ≤ c₃)
    (hmain : (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hreplacement : 2 * (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ kappaReplacement * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hcollision : 2 * (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
      ≤ (1 : ℝ) / 2 ^ (j + 1)) 
    (h_MoltResearch_continuous_typicalSCellReplacement : ∀ (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (q : ℕ → ℕ),
      Continuous (MoltResearch.typicalSCellReplacement g A B P rest N v₀ v₁ q))
    (h_MoltResearch_ExpSums_setIntegral_norm_add_sq_le : ∀ (F H : ℝ → ℂ),
      Continuous F →
        Continuous H →
          ∀ (T : ℝ) (G : Set ℝ),
            MeasurableSet G →
              G ⊆ Set.Ioc (-T) T →
                ∫ (ξ : ℝ) in G, ‖F ξ + H ξ‖ ^ 2 ≤
                  (2 * ∫ (ξ : ℝ) in G, ‖F ξ‖ ^ 2) + 2 * ∫ (ξ : ℝ) in G, ‖H ξ‖ ^ 2)
    (h_MoltResearch_continuous_typicalSCellUniformMain : ∀ (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (q : ℕ → ℕ),
      Continuous (MoltResearch.typicalSCellUniformMain g A B P rest N v₀ v₁ q))
    (h_MoltResearch_bandBudget_nonneg : ∀ (c₃ ε ρ : ℝ), 0 ≤ c₃ → 0 ≤ ρ → 0 ≤ MoltResearch.bandBudget c₃ ε ρ)
    (h_MoltResearch_continuous_typicalSAdjustedCollision : ∀ (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ),
      Continuous (MoltResearch.typicalSAdjustedCollision g A B P rest N v₀ v₁))
    (h_MoltResearch_measurableSet_inner_band : ∀ (K K₂ : ℝ), MeasurableSet {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂})
    (h_MoltResearch_bandPartOn_measurableSet : ∀ (P : ℕ → Set ℝ),
      (∀ (j : ℕ), MeasurableSet (P j)) →
        ∀ (J : ℕ) (G : Set ℝ),
          MeasurableSet G → ∀ (j : ℕ), MeasurableSet (MoltResearch.bandPartOn P J G j))
    (h_MoltResearch_typicalS_phase_eq_cellUniform_add_errors : ∀ (g : ℕ → ℂ),
      MoltResearch.CompletelyMultiplicativeC g →
        ∀ (A Delta : ℕ) (P : Finset ℕ),
          (∀ p ∈ P, Nat.Prime p) →
            ∀ (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ),
              (Finset.Ico v₀ (v₁ + 1)).biUnion (MoltResearch.eadicCell P (2 * N)) = P →
                (∀ p ∈ P,
                    ∀ (m : ℕ),
                      MoltResearch.HasFactorInAll rest (p * m) ↔ MoltResearch.HasFactorInAll rest m) →
                  ∀ (q : ℕ → ℕ) (xi : ℝ),
                    ∑ m ∈ MoltResearch.typicalS A (A + Delta) (P :: rest),
                        g m / (↑m : ℂ) *
                          (↑((Real.fourierChar : ℝ → Circle) (-(Real.log (↑m : ℝ) * xi))) : ℂ) =
                      MoltResearch.typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q xi +
                        (MoltResearch.typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q xi +
                          MoltResearch.typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi))
    :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (∫ xi in bandPartOn Pset J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (1 / 2 ^ (j + 1))
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  let Gpart := bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
  let main := typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q
  let replacement := typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q
  let collision := typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁
  have hGpart : MeasurableSet Gpart :=
    h_MoltResearch_bandPartOn_measurableSet Pset hPset J _ (h_MoltResearch_measurableSet_inner_band K₁ K₂) j
  have herror : 2 * (∫ xi in Gpart, ‖replacement xi + collision xi‖ ^ 2)
      ≤ (2 * (kappaReplacement + kappaCollision))
        * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    have hsplit := h_MoltResearch_ExpSums_setIntegral_norm_add_sq_le replacement collision
      (h_MoltResearch_continuous_typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q)
      (h_MoltResearch_continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁)
      T Gpart hGpart hpartT
    change 2 * (∫ xi in Gpart, ‖replacement xi‖ ^ 2)
      ≤ kappaReplacement * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
      at hreplacement
    change 2 * (∫ xi in Gpart, ‖collision xi‖ ^ 2)
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
      at hcollision
    linarith
  let F : ℝ → ℂ := fun xi =>
    ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
      * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
  let error : ℝ → ℂ := fun xi => replacement xi + collision xi
  have houter : (∫ xi in Gpart, ‖F xi‖ ^ 2)
      ≤ 2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
        + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2) := by
    calc
      (∫ xi in Gpart, ‖F xi‖ ^ 2) =
          ∫ xi in Gpart, ‖main xi + error xi‖ ^ 2 := by
            apply setIntegral_congr_fun hGpart
            intro xi _
            exact congrArg (· ^ 2) (congrArg norm
              (h_MoltResearch_typicalS_phase_eq_cellUniform_add_errors
                g hcm A Delta P hP rest N v₀ v₁ hcov hstable q xi))
      _ ≤ _ := h_MoltResearch_ExpSums_setIntegral_norm_add_sq_le main error
        (h_MoltResearch_continuous_typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q)
        ((h_MoltResearch_continuous_typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q).add
          (h_MoltResearch_continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁))
        T Gpart hGpart hpartT
  change (∫ xi in Gpart, ‖main xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) at hmain
  change 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)
      ≤ 2 * (kappaReplacement + kappaCollision)
        * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) at herror
  have hB0 : 0 ≤ bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) :=
    h_MoltResearch_bandBudget_nonneg c₃ eps _ hc₃ (by positivity)
  have hparts : 2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
        + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)
      ≤ (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    calc
      2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
          + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)
        ≤ 2 * (kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
            + 2 * (kappaReplacement + kappaCollision)
              * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by linarith
      _ = _ := by ring
  change (4 * (H : ℝ) / (A : ℝ)) ^ 2 * (∫ xi in Gpart, ‖F xi‖ ^ 2)
    ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
  calc
    (4 * (H : ℝ) / (A : ℝ)) ^ 2 * (∫ xi in Gpart, ‖F xi‖ ^ 2)
      ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * (2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
            + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left houter (sq_nonneg _)
    _ ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * ((2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))) :=
        mul_le_mul_of_nonneg_left hparts (sq_nonneg _)
    _ = ((4 * (H : ℝ) / (A : ℝ)) ^ 2
          * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision))
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by ring
    _ ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) :=
      mul_le_mul_of_nonneg_right hshare hB0
end MoltResearch
