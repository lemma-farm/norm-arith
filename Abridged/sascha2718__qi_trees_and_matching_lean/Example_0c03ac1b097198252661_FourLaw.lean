module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Support.Phi ====
public section
/-
The weight `φ_α t = t / (1-t)^α` at a *free* exponent `α`, together with the
elementary facts the support layer needs:

* `le_phi`              `t ≤ φ_α t` on `[0,1)`
* `one_sub_rpow_le`     the tangent line to `t ↦ t^α` at `t = 1` (Bernoulli)
* `rpow_neg_alpha_le`   `(1-t)^{-α} ≤ 1 + α φ_α(t)`
* `chord`               `(1-z)^{-α} ≤ 1 + c_α z` on `[0,1/2]`, `c_α = 2(2^α - 1)`
* `add_sq_le_weighted`  the weighted mean inequality behind `A_δ`

The exponent is a variable throughout.  The chord is proved from concavity
of `log` (both endpoint values of `z ↦ log(1+c_α z) + α log(1-z)` on
`[0,1/2]` vanish), which works for every `α ≥ 0`.
-/
@[expose] public section
namespace GraphMarkovMatching.Support
open Real
/-- `φ_α t = t / (1-t)^α`. The paper defines it on `[0,1)`; off that range
Lean's junk values apply and every lemma below carries `t < 1`. -/
noncomputable def phi (α t : ℝ) : ℝ := t / (1 - t) ^ α

/-! ### The chord bound at a free exponent

`(1-z)^{-α} ≤ 1 + c_α z` on `[0,1/2]` with the exact chord slope
`c_α = 2(2^α - 1)` through `(0,1)` and `(1/2, 2^α)`. At a free exponent the
proof uses concavity of `log`: the
function `g z = log(1 + c_α z) + α log(1-z)` satisfies `g 0 = g (1/2) = 0`
and is concave, hence nonnegative on `[0,1/2]`, and `exp g` is the claim. -/
end GraphMarkovMatching.Support

end
end

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Support.Potential ====
public section
/-
The countable probability space `(X, μ)` with a symmetric reflexive relation
`R`, the bad and good degrees `q` and `r`, and the potential `Φ(R,μ)`.

Design:

* `μ : PMF X`. Note this needs **no** `[Countable X]` hypothesis: a `PMF`
  sums to `1`, which forces its support to be countable automatically, so
  the standing countability assumption is encoded rather than assumed.
* No finiteness. Sums are `tsum`, and working in `ℝ≥0∞` makes them
  unconditionally summable by Fubini's theorem.
* `Φ` lands in `ℝ≥0∞`: the value `Φ = ∞` is meaningful and allowed.
-/
@[expose] public section
namespace GraphMarkovMatching.Support
open scoped ENNReal Classical
variable {X : Type*} {μ : PMF X} {R : X → X → Prop} {x y : X}
/-! ### The two degrees -/
/-- The good degree `r(x) = μ{y : x R y}` of Section 11.3. -/
noncomputable def rE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then μ y else 0
/-- The bad degree `q(x) = μ{y : ¬ x R y}` of Section 11.3. -/
noncomputable def qE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then 0 else μ y

noncomputable def q (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ := (qE μ R x).toReal

end GraphMarkovMatching.Support

end
end

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Potential.Directed ====
public section
/-
Directed potentials for two probability laws and a compatibility relation.
Two changes against the `Phi` of the support layer:

* **Directed**: the row law `μ` and the column law `ν` are different PMFs;
  the bad degree of a row point is measured against the column law. The
  support layer's `Phi α μ R` is the diagonal case `ν = μ`.
* **Safe at `q = 1`**: without reflexivity-on-support there is no guarantee
  that bad degrees stay below one, and `Real.rpow`'s junk value `0 ^ (-α) = 0`
  would silently zero out exactly the points that must contribute the most. The
  `ℝ≥0∞`-valued weight `phiE` is `⊤` at `q ≥ 1`, so finite potentials really
  do force `q < 1` wherever the row law charges, and the failure bound
  `𝔼 q ≤ Φ` holds unconditionally.

The `badInd` normal form `q_ν(z) = ∑' y, ν y · 𝟙[z ⋡ y]` makes the bad degree
linear in the column law, which is how the kernel mixture enters the step.
-/
@[expose] public section
namespace GraphMarkovMatching
open GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {X : Type u}
/-! ### The safe weight `phiE` -/
/-- The `ℝ≥0∞`-valued potential weight: `φ_α` below `1`, `⊤` from `1` on. -/
noncomputable def phiE (α t : ℝ) : ℝ≥0∞ :=
  if t < 1 then ENNReal.ofReal (phi α t) else ⊤

/-! ### The bad-degree normal form -/
end GraphMarkovMatching

end
end

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Potential.Inverse ====
public section
/-
Inverse powers of good degrees and their elementary potential bounds.
-/
@[expose] public section
namespace GraphMarkovMatching
open GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {X : Type u}
noncomputable def WnnD (α : ℝ) (ν : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - q ν R x) ^ (-α))

end GraphMarkovMatching

end
end

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Potential.Restricted ====
public section
/-
Directed potentials restricted to positive degree, their inverse moments and overlap identities.
-/
@[expose] public section
namespace GraphMarkovMatching
open GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {X : Type u}
noncomputable def PhiDres (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρs x * (if rE ρt R x = 0 then 0 else phiE α (q ρt R x))
noncomputable def zMass (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' y, ρs y * (if rE ρt R y = 0 then 1 else 0)
noncomputable def failureD (ρs ρt : PMF X) (R : X → X → Prop) : ℝ≥0∞ :=
  ∑' x, ρs x * qE ρt R x

noncomputable def WresD (α : ℝ) (ρt : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  if rE ρt R x = 0 then 0 else WnnD α ρt R x
noncomputable def HresD (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, ρs x * (if ¬ R x y then WresD α ρt R x else 0)
noncomputable def KresD (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, ρs x * (if ¬ R x y then
    (if rE ρt R x = 0 then 0 else phiE α (q ρt R x)) else 0)

section
variable {X : Type}
end
end GraphMarkovMatching

end
end

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Examples.Example_0c03ac1b097198252661_FourLaw ====
/-
The four-law contraction of `arbitrary_offspring_matching.tex`
(`thm:four-law-contraction`): for two source laws
`ρ₁, ρ₂` and two target laws `τ₁, τ₂` whose eight restricted directed potentials are
at most `M`, whose eight zero masses are at most `z`, and whose four weighted zero
integrals are at most `e`,

    P(ρ₁ × ρ₂, τ₁ × τ₂; R^□) ≤ a M + b M² + (γ + 4αM) z + 4 (1 + αM) e

with `a = 2 (L + K)`, `b = C_α(u)` and `γ = 2 + 2β`. The bound parameters `z` and `e`
are the paper's `δ₁` and `δ₂`, respectively. The proof integrates over the
doubly-positive set with the cancellation of the mean bad degrees between the source-row
terms and the target-overlap terms (`eq:four-law-rows`, `eq:four-law-overlaps`), and
handles the source pairs with a zero child degree by the resolved normalisation.

The scalar parameters `L`, `K`, `L0` enter as hypotheses, so that the exact maxima
`Lfun`, `Kfun` and rational surrogates are both admissible.

Organisation of the proof:

* `row_real`, `row_pt_gen`: the pointwise row estimate with the `s ≤ u` / `s > u`
  split (`eq:four-law-denominators`, the chord `chord_gen`, `eq:four-law-weight`);
* `main_pt`: the pointwise bound on a doubly-positive source pair
  (`eq:four-law-numerator` divided by `(r^□)^α`);
* `resPsi_pt`, `tsum_resPsi_le`: the product bound `eq:four-law-product` integrated
  over the positive set, carrying the mean bad degrees;
* `tsum_qE_sq_le`, `overlap_two_le`: the overlap estimate with the reversed potentials,
  `eq:four-law-square` and the `(1-β) z` term;
* `failureD_symm`, `failureD_le_resQ`: the identity behind the cancellation of `Q`;
* `PhiDres_square_split`: the pairs with a zero child degree, by the resolved
  normalisation;
* `fourLaw_contraction`: the assembly.
-/
@[expose] public section
namespace GraphMarkovMatching.Stopped
open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

/-! ### The pointwise row estimate -/

set_option linter.unusedVariables false in
/-- **One overlap integral** (`eq:four-law-overlaps`, one target law): with
`H_i ≤ q_{ρ_i} + αM`, the reversed potentials and `eq:four-law-square`,
`2 ∫ H₁ H₂ dτ ≤ 2KM + β (∫ q_{ρ₁} dτ + ∫ q_{ρ₂} dτ) + 2(1-β) z + 4αM² + 4αMz + 2α²M²`. -/
private lemma overlap_two_le {X : Type} {α β K : ℝ} (hα : 1 ≤ α) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K) (τ ρ₁ ρ₂ τa τb : PMF X)
    (R : X → X → Prop) (hsymm : ∀ a b, R a b → R b a) (M z : ℝ≥0∞)
    (h1 : PhiDres α ρ₁ τa R ≤ M) (h2 : PhiDres α ρ₂ τb R ≤ M)
    (hr1 : PhiDres α τ ρ₁ R ≤ M) (hr2 : PhiDres α τ ρ₂ R ≤ M)
    (hz1 : zMass τ ρ₁ R ≤ z) (hz2 : zMass τ ρ₂ R ≤ z) 
    (h_GraphMarkovMatching_KresD_le_PhiDres : ∀ {X : Type} (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X),
      GraphMarkovMatching.KresD α ρs ρt R y ≤ GraphMarkovMatching.PhiDres α ρs ρt R)
    (h_GraphMarkovMatching_Stopped_tsum_qE_sq_le : ∀ {X : Type} {α β K : ℝ},
      0 ≤ α →
        0 ≤ β →
          β ≤ 1 →
            (∀ (q : ℝ), 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K) →
              ∀ (τ ρ : PMF X) (R : X → X → Prop),
                ∑' (y : X), (τ : X → ENNReal) y * GraphMarkovMatching.Support.qE ρ R y ^ 2 ≤
                  ENNReal.ofReal K * GraphMarkovMatching.PhiDres α τ ρ R +
                      ENNReal.ofReal β * GraphMarkovMatching.failureD τ ρ R +
                    ENNReal.ofReal (1 - β) * GraphMarkovMatching.zMass τ ρ R)
    (h_GraphMarkovMatching_failureD_le_PhiDres_add_zMass : ∀ {X : Type} (α : ℝ),
      0 ≤ α →
        ∀ (ρs ρt : PMF X) (R : X → X → Prop),
          GraphMarkovMatching.failureD ρs ρt R ≤
            GraphMarkovMatching.PhiDres α ρs ρt R + GraphMarkovMatching.zMass ρs ρt R)
    (h_GraphMarkovMatching_HresD_le : ∀ {X : Type} {α : ℝ},
      1 ≤ α →
        ∀ (ρs ρt : PMF X) (R : X → X → Prop),
          (∀ (a b : X), R a b → R b a) →
            ∀ (y : X),
              GraphMarkovMatching.HresD α ρs ρt R y ≤
                GraphMarkovMatching.Support.qE ρs R y +
                  ENNReal.ofReal α * GraphMarkovMatching.KresD α ρs ρt R y)
    (h_GraphMarkovMatching_ennreal_two_mul_le_add_sq : ∀ (a b : ENNReal), 2 * (a * b) ≤ a ^ 2 + b ^ 2)
    :
    2 * ∑' y, τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)
      ≤ 2 * ENNReal.ofReal K * M
        + ENNReal.ofReal β * (failureD τ ρ₁ R + failureD τ ρ₂ R)
        + 2 * ENNReal.ofReal (1 - β) * z
        + 4 * ENNReal.ofReal α * M ^ 2 + 4 * ENNReal.ofReal α * M * z
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hH1 : ∀ y, HresD α ρ₁ τa R y ≤ qE ρ₁ R y + ENNReal.ofReal α * M := fun y =>
    (h_GraphMarkovMatching_HresD_le hα ρ₁ τa R hsymm y).trans
      (add_le_add le_rfl (mul_le_mul_right ((h_GraphMarkovMatching_KresD_le_PhiDres α ρ₁ τa R y).trans h1) _))
  have hH2 : ∀ y, HresD α ρ₂ τb R y ≤ qE ρ₂ R y + ENNReal.ofReal α * M := fun y =>
    (h_GraphMarkovMatching_HresD_le hα ρ₂ τb R hsymm y).trans
      (add_le_add le_rfl (mul_le_mul_right ((h_GraphMarkovMatching_KresD_le_PhiDres α ρ₂ τb R y).trans h2) _))
  have hpt : ∀ y, 2 * (τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y))
      ≤ τ y * qE ρ₁ R y ^ 2 + τ y * qE ρ₂ R y ^ 2
        + 2 * ENNReal.ofReal α * M * (τ y * qE ρ₁ R y + τ y * qE ρ₂ R y)
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 * τ y := by
    intro y
    calc 2 * (τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y))
        = τ y * (2 * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)) := by ring
      _ ≤ τ y * (HresD α ρ₁ τa R y ^ 2 + HresD α ρ₂ τb R y ^ 2) :=
          mul_le_mul_right (h_GraphMarkovMatching_ennreal_two_mul_le_add_sq _ _) _
      _ ≤ τ y * ((qE ρ₁ R y + ENNReal.ofReal α * M) ^ 2
          + (qE ρ₂ R y + ENNReal.ofReal α * M) ^ 2) := by
          gcongr
          · exact hH1 y
          · exact hH2 y
      _ = _ := by ring
  have hsq1 := h_GraphMarkovMatching_Stopped_tsum_qE_sq_le hα0 hβ0 hβ1 hK τ ρ₁ R
  have hsq2 := h_GraphMarkovMatching_Stopped_tsum_qE_sq_le hα0 hβ0 hβ1 hK τ ρ₂ R
  have hF1 : failureD τ ρ₁ R ≤ M + z :=
    (h_GraphMarkovMatching_failureD_le_PhiDres_add_zMass α hα0 τ ρ₁ R).trans (add_le_add hr1 hz1)
  have hF2 : failureD τ ρ₂ R ≤ M + z :=
    (h_GraphMarkovMatching_failureD_le_PhiDres_add_zMass α hα0 τ ρ₂ R).trans (add_le_add hr2 hz2)
  calc 2 * ∑' y, τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)
      = ∑' y, 2 * (τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)) :=
        ENNReal.tsum_mul_left.symm
    _ ≤ ∑' y, (τ y * qE ρ₁ R y ^ 2 + τ y * qE ρ₂ R y ^ 2
        + 2 * ENNReal.ofReal α * M * (τ y * qE ρ₁ R y + τ y * qE ρ₂ R y)
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 * τ y) := ENNReal.tsum_le_tsum hpt
    _ = (∑' y, τ y * qE ρ₁ R y ^ 2) + (∑' y, τ y * qE ρ₂ R y ^ 2)
        + 2 * ENNReal.ofReal α * M * (failureD τ ρ₁ R + failureD τ ρ₂ R)
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left,
          ENNReal.tsum_mul_left, ENNReal.tsum_add, PMF.tsum_coe, mul_one, failureD, failureD]
    _ ≤ (ENNReal.ofReal K * M + ENNReal.ofReal β * failureD τ ρ₁ R
          + ENNReal.ofReal (1 - β) * z)
        + (ENNReal.ofReal K * M + ENNReal.ofReal β * failureD τ ρ₂ R
          + ENNReal.ofReal (1 - β) * z)
        + 2 * ENNReal.ofReal α * M * ((M + z) + (M + z))
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 := by
        gcongr
        · exact hsq1.trans (add_le_add (add_le_add (mul_le_mul_right hr1 _) le_rfl)
            (mul_le_mul_right hz1 _))
        · exact hsq2.trans (add_le_add (add_le_add (mul_le_mul_right hr2 _) le_rfl)
            (mul_le_mul_right hz2 _))
    _ = _ := by ring
/-! ### The pairs with a zero child degree -/
end GraphMarkovMatching.Stopped
