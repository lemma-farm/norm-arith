module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Support.Phi ====
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

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Support.Potential ====
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

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Support.Product ====
public section
/-
The product of relations:

    Phi(R1 (x) R2, mu1 (x) mu2)  <=  Phi1 + Phi2 + 5 * Phi1 * Phi2

Mathlib has no `PMF.prod`, so `prodPMF` is built here from the `HasSum`
characterisation.

The constant `5` is `2 * alpha`, and the proof is: the good set of
`(x1,x2)` is a rectangle of mass `r1 * r2`, so `q = 1 - r1 r2 <= q1 + q2`,
whence `phi q <= phi q1 * r2^(-alpha) + phi q2 * r1^(-alpha)`; then apply
`rpow_neg_alpha_le` to each `r^(-alpha)` and use independence.
-/
@[expose] public section
namespace GraphMarkovMatching.Support
open scoped ENNReal Classical
variable {X₁ X₂ : Type*}
/-! ### The product measure and the product relation -/
/-- The product PMF, `(μ₁ ⊗ μ₂)(x₁,x₂) = μ₁ x₁ · μ₂ x₂`. Not in Mathlib, so
constructed here: in `ℝ≥0∞` summability is automatic, so only the total mass
needs checking. -/
noncomputable def prodPMF (μ₁ : PMF X₁) (μ₂ : PMF X₂) : PMF (X₁ × X₂) :=
  ⟨fun p => μ₁ p.1 * μ₂ p.2, by
    have h : ∑' p : X₁ × X₂, μ₁ p.1 * μ₂ p.2 = 1 := by
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left, μ₂.tsum_coe, mul_one]
      exact μ₁.tsum_coe
    rw [← h]
    exact ENNReal.summable.hasSum⟩
@[simp] axiom prodPMF_apply (μ₁ : PMF X₁) (μ₂ : PMF X₂) (p : X₁ × X₂) :
    prodPMF μ₁ μ₂ p = μ₁ p.1 * μ₂ p.2

end GraphMarkovMatching.Support

end
end

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Support.Square ====
public section
/-
The symmetrised square `R^□` of a relation and the setup for the
contraction lemma.

This file fixes the definitions and the structural facts:

* `SquareRel`      the symmetrised square relation on `X × X`
* refl / symm      preserved from `R`, as required to feed `R^□` back into
                   the contraction
* `aOverlap`       `a = μ{y : x₀ R y ∧ x₁ R y}`, the both-compatible overlap
* `cOverlap`       `c = μ{y : x₀ ⋡ y ∧ x₁ ⋡ y}`, the neither-compatible mass
* `aOverlap_le_rE` `a ≤ r_i`, since a single `Y` compatible with both is in
                   particular compatible with each (so `a ≤ min(r₀,r₁)`)

The degree identities and the contraction estimate itself are in
`Contraction.lean`.
-/
@[expose] public section
namespace GraphMarkovMatching.Support
open scoped ENNReal Classical
variable {X : Type*}
/-! ### The symmetrised square, equation (11.13) -/
/-- The symmetrised square `R^□` of equation (11.13):
`(x₀,x₁) R^□ (y₀,y₁) ↔ (x₀ R y₀ ∧ x₁ R y₁) ∨ (x₀ R y₁ ∧ x₁ R y₀)`.

The second disjunct crosses the coordinates; this is what distinguishes `R^□`
from the tensor square `ProdRel R R`, and it is exactly the "good antidiagonal"
of the transversal Lemma 11.4. -/
def SquareRel (R : X → X → Prop) : X × X → X × X → Prop :=
  fun x y => (R x.1 y.1 ∧ R x.2 y.2) ∨ (R x.1 y.2 ∧ R x.2 y.1)

/-- The paper's `c = μ{y : x₀ ⋡ y ∧ x₁ ⋡ y}`: the mass of labels incompatible
with both. This is the per-column bad probability in the transversal argument. -/
noncomputable def cOverlap (μ : PMF X) (R : X → X → Prop) (x₀ x₁ : X) : ℝ≥0∞ :=
  ∑' y, if ¬ R x₀ y ∧ ¬ R x₁ y then μ y else 0

end GraphMarkovMatching.Support

end
end

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Potential.Directed ====
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

end GraphMarkovMatching

end
end

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Stopped.Scalar ====
public section
/-
The scalar functions of `arbitrary_offspring_matching.tex` (`eq:mean-constants`,
`eq:four-law-constants`) and the pointwise inequalities of the four-law
contraction (`eq:four-law-product` to `eq:four-law-weight`):

* `Lfun α β = max_{0 ≤ q ≤ 1} (q/(1+q)^α + β (1-q)^α)`, as a supremum;
* `Kfun α β = α^α/(α+1)^{α+1} (1-β)^{α+1}`, the maximum of `(q-β)(1-q)^α` on `[0,1]`;
* `lambda α = 2 min_{0 ≤ β ≤ 1} (Lfun α β + Kfun α β)`, the exponent condition `lambda α < 1`;
* `Cfun α L0 u = 4 L0 ((1-u)^{-α} - 1)/u + 4/u + 8α + 2α²`, the quadratic coefficient;
* `phi_sq_le`, `phi_mul_le_beta`: `φ(q²) ≤ L φ(q) - β q` and the product bound
  `φ(xy) ≤ (L/2)(φ(x) + φ(y)) - (β/2)(x + y)`;
* `sq_le_K_phi_add`: `q² ≤ K φ(q) + β q`;
* `chord_gen`: the chord `(1-s)^{-α} ≤ 1 + c s` on `[0,u]`, `c = ((1-u)^{-α} - 1)/u`;
* `rpow_one_sub_le`: `s^{1-α} ≤ 1 + (α-1)(1-s)/s^α` on `(0,1]`;
* the explicit values of `Lfun α 0` and the closed form of `Kfun` as a maximum;
* `exists_beta_of_lambda_lt_one`, `exists_beta_min`: a minimising `β` exists, and the
  exponent condition supplies a `β` with `2 (L + K) < 1`;
* `amgm_pow`: weighted AM–GM in the power form `y x^γ ≤ ((y + γx)/(γ+1))^{γ+1}`, behind
  both the maximum `K_α(β)` and the value of `L_α` for `α ≥ 2`.

The parameters `L`, `K`, `L0` enter the four-law contraction as hypotheses (the bounds
`le_Lfun`, `Kfun_bound`, `le_Lfun` at `β = 0`), so that rational surrogates can replace
the exact maxima in numerical instances.
-/
@[expose] public section
namespace GraphMarkovMatching.Stopped
open GraphMarkovMatching.Support Real
/-! ### The scalar functions -/
noncomputable def chordSlope (α u : ℝ) : ℝ := ((1 - u) ^ (-α) - 1) / u
/-! ### Weighted AM–GM in power form

`y x^γ ≤ ((y + γ x)/(γ+1))^{γ+1}` for `x, y ≥ 0` and `γ ≥ 0`: the two-point weighted
AM–GM inequality with weights `1/(γ+1)`, `γ/(γ+1)`, raised to the power `γ + 1`. It
supplies the maximum of `(q-β)(1-q)^α` (`Kfun_bound`) and the value of `L_α` for
`α ≥ 2` (`Lfun_zero_eq_of_two_le`). -/

end GraphMarkovMatching.Stopped

end
end

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Potential.Degrees ====
public section
/-
Good degrees under pure laws, maps and mixtures, and independent product laws.
-/
@[expose] public section
namespace GraphMarkovMatching
open GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {X : Type u}

axiom tsum_mass_prod (μ₀ μ₁ : PMF X) (F G : X → ℝ≥0∞) :
    ∑' p : X × X, prodPMF μ₀ μ₁ p * (F p.1 * G p.2)
      = (∑' x, μ₀ x * F x) * (∑' x, μ₁ x * G x)
end GraphMarkovMatching

end
end

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Potential.Inverse ====
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

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Potential.Restricted ====
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
noncomputable def WresD (α : ℝ) (ρt : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  if rE ρt R x = 0 then 0 else WnnD α ρt R x
noncomputable def HresD (α : ℝ) (ρs ρt : PMF X) (R : X → X → Prop) (y : X) : ℝ≥0∞ :=
  ∑' x, ρs x * (if ¬ R x y then WresD α ρt R x else 0)

axiom fubini_swap_two_res (α : ℝ) (μ₀ μ₁ νc ν₀ ν₁ : PMF X)
    (R : X → X → Prop) :
    ∑' p : X × X, μ₀ p.1 * μ₁ p.2
        * (cOverlap νc R p.1 p.2 * (WresD α ν₀ R p.1 * WresD α ν₁ R p.2))
      = ∑' y, νc y * (HresD α μ₀ ν₀ R y * HresD α μ₁ ν₁ R y)
section
variable {X : Type}

end
end GraphMarkovMatching

end
end

-- ==== Examples.sascha2718__qi_trees_and_matching_lean.Examples.Example_70643fbe255e136f248c_FourLaw ====
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

/-- **The pointwise bound on a doubly-positive pair** (`thm:four-law-contraction`):
`eq:four-law-numerator` divided by `(r^□)^α`, the two row terms estimated by
`row_pt_gen` and the two overlap terms by `eq:four-law-denominators`. -/
axiom main_pt {X : Type} {α u : ℝ} (hα : 1 ≤ α) (hu0 : 0 < u) (hu1 : u < 1)
    (τ₁ τ₂ : PMF X) (R : X → X → Prop) (x₁ x₂ : X)
    (h11 : rE τ₁ R x₁ ≠ 0) (h12 : rE τ₂ R x₁ ≠ 0)
    (h21 : rE τ₁ R x₂ ≠ 0) (h22 : rE τ₂ R x₂ ≠ 0) :
    phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) (x₁, x₂))
      ≤ phiE α (q τ₁ R x₁ * q τ₂ R x₁)
          * (1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₂ + qE τ₂ R x₂))
        + phiE α (q τ₁ R x₁)
          * ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (phiE α (q τ₁ R x₂) + phiE α (q τ₂ R x₂)))
        + (1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₁ + qE τ₂ R x₁))
          * phiE α (q τ₁ R x₂ * q τ₂ R x₂)
        + ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (phiE α (q τ₁ R x₁) + phiE α (q τ₂ R x₁)))
          * phiE α (q τ₂ R x₂)
        + cOverlap τ₁ R x₁ x₂ * (WresD α τ₁ R x₁ * WresD α τ₂ R x₂)
        + cOverlap τ₂ R x₁ x₂ * (WresD α τ₂ R x₁ * WresD α τ₁ R x₂)
/-! ### The restricted summands -/
/-- The indicator of the doubly-positive set `F = {r_{τ₁} > 0, r_{τ₂} > 0}`. -/
private noncomputable def dpInd {X : Type} (τ₁ τ₂ : PMF X) (R : X → X → Prop) (x : X) :
    ℝ≥0∞ :=
  if rE τ₁ R x = 0 ∨ rE τ₂ R x = 0 then 0 else 1
/-- The restricted potential summand `𝟙[r_τ > 0] φ(q_τ)`. -/
private noncomputable def resPhi {X : Type} (α : ℝ) (τ : PMF X) (R : X → X → Prop) (x : X) :
    ℝ≥0∞ :=
  if rE τ R x = 0 then 0 else phiE α (q τ R x)
/-- The restricted product summand `𝟙_F φ(q_{τ₁} q_{τ₂})` of `I_i`. -/
private noncomputable def resPsi {X : Type} (α : ℝ) (τ₁ τ₂ : PMF X) (R : X → X → Prop)
    (x : X) : ℝ≥0∞ :=
  dpInd τ₁ τ₂ R x * phiE α (q τ₁ R x * q τ₂ R x)
/-- The restricted bad degree `𝟙_F q_τ`. -/
private noncomputable def resQ {X : Type} (τ₁ τ₂ τ : PMF X) (R : X → X → Prop) (x : X) :
    ℝ≥0∞ :=
  dpInd τ₁ τ₂ R x * qE τ R x
/-- The chord factor `1 + c (q_{τ₁} + q_{τ₂})` on `F`. -/
private noncomputable def chordFac {X : Type} (cb : ℝ≥0∞) (τ₁ τ₂ : PMF X) (R : X → X → Prop)
    (x : X) : ℝ≥0∞ :=
  1 + cb * (resQ τ₁ τ₂ τ₁ R x + resQ τ₁ τ₂ τ₂ R x)
/-- The weight factor `(u⁻¹ + α)(φ(q_{τ₁}) + φ(q_{τ₂}))` on the positive sets. -/
private noncomputable def weightFac {X : Type} (k : ℝ≥0∞) (α : ℝ) (τ₁ τ₂ : PMF X)
    (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  k * (resPhi α τ₁ R x + resPhi α τ₂ R x)
/-- The restricted potential is the integral of `resPhi` (`thm:four-law-contraction`). -/
private axiom PhiDres_eq_resPhi {X : Type} (α : ℝ) (ρ τ : PMF X) (R : X → X → Prop) :
    PhiDres α ρ τ R = ∑' x, ρ x * resPhi α τ R x
private axiom dpInd_eq_one {X : Type} {τ₁ τ₂ : PMF X} {R : X → X → Prop} {x : X}
    (h₁ : rE τ₁ R x ≠ 0) (h₂ : rE τ₂ R x ≠ 0) : dpInd τ₁ τ₂ R x = 1
/-- **Rows and overlaps** (`thm:four-law-contraction`): the integral of the square
potential over `F₁ × F₂` is at most the four row products of `eq:four-law-rows` and the
two overlap integrals `∫ H₁¹ H₂² dτ₁`, `∫ H₁² H₂¹ dτ₂` (`fubini_swap_two_res`). -/
private lemma main_sum_le {X : Type} {α u : ℝ} (hα : 1 ≤ α) (hu0 : 0 < u) (hu1 : u < 1)
    (ρ₁ ρ₂ τ₁ τ₂ : PMF X) (R : X → X → Prop) :
    ∑' p : X × X, prodPMF ρ₁ ρ₂ p * (dpInd τ₁ τ₂ R p.1 * dpInd τ₁ τ₂ R p.2
        * phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) p))
      ≤ (∑' x, ρ₁ x * resPsi α τ₁ τ₂ R x)
          * (∑' x, ρ₂ x * chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x)
        + PhiDres α ρ₁ τ₁ R
          * (∑' x, ρ₂ x
              * weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x)
        + (∑' x, ρ₁ x * chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x)
          * (∑' x, ρ₂ x * resPsi α τ₁ τ₂ R x)
        + (∑' x, ρ₁ x
              * weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x)
          * PhiDres α ρ₂ τ₂ R
        + (∑' y, τ₁ y * (HresD α ρ₁ τ₁ R y * HresD α ρ₂ τ₂ R y))
        + (∑' y, τ₂ y * (HresD α ρ₁ τ₂ R y * HresD α ρ₂ τ₁ R y)) := by
  have hpt : ∀ p : X × X, prodPMF ρ₁ ρ₂ p * (dpInd τ₁ τ₂ R p.1 * dpInd τ₁ τ₂ R p.2
        * phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) p))
      ≤ prodPMF ρ₁ ρ₂ p * (resPsi α τ₁ τ₂ R p.1
            * chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p * (resPhi α τ₁ R p.1
            * weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p * (chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R p.1
            * resPsi α τ₁ τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p
          * (weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R p.1
            * resPhi α τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p
          * (cOverlap τ₁ R p.1 p.2 * (WresD α τ₁ R p.1 * WresD α τ₂ R p.2))
        + prodPMF ρ₁ ρ₂ p
          * (cOverlap τ₂ R p.1 p.2 * (WresD α τ₂ R p.1 * WresD α τ₁ R p.2)) := by
    rintro ⟨x₁, x₂⟩
    by_cases h1 : rE τ₁ R x₁ = 0 ∨ rE τ₂ R x₁ = 0
    · have h0 : dpInd τ₁ τ₂ R x₁ = 0 := by unfold dpInd; rw [ite_eq_left h1]
      simp only [h0, zero_mul, mul_zero]
      exact zero_le
    by_cases h2 : rE τ₁ R x₂ = 0 ∨ rE τ₂ R x₂ = 0
    · have h0 : dpInd τ₁ τ₂ R x₂ = 0 := by unfold dpInd; rw [ite_eq_left h2]
      simp only [h0, zero_mul, mul_zero]
      exact zero_le
    push Not at h1 h2
    obtain ⟨h11, h12⟩ := h1
    obtain ⟨h21, h22⟩ := h2
    have e1 : dpInd τ₁ τ₂ R x₁ = 1 := dpInd_eq_one h11 h12
    have e2 : dpInd τ₁ τ₂ R x₂ = 1 := dpInd_eq_one h21 h22
    have hmain := main_pt hα hu0 hu1 τ₁ τ₂ R x₁ x₂ h11 h12 h21 h22
    have f1 : resPsi α τ₁ τ₂ R x₁ = phiE α (q τ₁ R x₁ * q τ₂ R x₁) := by
      rw [resPsi, e1, one_mul]
    have f2 : resPsi α τ₁ τ₂ R x₂ = phiE α (q τ₁ R x₂ * q τ₂ R x₂) := by
      rw [resPsi, e2, one_mul]
    have g1 : chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x₁
        = 1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₁ + qE τ₂ R x₁) := by
      rw [chordFac, resQ, resQ, e1, one_mul, one_mul]
    have g2 : chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x₂
        = 1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₂ + qE τ₂ R x₂) := by
      rw [chordFac, resQ, resQ, e2, one_mul, one_mul]
    have p11 : resPhi α τ₁ R x₁ = phiE α (q τ₁ R x₁) := by rw [resPhi, ite_eq_right h11]
    have p12 : resPhi α τ₂ R x₁ = phiE α (q τ₂ R x₁) := by rw [resPhi, ite_eq_right h12]
    have p21 : resPhi α τ₁ R x₂ = phiE α (q τ₁ R x₂) := by rw [resPhi, ite_eq_right h21]
    have p22 : resPhi α τ₂ R x₂ = phiE α (q τ₂ R x₂) := by rw [resPhi, ite_eq_right h22]
    have w1 : weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x₁
        = (ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
          * (phiE α (q τ₁ R x₁) + phiE α (q τ₂ R x₁)) := by
      rw [weightFac, p11, p12]
    have w2 : weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x₂
        = (ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
          * (phiE α (q τ₁ R x₂) + phiE α (q τ₂ R x₂)) := by
      rw [weightFac, p21, p22]
    simp only [e1, e2, one_mul, f1, f2, g1, g2, p11, p22, w1, w2]
    refine le_trans (mul_le_mul_right hmain _) (le_of_eq ?_)
    ring
  have hov1 : ∑' p : X × X, prodPMF ρ₁ ρ₂ p
        * (cOverlap τ₁ R p.1 p.2 * (WresD α τ₁ R p.1 * WresD α τ₂ R p.2))
      = ∑' y, τ₁ y * (HresD α ρ₁ τ₁ R y * HresD α ρ₂ τ₂ R y) := by
    rw [← fubini_swap_two_res]
    exact tsum_congr fun p => by rw [prodPMF_apply]
  have hov2 : ∑' p : X × X, prodPMF ρ₁ ρ₂ p
        * (cOverlap τ₂ R p.1 p.2 * (WresD α τ₂ R p.1 * WresD α τ₁ R p.2))
      = ∑' y, τ₂ y * (HresD α ρ₁ τ₂ R y * HresD α ρ₂ τ₁ R y) := by
    rw [← fubini_swap_two_res]
    exact tsum_congr fun p => by rw [prodPMF_apply]
  refine le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ?_)
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add,
    ENNReal.tsum_add, hov1, hov2,
    tsum_mass_prod ρ₁ ρ₂ (resPsi α τ₁ τ₂ R)
      (chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R),
    tsum_mass_prod ρ₁ ρ₂ (resPhi α τ₁ R)
      (weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R),
    tsum_mass_prod ρ₁ ρ₂ (chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R)
      (resPsi α τ₁ τ₂ R),
    tsum_mass_prod ρ₁ ρ₂
      (weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R)
      (resPhi α τ₂ R),
    ← PhiDres_eq_resPhi, ← PhiDres_eq_resPhi]
/-! ### The assembly -/
end GraphMarkovMatching.Stopped
