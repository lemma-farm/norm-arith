module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.vad256e1f7ac4.SubdiffusiveProcess.Sobolev.WeakGradient ====
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
# The actual weak-gradient graph

Spatial coordinates use the usual finite product, with its sup norm. Gradient
energy will use the sum of squared coordinate L2 norms, not that sup norm.
The graph below imposes the distributional derivative identity against every
smooth function compactly supported in the open domain. It does not assume
an abstract space has the properties of a Sobolev space.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
namespace SubdiffusiveProcess
noncomputable section
abbrev SpatialCoordinates (d : ℕ) := Fin d → ℝ
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
end
end SubdiffusiveProcess

end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.vad256e1f7ac4.SubdiffusiveProcess.ResponseMoments.Interfaces ====
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
# Response interfaces: responses, the moment bank and the Efron--Stein input

Carriers for the resampling and comparison chain of

* `SubdiffusiveProcess.ResponseMoments.Potential` is the bounded-potential carrier already used by
  `expPotentialCoefficient`.
* `SubdiffusiveProcess.ResponseMoments.Response` bundles the two *proved* properties of a response that the
  whole of Subsection `mfd:sec-resampling` uses: the multiplicative comparison
  `eq:mfd-mult`  and the localized perturbation
  estimates `eq:mfd-14`.  Both the Dirichlet response
  and the killed inverse response are instances, by
  `boundary_responses_potential_stability` and
  `source_responses_potential_stability` in `Sobolev/PotentialPerturbation`
  together with `dirichletResponse_potential_comparison` and
  `inverseResponse_potential_comparison` in `Sobolev/PotentialResponses`.
* `SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality` is the foundational input of the paper,
  `eq:mfd-ES`, i.e. Theorem 2 of BBLM 2005.  It is a
  `Prop`-valued hypothesis structure; it is never an axiom, and every theorem
  that uses it carries it as an explicit binder.

No statement in this file asserts any conclusion of the paper.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
namespace ResponseMoments
variable {d : ℕ}
/-- The bounded potentials on a cube: the carrier consumed by
`expPotentialCoefficient`.  Its norm is the essential supremum. -/
abbrev Potential (Q : Opens (SpatialCoordinates d)) :=
  Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))
/-- A *response* in the sense of the paper, : a nonnegative
functional `eval g` of the potential together with the energy measure `mass g`
of its minimizer.  The fields are exactly the properties proved in
`Sobolev/PotentialPerturbation` and `Sobolev/PotentialResponses`; nothing that
the paper proves later is assumed here. -/
structure Response (Q : Opens (SpatialCoordinates d)) where
  /-- The response `𝓡(g)` computed with the coefficient `e ^ g`. -/
  eval : Potential Q → ℝ
  /-- The energy measure `Γ(u^g)(B)` of the corresponding minimizer. -/
  mass : Potential Q → Set (SpatialCoordinates d) → ℝ
  eval_nonneg : ∀ g, 0 ≤ eval g
  mass_nonneg : ∀ g s, 0 ≤ mass g s
  mass_mono : ∀ g s t, MeasurableSet s → MeasurableSet t → s ⊆ t →
    mass g s ≤ mass g t
  /-- The total energy of the minimizer is the response. -/
  mass_univ : ∀ g, mass g Set.univ = eval g
  /-- `eq:mfd-mult`. -/
  exp_comparison : ∀ g h, eval g ≤ Real.exp ‖g - h‖ * eval h
  /-- The response bound in `eq:mfd-14`. -/
  response_perturbation : ∀ (h g : Potential Q) (s : Set (SpatialCoordinates d)),
    MeasurableSet s →
    (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), x ∉ s → g x = 0) →
    |eval (h + g) - eval h| ≤ 2 * ‖g‖ * Real.exp (4 * ‖g‖) * mass h s
  /-- The local-energy bound in `eq:mfd-14`, with the constant
  supplied by `boundary_responses_potential_stability` and
  `source_responses_potential_stability`: `δ = ‖g‖ e^{‖g‖}`, `c = e^{-‖g‖}`,
  `M = e^{‖g‖}`, so `2 M (1 + δ²/c²) = 2 e^{‖g‖} (1 + ‖g‖² e^{4‖g‖})`.  Like the
  paper's `4 e^{S}` it is of the form `C e^{C S}` with an extra factor `S²`,
  which the moment bank  absorbs (it only adds powers
  of the disorder). -/
  mass_perturbation : ∀ (h g : Potential Q) (s : Set (SpatialCoordinates d)),
    MeasurableSet s →
    (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), x ∉ s → g x = 0) →
    mass (h + g) s ≤
      2 * Real.exp ‖g‖ * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) * mass h s
namespace Response
variable {Q : Opens (SpatialCoordinates d)}
end Response

end ResponseMoments
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_c969baac900cd5f0aa3b_ResponseOfExpComparison ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
namespace ResponseMoments
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}
set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.ResponseMoments.aux_response_real_perturb : ∀ (x E Y : ℝ),
  0 ≤ x → 0 ≤ Y → E ≤ Real.exp x * Y → Y ≤ Real.exp x * E → |E - Y| ≤ 2 * x * Real.exp (4 * x) * Y
/-- Generic `Response` smart constructor: any nonnegative `eval` with an `exp_comparison`-shaped
bound gives a full `Response`, via the trivial mass choice `mass g _ := eval g`. -/
def Response.ofExpComparison (eval : Potential Q → ℝ) (eval_nonneg : ∀ g, 0 ≤ eval g)
    (exp_cmp : ∀ g h, eval g ≤ Real.exp ‖g - h‖ * eval h) : Response Q where
  eval := eval
  mass g _ := eval g
  eval_nonneg := eval_nonneg
  mass_nonneg g _ := eval_nonneg g
  mass_mono _ _ _ _ _ _ := le_rfl
  mass_univ _ := rfl
  exp_comparison := exp_cmp
  response_perturbation h g _ _ _ := by
    apply aux_response_real_perturb ‖g‖ _ _ (norm_nonneg g) (eval_nonneg h)
    · have := exp_cmp (h + g) h
      rwa [add_sub_cancel_left] at this
    · have := exp_cmp h (h + g)
      rwa [sub_add_cancel_left, norm_neg] at this
  mass_perturbation h g _ _ _ := by
    have hc := exp_cmp (h + g) h
    rw [add_sub_cancel_left] at hc
    have hn := eval_nonneg h
    have h1 : 1 ≤ 2 * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) := by
      nlinarith [sq_nonneg ‖g‖, Real.exp_pos (4 * ‖g‖), mul_nonneg (sq_nonneg ‖g‖)
        (Real.exp_pos (4 * ‖g‖)).le]
    calc eval (h + g) ≤ Real.exp ‖g‖ * eval h := hc
      _ ≤ 2 * Real.exp ‖g‖ * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) * eval h := by
          have hE := Real.exp_pos ‖g‖
          nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hE.le hn)]
end ResponseMoments
end SubdiffusiveProcess
