/-
# Closed symmetric forms and Dirichlet forms on `L²`

This file is the base of a self-contained, reusable Dirichlet-form library.  It
imports only Mathlib, uses no carrier of the ambient project, and is written so
that the directory `SubdiffusiveProcess/DirichletForm/` can be lifted into a
standalone Lake package without changes.
-/
module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Algebra.QuadraticDiscriminant
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
# Closed symmetric forms and Dirichlet forms

Let `m` be a measure on a measurable space `X`.  A **closed form** on `L²(X, m)`
is a densely defined, symmetric, nonnegative bilinear form `E` whose domain
`D(E)` is a submodule of `L²(X, m)` complete for the energy norm
`E₁(u) = E(u, u) + ‖u‖²`.  A **Dirichlet form** is a closed form on which the
unit contraction `t ↦ (t ⊓ 1) ⊔ 0` operates.

## Main definitions

* `SubdiffusiveProcess.DirichletForm.ClosedForm m`: a densely defined, symmetric, nonnegative,
  closed bilinear form on `L²(X, m)`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.energyInner`, `SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq`:
  the energy inner product `E₁(u, v) = E(u, v) + ⟪u, v⟫` and `E₁(u) = E₁(u, u)`.
* `SubdiffusiveProcess.DirichletForm.IsNormalContraction`: `T : ℝ → ℝ` with `T 0 = 0` and
  `|T s - T t| ≤ |s - t|`.
* `SubdiffusiveProcess.DirichletForm.unitTruncation`: the unit contraction `t ↦ (t ⊓ 1) ⊔ 0`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.OperatesOn`: `T` operates on `E`, i.e. `T ∘ u` stays
  in `D(E)` and does not increase the energy.
* `SubdiffusiveProcess.DirichletForm`: a closed form on which `unitTruncation` operates.
* `SubdiffusiveProcess.DirichletForm.HasNormalContractions`: the Fukushima–Oshima–Takeda statement
  that *every* normal contraction operates on a Dirichlet form.

## Implementation notes

The bilinear form is carried as a total function `Lp ℝ 2 m → Lp ℝ 2 m → ℝ`; every
axiom is restricted to the domain, so the values off the domain carry no
information.  This keeps statements free of subtype coercions and matches the
way a form defined by a dual (resolvent) expression is met in practice.

## References

* M. Fukushima, Y. Oshima, M. Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, 2nd edition, de Gruyter, 2011.
-/
open MeasureTheory Filter Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]
namespace SubdiffusiveProcess.DirichletForm
/-- The unit contraction `t ↦ (t ⊓ 1) ⊔ 0` of the real line. -/
def unitTruncation (t : ℝ) : ℝ := max (min t 1) 0
structure ClosedForm (m : Measure X) where
  /-- The form domain `D(E)`, a linear subspace of `L²(X, m)`. -/
  domain : Submodule ℝ (Lp ℝ 2 m)
  /-- The bilinear form `E(u, v)`.  Values outside `domain` carry no
  information: every axiom below is restricted to `domain`. -/
  form : Lp ℝ 2 m → Lp ℝ 2 m → ℝ
  /-- `D(E)` is dense in `L²(X, m)`. -/
  denseDomain : Dense (domain : Set (Lp ℝ 2 m))
  /-- `E(u, v) = E(v, u)`. -/
  form_symm : ∀ u ∈ domain, ∀ v ∈ domain, form u v = form v u
  /-- `E` is additive in its first argument. -/
  form_add_left : ∀ u ∈ domain, ∀ v ∈ domain, ∀ w ∈ domain,
    form (u + v) w = form u w + form v w
  /-- `E` is homogeneous in its first argument. -/
  form_smul_left : ∀ c : ℝ, ∀ u ∈ domain, ∀ v ∈ domain, form (c • u) v = c * form u v
  /-- `E(u, u) ≥ 0`. -/
  form_nonneg : ∀ u ∈ domain, 0 ≤ form u u
  /-- `E` is closed: `D(E)` is complete for the energy norm
  `E₁(u) = E(u, u) + ‖u‖²`. -/
  complete : ∀ u : ℕ → Lp ℝ 2 m, (∀ n, u n ∈ domain) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      form (u p - u q) (u p - u q) + ‖u p - u q‖ ^ 2 < ε) →
    ∃ w ∈ domain, Tendsto
      (fun n => form (u n - w) (u n - w) + ‖u n - w‖ ^ 2) atTop (𝓝 0)
namespace ClosedForm
variable {m : Measure X} (E : ClosedForm m)
/-- `E(0, v) = 0`. -/
theorem form_zero_left {v : Lp ℝ 2 m} (hv : v ∈ E.domain) : E.form 0 v = 0 := by
  simpa using E.form_smul_left 0 0 E.domain.zero_mem v hv
theorem form_add_right {u v w : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hw : w ∈ E.domain) : E.form u (v + w) = E.form u v + E.form u w := by
  rw [E.form_symm u hu _ (E.domain.add_mem hv hw), E.form_add_left v hv w hw u hu,
    E.form_symm v hv u hu, E.form_symm w hw u hu]
/-- `E` is homogeneous in its second argument. -/
theorem form_smul_right (c : ℝ) {u v : Lp ℝ 2 m} (hu : u ∈ E.domain)
    (hv : v ∈ E.domain) : E.form u (c • v) = c * E.form u v := by
  rw [E.form_symm u hu _ (E.domain.smul_mem c hv), E.form_smul_left c v hv u hu,
    E.form_symm v hv u hu]
/-- `E(-u, v) = -E(u, v)`. -/
theorem form_neg_left {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (-u) v = -E.form u v := by
  simpa using E.form_smul_left (-1) u hu v hv
/-- `E(u, -v) = -E(u, v)`. -/
theorem form_neg_right {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form u (-v) = -E.form u v := by
  simpa using E.form_smul_right (-1) hu hv
/-- `E(u - v, w) = E(u, w) - E(v, w)`. -/
theorem form_sub_left {u v w : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hw : w ∈ E.domain) : E.form (u - v) w = E.form u w - E.form v w := by
  rw [sub_eq_add_neg, E.form_add_left u hu _ (E.domain.neg_mem hv) w hw,
    E.form_neg_left hv hw, sub_eq_add_neg]
/-- `E(u, v - w) = E(u, v) - E(u, w)`. -/
theorem form_sub_right {u v w : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hw : w ∈ E.domain) : E.form u (v - w) = E.form u v - E.form u w := by
  rw [sub_eq_add_neg, E.form_add_right hu hv (E.domain.neg_mem hw),
    E.form_neg_right hu hw, sub_eq_add_neg]
/-- Expansion of `E(u + v, u + v)`. -/
theorem form_add_self {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (u + v) (u + v) = E.form u u + 2 * E.form u v + E.form v v := by
  rw [E.form_add_left u hu v hv _ (E.domain.add_mem hu hv), E.form_add_right hu hu hv,
    E.form_add_right hv hu hv, E.form_symm v hv u hu]
  ring
/-- Expansion of `E(u + t • v, u + t • v)`. -/
theorem form_add_smul_self (t : ℝ) {u v : Lp ℝ 2 m} (hu : u ∈ E.domain)
    (hv : v ∈ E.domain) :
    E.form (u + t • v) (u + t • v) =
      E.form u u + 2 * t * E.form u v + t ^ 2 * E.form v v := by
  rw [E.form_add_self hu (E.domain.smul_mem t hv), E.form_smul_right t hu hv,
    E.form_smul_left t v hv _ (E.domain.smul_mem t hv), E.form_smul_right t hv hv]
  ring
def energyInner (u v : Lp ℝ 2 m) : ℝ := E.form u v + inner ℝ u v
/-- The squared energy norm `E₁(u) = E(u, u) + ‖u‖²`. -/
def energyNormSq (u : Lp ℝ 2 m) : ℝ := E.form u u + ‖u‖ ^ 2
theorem sq_norm_le_energyNormSq {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    ‖u‖ ^ 2 ≤ E.energyNormSq u := by
  have := E.form_nonneg u hu
  simp only [energyNormSq]
  linarith
/-- The energy norm is nonnegative. -/
theorem energyNormSq_nonneg {u : Lp ℝ 2 m} (hu : u ∈ E.domain) : 0 ≤ E.energyNormSq u := by
  have h := E.sq_norm_le_energyNormSq hu
  nlinarith [sq_nonneg ‖u‖]
/-- `E₁(-u) = E₁(u)`. -/
theorem energyNormSq_neg {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    E.energyNormSq (-u) = E.energyNormSq u := by
  rw [energyNormSq, energyNormSq, E.form_neg_left hu (E.domain.neg_mem hu),
    E.form_neg_right hu hu, norm_neg]
  ring
/-- `E₁(u - v) = E₁(v - u)`. -/
theorem energyNormSq_sub_comm {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.energyNormSq (u - v) = E.energyNormSq (v - u) := by
  rw [← E.energyNormSq_neg (E.domain.sub_mem hv hu), neg_sub]
theorem energyNormSq_add_smul_self (t : ℝ) {u v : Lp ℝ 2 m} (hu : u ∈ E.domain)
    (hv : v ∈ E.domain) :
    E.energyNormSq (u + t • v) =
      E.energyNormSq u + 2 * t * E.energyInner u v + t ^ 2 * E.energyNormSq v := by
  have hnorm : ‖u + t • v‖ ^ 2 = ‖u‖ ^ 2 + 2 * t * (inner ℝ u v : ℝ) + t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  simp only [energyNormSq, energyInner, E.form_add_smul_self t hu hv, hnorm]
  ring
/-- Cauchy–Schwarz for the energy inner product, in squared form. -/
theorem energyInner_sq_le_mul {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.energyInner u v ^ 2 ≤ E.energyNormSq u * E.energyNormSq v := by
  have key : ∀ t : ℝ,
      0 ≤ E.energyNormSq v * (t * t) + 2 * E.energyInner u v * t + E.energyNormSq u := by
    intro t
    have h := E.energyNormSq_nonneg (E.domain.add_mem hu (E.domain.smul_mem t hv))
    rw [E.energyNormSq_add_smul_self t hu hv] at h
    nlinarith [h]
  have h := discrim_le_zero key
  rw [discrim] at h
  nlinarith [h]
/-- Cauchy–Schwarz for the energy inner product: the energy space `(D(E), E₁)`
is a pre-Hilbert space, and it is complete by `ClosedForm.complete`. -/
theorem abs_energyInner_le {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    |E.energyInner u v| ≤ Real.sqrt (E.energyNormSq u) * Real.sqrt (E.energyNormSq v) := by
  have h := E.energyInner_sq_le_mul hu hv
  rw [← Real.sqrt_mul_self (abs_nonneg (E.energyInner u v)),
    ← Real.sqrt_mul (E.energyNormSq_nonneg hu)]
  refine Real.sqrt_le_sqrt ?_
  rw [abs_mul_abs_self, ← sq]
  exact h
/-- **Triangle inequality for the energy norm.**  `E₁^{1/2}` is a norm on the
domain, so a density argument can be run in two steps. -/
theorem sqrt_energyNormSq_add_le {u v : Lp ℝ 2 m} (hu : u ∈ E.domain)
    (hv : v ∈ E.domain) :
    Real.sqrt (E.energyNormSq (u + v)) ≤
      Real.sqrt (E.energyNormSq u) + Real.sqrt (E.energyNormSq v) := by
  have hexp : E.energyNormSq (u + v) =
      E.energyNormSq u + 2 * E.energyInner u v + E.energyNormSq v := by
    have h := E.energyNormSq_add_smul_self 1 hu hv
    simpa using h
  have hcs := E.abs_energyInner_le hu hv
  have hle : E.energyNormSq (u + v) ≤
      (Real.sqrt (E.energyNormSq u) + Real.sqrt (E.energyNormSq v)) ^ 2 := by
    have h1 : Real.sqrt (E.energyNormSq u) ^ 2 = E.energyNormSq u :=
      Real.sq_sqrt (E.energyNormSq_nonneg hu)
    have h2 : Real.sqrt (E.energyNormSq v) ^ 2 = E.energyNormSq v :=
      Real.sq_sqrt (E.energyNormSq_nonneg hv)
    have h3 : E.energyInner u v ≤
        Real.sqrt (E.energyNormSq u) * Real.sqrt (E.energyNormSq v) :=
      le_trans (le_abs_self _) hcs
    nlinarith [h1, h2, h3]
  have hnn : 0 ≤ Real.sqrt (E.energyNormSq u) + Real.sqrt (E.energyNormSq v) := by
    positivity
  calc Real.sqrt (E.energyNormSq (u + v))
      ≤ Real.sqrt ((Real.sqrt (E.energyNormSq u) + Real.sqrt (E.energyNormSq v)) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt (E.energyNormSq u) + Real.sqrt (E.energyNormSq v) :=
        Real.sqrt_sq hnn
end ClosedForm
end SubdiffusiveProcess.DirichletForm
/-- A **Dirichlet form** on `L²(X, m)`: a closed symmetric nonnegative form on
which the unit contraction `t ↦ (t ⊓ 1) ⊔ 0` operates.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroDirichletForm`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
structure SubdiffusiveProcess.DirichletForm (m : Measure X) extends _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m where
  /-- The Markov property: the unit contraction operates on `E`. -/
  markov : ∀ u ∈ domain, ∀ v : Lp ℝ 2 m,
    (⇑v =ᵐ[m] fun x => _root_.SubdiffusiveProcess.DirichletForm.unitTruncation (u x)) →
    v ∈ domain ∧ form v v ≤ form u u
namespace SubdiffusiveProcess.DirichletForm
variable {m : Measure X}
/-- The unit contraction fixes the origin. -/
@[simp] theorem unitTruncation_zero : unitTruncation 0 = 0 := by
  simp [unitTruncation]
/-- The unit contraction is `1`-Lipschitz. -/
theorem lipschitzWith_unitTruncation : LipschitzWith 1 unitTruncation := by
  change LipschitzWith 1 (fun x : ℝ => max (min x 1) 0)
  simpa using
    (LipschitzWith.id.min (LipschitzWith.const (1 : ℝ))).max (LipschitzWith.const (0 : ℝ))
end SubdiffusiveProcess.DirichletForm
