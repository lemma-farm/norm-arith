module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.UrysohnsLemma

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v89daeff8b337.SubdiffusiveProcess.DirichletForm.Basic ====
public section
/-
# Closed symmetric forms and Dirichlet forms on `L²`

This file is the base of a self-contained, reusable Dirichlet-form library.  It
imports only Mathlib, uses no carrier of the ambient project, and is written so
that the directory `SubdiffusiveProcess/DirichletForm/` can be lifted into a
standalone Lake package without changes.
-/
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

/-- A densely defined, symmetric, nonnegative bilinear form on `L²(X, m)` which
is closed for the energy norm.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroClosedForm`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
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

end SubdiffusiveProcess.DirichletForm

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v89daeff8b337.SubdiffusiveProcess.DirichletForm.FOTLocalityClosure ====
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
open MeasureTheory Filter Set Topology
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess.DirichletForm
variable {X : Type*} [MeasurableSpace X] {m : Measure X}
namespace ClosedForm
set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.form_add_self_le.{w_u_1} : ∀ {X : Type w_u_1} [inst : MeasurableSpace X] {m : MeasureTheory.Measure X}
  (E : SubdiffusiveProcess.DirichletForm.ClosedForm m) {u v : ↥(MeasureTheory.Lp ℝ 2 m)},
  u ∈ E.domain → v ∈ E.domain → E.form (u + v) (u + v) ≤ 2 * E.form u u + 2 * E.form v v
set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.form_sub_self_le.{w_u_1} : ∀ {X : Type w_u_1} [inst : MeasurableSpace X] {m : MeasureTheory.Measure X}
  (E : SubdiffusiveProcess.DirichletForm.ClosedForm m) {u v : ↥(MeasureTheory.Lp ℝ 2 m)},
  u ∈ E.domain → v ∈ E.domain → E.form (u - v) (u - v) ≤ 2 * E.form u u + 2 * E.form v v
set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.form_smul_self.{w_u_1} : ∀ {X : Type w_u_1} [inst : MeasurableSpace X] {m : MeasureTheory.Measure X}
  (E : SubdiffusiveProcess.DirichletForm.ClosedForm m) (c : ℝ) {u : ↥(MeasureTheory.Lp ℝ 2 m)},
  u ∈ E.domain → E.form (c • u) (c • u) = c ^ 2 * E.form u u
end ClosedForm

variable [TopologicalSpace X]
end SubdiffusiveProcess.DirichletForm

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_b8651ad638f0fb0692e7_FOTLocalityApproximation ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
open MeasureTheory Filter Set Topology
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess.DirichletForm
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
/-- Continuous core approximations with a uniform energy bound. -/
structure CoreApproximation (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X) (u : Lp ℝ 2 m) where
  seq : ℕ → Lp ℝ 2 m
  rep : ℕ → X → ℝ
  mem_domain : ∀ n, seq n ∈ F.domain
  continuous : ∀ n, Continuous (rep n)
  compact : ∀ n, HasCompactSupport (rep n)
  support : ∀ n, tsupport (rep n) ⊆ U
  ae_rep : ∀ n, ⇑(seq n) =ᵐ[m] rep n
  tendsto : Tendsto seq atTop (𝓝 u)
  bound : ℝ
  energy_le : ∀ n, F.form (seq n) (seq n) ≤ bound
set_option linter.unusedVariables false in
theorem CoreApproximation.exists_plateau [T2Space X]
    {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} {u : Lp ℝ 2 m}
    (a : CoreApproximation F U u) {R : ℝ≥0} (haR : ∀ n x, |a.rep n x| ≤ R)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain) {f : X → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hwae : ⇑w =ᵐ[m] f) (hf01 : ∀ x, f x ∈ Icc 0 1)
    {c : ℝ} (hfu : ∀ᵐ x ∂m, (c - u x) * f x = 0) 
    (h_SubdiffusiveProcess_DirichletForm_exists_mul_mem_form_le : ∀ {X : Type u_1} [inst : MeasurableSpace X] {m : MeasureTheory.Measure X}
      (F : SubdiffusiveProcess.DirichletForm m) {u v : ↥(MeasureTheory.Lp ℝ 2 m)},
      u ∈ F.domain →
        v ∈ F.domain →
          ∀ {M : ℝ},
            (∀ᵐ (x : X) ∂m, |(↑(↑u : X →ₘ[m] ℝ) : X → ℝ) x| ≤ M) →
              (∀ᵐ (x : X) ∂m, |(↑(↑v : X →ₘ[m] ℝ) : X → ℝ) x| ≤ M) →
                ∃ w ∈ F.domain,
                  ((↑(↑w : X →ₘ[m] ℝ) : X → ℝ) =ᵐ[m] fun (x : X) ↦
                      (↑(↑u : X →ₘ[m] ℝ) : X → ℝ) x * (↑(↑v : X →ₘ[m] ℝ) : X → ℝ) x) ∧
                    F.form w w ≤ 8 * M ^ 2 * (F.form u u + F.form v v))
    :
    ∃ b : CoreApproximation F U u,
      ∀ n x, f x = 1 → b.rep n x = c := by
  have haM : ∀ n, ∀ᵐ x ∂m, |a.seq n x| ≤ (R : ℝ) + 1 := by
    intro n
    filter_upwards [a.ae_rep n] with x hx
    rw [hx]
    linarith [haR n x]
  have hwM : ∀ᵐ x ∂m, |w x| ≤ (R : ℝ) + 1 := by
    filter_upwards [hwae] with x hx
    rw [hx, abs_of_nonneg (hf01 x).1]
    linarith [(hf01 x).2, R.coe_nonneg]
  choose p hpD hpae hpE using fun n =>
    h_SubdiffusiveProcess_DirichletForm_exists_mul_mem_form_le F (a.mem_domain n) hw (haM n) hwM
  let v : ℕ → Lp ℝ 2 m := fun n => a.seq n - p n + c • w
  let g : ℕ → X → ℝ := fun n x => a.rep n x - a.rep n x * f x + c * f x
  have hvD : ∀ n, v n ∈ F.domain := fun n =>
    F.domain.add_mem (F.domain.sub_mem (a.mem_domain n) (hpD n)) (F.domain.smul_mem c hw)
  have hgae : ∀ n, ⇑(v n) =ᵐ[m] g n := by
    intro n
    filter_upwards [Lp.coeFn_add (a.seq n - p n) (c • w),
      Lp.coeFn_sub (a.seq n) (p n), Lp.coeFn_smul c w, hpae n, a.ae_rep n, hwae]
      with x h1 h2 h3 h4 h5 h6
    change (a.seq n - p n + c • w : Lp ℝ 2 m) x = _
    rw [h1, Pi.add_apply, h2, Pi.sub_apply, h3, Pi.smul_apply, smul_eq_mul, h4, h5, h6]
  have hnorm : ∀ n, ‖v n - u‖ ≤ ‖a.seq n - u‖ := by
    intro n
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (v n) u, Lp.coeFn_sub (a.seq n) u,
      hgae n, a.ae_rep n, hfu] with x h1 h2 h3 h4 heq
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, Real.norm_eq_abs, Real.norm_eq_abs]
    change |a.rep n x - a.rep n x * f x + c * f x - u x| ≤ |a.rep n x - u x|
    calc
      _ = |(a.rep n x - u x) * (1 - f x)| := by
        congr 1
        nlinarith [heq]
      _ = |a.rep n x - u x| * |1 - f x| := abs_mul _ _
      _ ≤ |a.rep n x - u x| := by
        apply mul_le_of_le_one_right (abs_nonneg _)
        exact abs_le.mpr ⟨by linarith [(hf01 x).2], by linarith [(hf01 x).1]⟩
  have hvE : ∀ n, F.form (v n) (v n) ≤
      4 * a.bound + 32 * ((R : ℝ) + 1) ^ 2 * (a.bound + F.form w w) +
        2 * c ^ 2 * F.form w w := by
    intro n
    have hp := (hpE n).trans (show _ ≤
        8 * ((R : ℝ) + 1) ^ 2 * (a.bound + F.form w w) by
      gcongr
      exact a.energy_le n)
    have h1 := F.toClosedForm.form_sub_self_le (a.mem_domain n) (hpD n)
    have h2 := F.toClosedForm.form_add_self_le
      (F.domain.sub_mem (a.mem_domain n) (hpD n)) (F.domain.smul_mem c hw)
    rw [F.toClosedForm.form_smul_self c hw] at h2
    change F.form (a.seq n - p n + c • w) (a.seq n - p n + c • w) ≤ _
    linarith [a.energy_le n]
  refine ⟨{
    seq := v
    rep := g
    mem_domain := hvD
    continuous := fun n => ((a.continuous n).sub ((a.continuous n).mul hf)).add
      (continuous_const.mul hf)
    compact := fun n => ((a.compact n).sub hfc.mul_left).add hfc.mul_left
    support := ?_
    ae_rep := hgae
    tendsto := tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg _) hnorm
        (tendsto_iff_norm_sub_tendsto_zero.mp a.tendsto))
    bound := 4 * a.bound + 32 * ((R : ℝ) + 1) ^ 2 * (a.bound + F.form w w) +
      2 * c ^ 2 * F.form w w
    energy_le := hvE
  }, ?_⟩
  · intro n
    have hs : Function.support (g n) ⊆ tsupport (a.rep n) ∪ tsupport f := by
      intro x hx
      by_contra h
      have h1 : x ∉ tsupport (a.rep n) := fun hx => h (Or.inl hx)
      have h2 : x ∉ tsupport f := fun hx => h (Or.inr hx)
      have ha0 := image_eq_zero_of_notMem_tsupport h1
      have hf0 := image_eq_zero_of_notMem_tsupport h2
      exact hx (by simp [g, ha0, hf0])
    exact (closure_minimal hs (isClosed_closure.union isClosed_closure)).trans
      (union_subset (a.support n) hfU)
  · intro n x hx
    change a.rep n x - a.rep n x * f x + c * f x = c
    rw [hx]
    ring
end SubdiffusiveProcess.DirichletForm
