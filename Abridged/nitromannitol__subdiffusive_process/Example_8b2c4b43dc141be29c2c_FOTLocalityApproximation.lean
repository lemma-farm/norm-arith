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

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v07d0a733674e.SubdiffusiveProcess.DirichletForm.Basic ====
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

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_8b2c4b43dc141be29c2c_FOTLocalityApproximation ====
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
theorem CoreApproximation.exists_supported [T2Space X]
    {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X} {u : Lp ℝ 2 m}
    (a : CoreApproximation F U u) {R : ℝ≥0} (haR : ∀ n x, |a.rep n x| ≤ R)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain) {f : X → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hwae : ⇑w =ᵐ[m] f) (hf01 : ∀ x, f x ∈ Icc 0 1)
    (hfu : ∀ᵐ x ∂m, u x * f x = u x) 
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
    ∃ b : CoreApproximation F U u, ∀ n, tsupport (b.rep n) ⊆ tsupport f := by
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
  have hprep : ∀ n, ⇑(p n) =ᵐ[m] (fun x => a.rep n x * f x) := by
    intro n
    filter_upwards [hpae n, a.ae_rep n, hwae] with x hx hy hz
    rw [hx, hy, hz]
  have hnorm : ∀ n, ‖p n - u‖ ≤ ‖a.seq n - u‖ := by
    intro n
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (p n) u, Lp.coeFn_sub (a.seq n) u, hpae n, hwae, hfu]
      with x hx hy hz hfξ heq
    rw [hx, hy, Pi.sub_apply, Pi.sub_apply, hz, hfξ, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      |a.seq n x * f x - u x| = |(a.seq n x - u x) * f x| := by
        congr 1
        rw [sub_mul, heq]
      _ = |a.seq n x - u x| * |f x| := abs_mul _ _
      _ ≤ |a.seq n x - u x| := by
        apply mul_le_of_le_one_right (abs_nonneg _)
        rw [abs_of_nonneg (hf01 x).1]
        exact (hf01 x).2
  refine ⟨{
    seq := p
    rep := fun n x => a.rep n x * f x
    mem_domain := hpD
    continuous := fun n => (a.continuous n).mul hf
    compact := fun n => hfc.mul_left
    support := fun n => tsupport_mul_subset_right.trans hfU
    ae_rep := hprep
    tendsto := tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg _) hnorm
        (tendsto_iff_norm_sub_tendsto_zero.mp a.tendsto))
    bound := 8 * ((R : ℝ) + 1) ^ 2 * (a.bound + F.form w w)
    energy_le := fun n => (hpE n).trans (by gcongr; exact a.energy_le n)
  }, fun n => tsupport_mul_subset_right⟩
end SubdiffusiveProcess.DirichletForm
