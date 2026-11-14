module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v6409549b3905.SubdiffusiveProcess.ResponseMoments.Forms ====
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
# Carriers for the comparison of two candidate energies

Subsection `mfd:sec-compare` 
 argues with two candidate local energies `E`, `F` through
their energy measures `Γ_E(u,v)`, `Γ_F(u,v)`.  This file introduces the two
carriers that the statements of that subsection need and nothing more.

* `SubdiffusiveProcess.ResponseMoments.LocalEnergy V X` is a symmetric bilinear energy *measure*
  `gam u v s` on a real vector space `V` of admissible functions, with values
  in `ℝ`, monotone and nonnegative on the diagonal.  Its form is
  `form u v = gam u v Set.univ`.  Strong locality, closedness and the
  Dirichlet property are *not* assumed: only the algebra used in
  `mfd:lem-diff`, `lem_common`, `mfd:lem-relvar`, `mfd:prop-conc` and
  `mfd:thm-prop`.
* `SubdiffusiveProcess.ResponseMoments.DomainedEnergy H X` adds the domain `dom : Submodule ℝ H`, which the
  two statements that compare unequal domains (`mfd:prop-density`,
  `mfd:thm-C0`) need.

Nothing in this file asserts a conclusion of the paper.
-/
open MeasureTheory Set
noncomputable section
namespace SubdiffusiveProcess
namespace ResponseMoments
/-- A candidate local energy, given through its energy measure.
`gam u v s = Γ_E(u,v)(s)`; the form is `gam u v Set.univ`. -/
structure LocalEnergy (V : Type*) [AddCommGroup V] [Module ℝ V]
    (X : Type*) [MeasurableSpace X] where
  /-- The energy measure `Γ(u,v)(s)`. -/
  gam : V → V → Set X → ℝ
  gam_symm : ∀ u v s, gam u v s = gam v u s
  gam_add_left : ∀ u v w s, gam (u + v) w s = gam u w s + gam v w s
  gam_smul_left : ∀ (c : ℝ) (u v : V) (s : Set X), gam (c • u) v s = c * gam u v s
  gam_nonneg : ∀ (u : V) (s : Set X), 0 ≤ gam u u s
  gam_mono : ∀ (u : V) (s t : Set X), s ⊆ t → gam u u s ≤ gam u u t
  /-- Finite additivity of the energy measure on disjoint measurable sets. -/
  gam_add_disjoint : ∀ (u v : V) (s t : Set X), MeasurableSet s → MeasurableSet t → Disjoint s t → gam u v (s ∪ t) = gam u v s + gam u v t
namespace LocalEnergy
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {X : Type*} [MeasurableSpace X]
/-- The energy form `E(u,v) = Γ_E(u,v)(X)`. -/
def form (E : LocalEnergy V X) (u v : V) : ℝ := E.gam u v Set.univ
set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.ResponseMoments.LocalEnergy.form_nonneg.{w_u_1,w_u_2} : ∀ {V : Type w_u_1} [inst : AddCommGroup V] [inst_1 : Module ℝ V] {X : Type w_u_2}
  [inst_2 : MeasurableSpace X] (E : SubdiffusiveProcess.ResponseMoments.LocalEnergy V X) (u : V),
  0 ≤ E.form u u
end LocalEnergy

namespace DomainedEnergy
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {X : Type*} [MeasurableSpace X]
end DomainedEnergy
end ResponseMoments
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_c985c76339aee002126a_DiffCauchySchwarz ====
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
# The relative form of two candidate energies, Lemma `mfd:lem-diff`

`mfd:lem-diff`: with
`m Γ_E ≤ Γ_F ≤ M Γ_E` and `c ∈ [m, M]`, the relative measure
`Γ_D = Γ_F - c Γ_E` satisfies
`|Γ_D(u,v)|(B) ≤ Δ √(Γ_E(u)(B) Γ_E(v)(B))` with `Δ = M - m`.
The proof is matrix Cauchy--Schwarz applied to the two nonnegative
combinations `Δ Γ_E ± Γ_D`, exactly as in paper label `mfd:lem-diff`.
-/
open Real
noncomputable section
namespace SubdiffusiveProcess
namespace ResponseMoments
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {X : Type*} [MeasurableSpace X]
theorem minimizer_difference_energy_le (E F : LocalEnergy V X) (m M c : ℝ)
    (hm : 0 < m) (_hmc : m ≤ c) (_hcM : c ≤ M) (uE w : V)
    (hcoercive : m * E.form w w ≤ F.form w w)
    (heuler : F.form w w = -(F.form uE w - c * E.form uE w))
    (hCS : |F.form uE w - c * E.form uE w| ≤
      (M - m) * Real.sqrt (E.form uE uE * E.form w w)) :
    E.form w w ≤ ((M - m) / m) ^ 2 * E.form uE uE := by
  have hEu : 0 ≤ E.form uE uE := E.form_nonneg uE
  have hEw : 0 ≤ E.form w w := E.form_nonneg w
  have hsplit : Real.sqrt (E.form uE uE * E.form w w) =
      Real.sqrt (E.form uE uE) * Real.sqrt (E.form w w) := Real.sqrt_mul hEu _
  have hneg : -(F.form uE w - c * E.form uE w) ≤
      |F.form uE w - c * E.form uE w| := neg_le_abs _
  have hkey : m * E.form w w ≤
      (M - m) * (Real.sqrt (E.form uE uE) * Real.sqrt (E.form w w)) := by
    rw [← hsplit]
    calc m * E.form w w ≤ F.form w w := hcoercive
      _ = -(F.form uE w - c * E.form uE w) := heuler
      _ ≤ |F.form uE w - c * E.form uE w| := hneg
      _ ≤ (M - m) * Real.sqrt (E.form uE uE * E.form w w) := hCS
  have hy : Real.sqrt (E.form w w) ^ 2 = E.form w w := Real.sq_sqrt hEw
  have hx : Real.sqrt (E.form uE uE) ^ 2 = E.form uE uE := Real.sq_sqrt hEu
  have hynn : 0 ≤ Real.sqrt (E.form w w) := Real.sqrt_nonneg _
  have hxnn : 0 ≤ Real.sqrt (E.form uE uE) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hynn with hy0 | hy0
  · have : E.form w w = 0 := by rw [← hy, ← hy0]; ring
    rw [this]
    positivity
  · have hstep : m * Real.sqrt (E.form w w) ≤ (M - m) * Real.sqrt (E.form uE uE) := by
      have := hkey
      rw [← hy] at this
      nlinarith [this, hy0]
    have hdiv : Real.sqrt (E.form w w) ≤ (M - m) / m * Real.sqrt (E.form uE uE) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm]
      nlinarith [hstep]
    have hsq := mul_self_le_mul_self hynn hdiv
    rw [← hy, ← hx]
    nlinarith [hsq, hxnn]
end ResponseMoments
end SubdiffusiveProcess
