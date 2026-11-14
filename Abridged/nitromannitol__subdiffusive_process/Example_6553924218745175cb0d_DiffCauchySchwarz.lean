module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v5dc4108844b3.SubdiffusiveProcess.ResponseMoments.Forms ====
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

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_6553924218745175cb0d_DiffCauchySchwarz ====
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
theorem harmonic_replacement_error_le (E : LocalEnergy V X) (u pr : V)
    (f2 nrm Kp hmesh s : ℝ) (_hs : 0 < s) (hh : 0 < hmesh) (hK : 0 ≤ Kp)
    (_hf2 : 0 ≤ f2) (_hnrm : 0 ≤ nrm)
    (hload : E.form u pr = E.form pr pr)
    (hCS : E.form u pr ≤ f2 * nrm)
    (hpoin : nrm ^ 2 ≤ Kp * hmesh ^ (2 * s) * E.form pr pr) :
    E.form pr pr ≤ Kp * hmesh ^ (2 * s) * f2 ^ 2 := by
  have hA : 0 ≤ E.form pr pr := E.form_nonneg pr
  have hpow : 0 < hmesh ^ (2 * s) := Real.rpow_pos_of_pos hh _
  have h1 : E.form pr pr ≤ f2 * nrm := by rw [← hload]; exact hCS
  rcases eq_or_lt_of_le hA with hA0 | hA0
  · rw [← hA0]
    positivity
  · have h2 : E.form pr pr ^ 2 ≤ f2 ^ 2 * nrm ^ 2 := by
      have := mul_self_le_mul_self hA h1
      nlinarith [this, _hnrm, _hf2]
    nlinarith [h2, hpoin, hA0, hpow, hK, sq_nonneg f2]
end ResponseMoments
end SubdiffusiveProcess
