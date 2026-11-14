module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v26ebc2ab7993.SubdiffusiveProcess.ResponseMoments.Forms ====
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
def diffGam (c : ℝ) (E F : LocalEnergy V X) (u v : V) (s : Set X) : ℝ :=
  F.gam u v s - c * E.gam u v s
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

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_bb7e9b79bb13696cea9a_DiffCauchySchwarz ====
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
set_option linter.unusedVariables false in
theorem diff_measure_cauchy_schwarz (E F : LocalEnergy V X) (m M c : ℝ)
    (hmc : m ≤ c) (hcM : c ≤ M)
    (hlower : ∀ (w : V) (s : Set X), MeasurableSet s → m * E.gam w w s ≤ F.gam w w s)
    (hupper : ∀ (w : V) (s : Set X), MeasurableSet s → F.gam w w s ≤ M * E.gam w w s)
    (u v : V) (s : Set X) (hs : MeasurableSet s) 
    (h_SubdiffusiveProcess_ResponseMoments_abs_bilin_le_sqrt : ∀ {V : Type u_1} [inst : AddCommGroup V] [inst_1 : Module ℝ V] {B : V → V → ℝ},
      (∀ (u v : V), B u v = B v u) →
        (∀ (u v w : V), B (u + v) w = B u w + B v w) →
          (∀ (c : ℝ) (u v : V), B (c • u) v = c * B u v) →
            (∀ (u : V), 0 ≤ B u u) → ∀ (u v : V), |B u v| ≤ √(B u u * B v v))
    (h_SubdiffusiveProcess_ResponseMoments_sqrt_mul_add_sqrt_mul_le : ∀ {a b c e : ℝ}, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ e → √(a * c) + √(b * e) ≤ √((a + b) * (c + e)))
    :
    |_root_.SubdiffusiveProcess.ResponseMoments.LocalEnergy.diffGam c E F u v s| ≤
      (M - m) * Real.sqrt (E.gam u u s * E.gam v v s) := by
  classical
  set Del : ℝ := M - m with hDel
  set P : V → V → ℝ := fun w w' =>
    Del * E.gam w w' s + (F.gam w w' s - c * E.gam w w' s) with hP
  set N : V → V → ℝ := fun w w' =>
    Del * E.gam w w' s - (F.gam w w' s - c * E.gam w w' s) with hN
  have hEnn : ∀ w : V, 0 ≤ E.gam w w s := fun w => E.gam_nonneg w s
  have hPsymm : ∀ a b, P a b = P b a := by
    intro a b; simp only [hP, E.gam_symm a b s, F.gam_symm a b s]
  have hNsymm : ∀ a b, N a b = N b a := by
    intro a b; simp only [hN, E.gam_symm a b s, F.gam_symm a b s]
  have hPadd : ∀ a b w, P (a + b) w = P a w + P b w := by
    intro a b w; simp only [hP, E.gam_add_left, F.gam_add_left]; ring
  have hNadd : ∀ a b w, N (a + b) w = N a w + N b w := by
    intro a b w; simp only [hN, E.gam_add_left, F.gam_add_left]; ring
  have hPsmul : ∀ (r : ℝ) a b, P (r • a) b = r * P a b := by
    intro r a b; simp only [hP, E.gam_smul_left, F.gam_smul_left]; ring
  have hNsmul : ∀ (r : ℝ) a b, N (r • a) b = r * N a b := by
    intro r a b; simp only [hN, E.gam_smul_left, F.gam_smul_left]; ring
  have hPnn : ∀ w : V, 0 ≤ P w w := by
    intro w
    have h1 := hlower w s hs
    have h2 := hEnn w
    simp only [hP, hDel]
    nlinarith
  have hNnn : ∀ w : V, 0 ≤ N w w := by
    intro w
    have h1 := hupper w s hs
    have h2 := hEnn w
    simp only [hN, hDel]
    nlinarith
  have hPle : ∀ w : V, P w w ≤ 2 * Del * E.gam w w s := by
    intro w
    have h1 := hupper w s hs
    have h2 := hEnn w
    simp only [hP, hDel]
    nlinarith
  have hNle : ∀ w : V, N w w ≤ 2 * Del * E.gam w w s := by
    intro w
    have h1 := hlower w s hs
    have h2 := hEnn w
    simp only [hN, hDel]
    nlinarith
  have hPcs := h_SubdiffusiveProcess_ResponseMoments_abs_bilin_le_sqrt hPsymm hPadd hPsmul hPnn u v
  have hNcs := h_SubdiffusiveProcess_ResponseMoments_abs_bilin_le_sqrt hNsymm hNadd hNsmul hNnn u v
  have hd : 0 ≤ Del := by simp only [hDel]; linarith
  have hPNu : P u u + N u u = 2 * Del * E.gam u u s := by simp only [hP, hN]; ring
  have hPNv : P v v + N v v = 2 * Del * E.gam v v s := by simp only [hP, hN]; ring
  have hcs2 := h_SubdiffusiveProcess_ResponseMoments_sqrt_mul_add_sqrt_mul_le (hPnn u) (hNnn u) (hPnn v) (hNnn v)
  rw [hPNu, hPNv] at hcs2
  have hkey : Real.sqrt ((2 * Del * E.gam u u s) * (2 * Del * E.gam v v s)) =
      2 * Del * Real.sqrt (E.gam u u s * E.gam v v s) := by
    have hrw : (2 * Del * E.gam u u s) * (2 * Del * E.gam v v s) =
        (2 * Del) ^ 2 * (E.gam u u s * E.gam v v s) := by ring
    rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hkey] at hcs2
  have hsum : |P u v| + |N u v| ≤
      2 * Del * Real.sqrt (E.gam u u s * E.gam v v s) := by
    linarith [hPcs, hNcs, hcs2]
  have hDeq : _root_.SubdiffusiveProcess.ResponseMoments.LocalEnergy.diffGam c E F u v s = (P u v - N u v) / 2 := by
    simp only [hP, hN, _root_.SubdiffusiveProcess.ResponseMoments.LocalEnergy.diffGam]
    ring
  have habs : |P u v - N u v| ≤ |P u v| + |N u v| := by
    rcases abs_cases (P u v - N u v) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] <;> [skip; skip] <;>
      · rcases abs_cases (P u v) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          rcases abs_cases (N u v) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
          rw [h1, h2] <;> linarith
  rw [hDeq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hDel' : Del = M - m := hDel
  nlinarith [habs, hsum, Real.sqrt_nonneg (E.gam u u s * E.gam v v s)]
end ResponseMoments
end SubdiffusiveProcess
