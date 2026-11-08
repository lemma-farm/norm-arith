module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.VariationalResponses.LimitForm
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.ContinuousTraceResponse
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-! Finite response witnesses pass to the form defined by a limiting killed inverse.
The energy estimate here bounds the total energy; it does not assert a localized
liminf theorem or construct the finite witnesses.
-/
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace SubdiffusiveProcess
/-- A uniformly bounded response-energy sequence has a limit in the inverse-limit form domain. -/
theorem form_bound_of_response_limits
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hE : ∀ v, E.energy v = limitFormEnergy G v)
    (hresponse : ∀ f : DomainL2 Q,
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (𝓝 (inner ℝ f (G f))))
    (un : ℕ → S.space) (u : DomainL2 Q)
    (hL2 : Tendsto (fun n => (un n).val.1) atTop (𝓝 u))
    (K : ℝ) (hK : ∀ n, responseForm S (a n) (un n) (un n) ≤ K) :
    u ∈ E.domain ∧ E.form u u ≤ K := by
  have hweak : ∀ f : DomainL2 Q,
      Tendsto (fun n => inner ℝ f (un n).val.1) atTop (𝓝 (inner ℝ f u)) := by
    intro f
    exact tendsto_const_nhds.inner hL2
  have hlower := quadraticDual_le_liminf_responseForm S a G un u hweak hresponse
  have hupper : E.energy u ≤ (K : EReal) := by
    rw [hE]
    exact hlower.trans ((liminf_le_liminf
      (Eventually.of_forall fun n => EReal.coe_le_coe_iff.mpr (hK n))).trans_eq
        (liminf_const (K : EReal)))
  have hu := E.mem_domain_of_energy_lt_top (hupper.trans_lt (EReal.coe_lt_top K))
  refine ⟨hu, ?_⟩
  rw [E.energy_of_mem hu] at hupper
  exact EReal.coe_le_coe_iff.mp hupper
end SubdiffusiveProcess
