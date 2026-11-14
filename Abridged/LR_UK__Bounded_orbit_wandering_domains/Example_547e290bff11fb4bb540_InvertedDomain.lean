module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Tactic

-- ==== Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.vdb8cca1e266e.FunctionTheory.Conformal.ExteriorCoordinate ====
public section
@[expose] public section
open Set Metric Complex Bornology
open scoped Topology
namespace FunctionTheory
/-- The spherical exterior in the coordinate `z ↦ 1/z`. Zero represents
infinity, so it is explicitly included. The pole belongs to the removed set. -/
def invertedExterior (K : Set ℂ) : Set ℂ := {w | w = 0 ∨ w⁻¹ ∉ K}
end FunctionTheory

end
end

-- ==== Examples.LR_UK__Bounded_orbit_wandering_domains.Examples.Example_547e290bff11fb4bb540_InvertedDomain ====
@[expose] public section
open Set Metric Complex Filter Bornology
open scoped Topology
namespace FunctionTheory


set_option linter.unusedVariables false in
/-- A neighbourhood of the image of infinity becomes the exterior of a
compact set when the reciprocal coordinate is undone. -/
theorem isCompact_invertedExterior_of_isOpen {V : Set ℂ}
    (hV : IsOpen V) (h0 : (0 : ℂ) ∈ V) 
    (h_FunctionTheory_isClosed_invertedExterior_of_isOpen : ∀ {V : Set ℂ}, IsOpen V → IsClosed (FunctionTheory.invertedExterior V))
    : IsCompact (invertedExterior V) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  apply (isCompact_iff_isClosed_bounded).mpr
  refine ⟨h_FunctionTheory_isClosed_invertedExterior_of_isOpen hV, ?_⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨ε⁻¹, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · simp [hz0, le_of_lt (inv_pos.mpr hε)]
  · by_contra! hlarge
    have hinv : ‖z⁻¹‖ < ε := by
      rw [norm_inv]
      simpa only [inv_inv] using (inv_lt_inv₀ (norm_pos_iff.mpr hz0) (inv_pos.mpr hε)).mpr hlarge
    exact (hz.resolve_left hz0) (hball (by simpa using hinv))

end FunctionTheory
