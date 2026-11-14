module

public import Mathlib

-- ==== Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.vbae92a91c2fb.RequestProject.FlowBasic ====
public section
/-!
# Global flows of bounded, Lipschitz, time-dependent vector fields

For a time-dependent vector field `V : ℝ → E → E` which is continuous in time, uniformly bounded
and uniformly Lipschitz in space, we construct the global flow `gflow V t₀ t x` (the value at time
`t` of the solution starting from `x` at time `t₀`) and prove its basic properties: the flow
equation, uniqueness, the cocycle law, Lipschitz bounds and closeness to the identity.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped NNReal
noncomputable section
namespace AnomDiss
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
/-- Standing assumptions on a time-dependent vector field: continuity in time, a uniform bound
`M` and a uniform spatial Lipschitz constant `K`. -/
structure GoodField (V : ℝ → E → E) (M K : ℝ≥0) : Prop where
  cont : ∀ x, Continuous fun t => V t x
  bound : ∀ t x, ‖V t x‖ ≤ M
  lip : ∀ t, LipschitzWith K (V t)
namespace GoodField
variable {V : ℝ → E → E} {M K : ℝ≥0}

end GoodField
open Classical in
/-- The global flow: `gflow V t₀ t x` is the value at time `t` of the solution of `ẏ = V(t, y)`
with `y(t₀) = x` (and `x` itself if no global solution exists). -/
def gflow (V : ℝ → E → E) (t₀ t : ℝ) (x : E) : E :=
  if h : ∃ α : ℝ → E, α t₀ = x ∧ ∀ s, HasDerivAt α (V s (α s)) s then h.choose t else x
namespace GoodField
variable {V : ℝ → E → E} {M K : ℝ≥0}

set_option linter.unusedVariables false in
axiom _root_.AnomDiss.GoodField.gflow_self.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [CompleteSpace E]
  {V : ℝ → E → E} {M K : NNReal},
  AnomDiss.GoodField V M K → ∀ (t₀ : ℝ) (x : E), AnomDiss.gflow V t₀ t₀ x = x
set_option linter.unusedVariables false in
axiom _root_.AnomDiss.GoodField.hasDerivAt_gflow.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [CompleteSpace E]
  {V : ℝ → E → E} {M K : NNReal},
  AnomDiss.GoodField V M K →
    ∀ (t₀ t : ℝ) (x : E),
      HasDerivAt (fun (s : ℝ) ↦ AnomDiss.gflow V t₀ s x) (V t (AnomDiss.gflow V t₀ t x)) t

set_option linter.unusedVariables false in
axiom _root_.AnomDiss.GoodField.norm_gflow_sub_le.{w_u_1} : ∀ {E : Type w_u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [CompleteSpace E]
  {V : ℝ → E → E} {M K : NNReal},
  AnomDiss.GoodField V M K →
    ∀ (t₀ t : ℝ) (x : E), ‖AnomDiss.gflow V t₀ t x - x‖ ≤ (↑M : ℝ) * |t - t₀|

end GoodField
end AnomDiss

end
end
end

-- ==== Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Examples.Example_b09b44cbf12400a4d6ee_FlowTime ====
/-!
# Dependence of flow maps on the initial time

For a field which is Lipschitz in time, `Φ_{r → s}(z) = z + (s - r) V(s, z) + O((s - r)²)`
uniformly in `z`.  Consequently, along a differentiable curve `y`, the map
`r ↦ Φ_{r → s}(y r)` has derivative `y'(s) - V(s, y(s))` at `r = s`, and for the backward maps
`Y_r = Φ_{r → t₀}` the chain rule gives the transport equation `∂ᵣ (g ∘ Y_r) = -V · ∇(g ∘ Y_r)`.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real Asymptotics
open scoped NNReal
noncomputable section
namespace AnomDiss
namespace GoodField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {V : ℝ → E → E} {M K : ℝ≥0}
/-- Second-order expansion of a flow map in the initial time, uniformly in space. -/
lemma norm_gflow_sub_sub_smul_le (hV : GoodField V M K) {Lt : ℝ}
    (hLt : ∀ s s' x, ‖V s x - V s' x‖ ≤ Lt * |s - s'|) (r s : ℝ) (z : E) :
    ‖gflow V r s z - z - (s - r) • V s z‖ ≤ (Lt + K * M) * (s - r) ^ 2 := by
  have hLt0 : 0 ≤ Lt := by
    have := hLt (r + 1) r z
    have h0 : (0:ℝ) ≤ Lt * |r + 1 - r| := (norm_nonneg _).trans this
    simpa using h0
  set H : ℝ → E := fun u => gflow V r u z - z - (u - r) • V s z with hH
  have hd : ∀ u, HasDerivAt H (V u (gflow V r u z) - V s z) u := by
    intro u
    have h1 := ((hasDerivAt_id u).sub_const r).smul_const (V s z)
    have := ((hV.hasDerivAt_gflow r u z).sub_const z).fun_sub h1
    simpa using this
  have hbd : ∀ u ∈ uIcc r s, ‖V u (gflow V r u z) - V s z‖ ≤ (Lt + K * M) * |s - r| := by
    intro u hu
    have hu1 : |u - s| ≤ |s - r| := by
      rcases le_total r s with h | h
      · rw [uIcc_of_le h] at hu
        rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonneg (by linarith)]; linarith [hu.1]
      · rw [uIcc_of_ge h] at hu
        rw [abs_of_nonneg (by linarith [hu.1]), abs_of_nonpos (by linarith)]; linarith [hu.2]
    have hu2 : |u - r| ≤ |s - r| := by
      rcases le_total r s with h | h
      · rw [uIcc_of_le h] at hu
        rw [abs_of_nonneg (by linarith [hu.1]), abs_of_nonneg (by linarith)]; linarith [hu.2]
      · rw [uIcc_of_ge h] at hu
        rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith)]; linarith [hu.1]
    have e1 := hLt u s (gflow V r u z)
    have e2 := (hV.lip s).dist_le_mul (gflow V r u z) z
    have e3 := hV.norm_gflow_sub_le r u z
    rw [dist_eq_norm, dist_eq_norm] at e2
    calc ‖V u (gflow V r u z) - V s z‖
        = ‖(V u (gflow V r u z) - V s (gflow V r u z)) + (V s (gflow V r u z) - V s z)‖ := by
          congr 1; abel
      _ ≤ Lt * |u - s| + K * (M * |u - r|) := by
          refine (norm_add_le _ _).trans (add_le_add e1 (e2.trans ?_))
          gcongr
      _ ≤ Lt * |s - r| + K * (M * |s - r|) := by gcongr
      _ = (Lt + K * M) * |s - r| := by ring
  have key := (convex_uIcc r s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hd u).hasDerivWithinAt) hbd left_mem_uIcc right_mem_uIcc
  have eH : H s - H r = gflow V r s z - z - (s - r) • V s z := by
    simp only [hH, hV.gflow_self, sub_self, zero_smul, sub_zero]
  rw [eH, Real.norm_eq_abs] at key
  calc _ ≤ (Lt + K * M) * |s - r| * |s - r| := key
    _ = _ := by rw [mul_assoc, ← sq, sq_abs]
end GoodField
end AnomDiss
