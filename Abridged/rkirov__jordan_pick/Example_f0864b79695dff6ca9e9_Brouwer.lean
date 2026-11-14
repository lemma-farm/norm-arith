import Mathlib

-- ==== Examples.rkirov__jordan_pick.Examples.Example_f0864b79695dff6ca9e9_Brouwer ====
set_option autoImplicit false
/-!
# Toward the 2D Brouwer fixed point theorem

We build the classical topological proof of the two-dimensional Brouwer fixed
point theorem, in four phases:

* **Phase 1** — the once-around loop on `AddCircle 1` is not homotopic (rel
  endpoints) to the constant loop.  This is the mathematical heart: it is proved
  from the covering `ℝ → AddCircle 1` via unique path lifting
  (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`).
* **Phase 1.5** — transport of Phase 1 across `AddCircle 1 ≃ₜ Circle ≃ₜ
  sphere (0:ℝ²) 1` to obtain a non-nullhomotopic loop on the geometric circle.
* **Phase 2** — no retraction of the disk onto its boundary circle: a retraction
  would give a null-homotopy of the Phase 1.5 loop.
* **Phase 3** — Brouwer for the closed unit disk (`brouwer_disk`): a
  fixed-point-free self-map yields a retraction (ray construction).
* **Phase 4** — the general convex/compact/nonempty statement `brouwerFPT`.
-/
namespace JordanCurve.Brouwer
open Metric Set Function unitInterval Topology
open scoped RealInnerProductSpace
/-- The plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
/-! ## Phase 1 — the once-around loop on `AddCircle 1` is not nullhomotopic -/
section Disk
variable (f : C(closedBall (0 : Plane) 1, closedBall (0 : Plane) 1))
variable (hf : ∀ x, (f x : Plane) ≠ (x : Plane))
include hf
end Disk
section Projection
variable {s : Set Plane} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty)
/-- Nearest-point projection of `u` onto the nonempty compact convex set `s`. -/
noncomputable def projFun (u : Plane) : Plane :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose


set_option linter.unusedVariables false in
/-- The projection is nonexpansive. -/
lemma projFun_dist_le (u₁ u₂ : Plane) 
    (h_JordanCurve_Brouwer_projFun_mem : ∀ {s : Set JordanCurve.Brouwer.Plane} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty)
      (u : JordanCurve.Brouwer.Plane), JordanCurve.Brouwer.projFun hconv hcomp hne u ∈ s)
    (h_JordanCurve_Brouwer_projFun_inner_le : ∀ {s : Set JordanCurve.Brouwer.Plane} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty)
      (u : JordanCurve.Brouwer.Plane) {w : JordanCurve.Brouwer.Plane},
      w ∈ s →
        Inner.inner ℝ (u - JordanCurve.Brouwer.projFun hconv hcomp hne u)
            (w - JordanCurve.Brouwer.projFun hconv hcomp hne u) ≤
          0)
    :
    ‖projFun hconv hcomp hne u₁ - projFun hconv hcomp hne u₂‖ ≤ ‖u₁ - u₂‖ := by
  set v₁ := projFun hconv hcomp hne u₁
  set v₂ := projFun hconv hcomp hne u₂
  have hb1 : 0 ≤ ⟪u₁ - v₁, v₁ - v₂⟫ := by
    have h := h_JordanCurve_Brouwer_projFun_inner_le hconv hcomp hne u₁ (h_JordanCurve_Brouwer_projFun_mem hconv hcomp hne u₂)
    rw [show v₂ - v₁ = -(v₁ - v₂) by abel, inner_neg_right] at h
    linarith
  have hb2 : ⟪u₂ - v₂, v₁ - v₂⟫ ≤ 0 :=
    h_JordanCurve_Brouwer_projFun_inner_le hconv hcomp hne u₂ (h_JordanCurve_Brouwer_projFun_mem hconv hcomp hne u₁)
  have decomp : ⟪u₁ - u₂, v₁ - v₂⟫
      = ⟪u₁ - v₁, v₁ - v₂⟫ - ⟪u₂ - v₂, v₁ - v₂⟫ + ⟪v₁ - v₂, v₁ - v₂⟫ := by
    have hsum : u₁ - u₂ = (u₁ - v₁ - (u₂ - v₂)) + (v₁ - v₂) := by abel
    rw [← inner_sub_left, ← inner_add_left, ← hsum]
  have key : ‖v₁ - v₂‖ ^ 2 ≤ ⟪u₁ - u₂, v₁ - v₂⟫ := by
    rw [decomp, ← real_inner_self_eq_norm_sq]; linarith
  have hcs : ⟪u₁ - u₂, v₁ - v₂⟫ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := real_inner_le_norm _ _
  rcases (norm_nonneg (v₁ - v₂)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · have hsq : ‖v₁ - v₂‖ * ‖v₁ - v₂‖ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := by
      rw [← pow_two]; exact le_trans key hcs
    exact le_of_mul_le_mul_right hsq hpos
end Projection
