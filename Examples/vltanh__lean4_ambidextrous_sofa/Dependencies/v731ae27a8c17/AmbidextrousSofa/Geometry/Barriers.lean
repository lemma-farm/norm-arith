module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Geometry.Hallway
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Whole-angle niches and the actual terminal wall

The definitions retain both attached inner rays and their full open angular
interval. The terminal first wall is included separately. At a full quarter
turn it is nonpositive for a cap in the unit strip and is therefore redundant.
No analogous omission is made at a proper terminal angle.
-/
noncomputable section
namespace AmbidextrousSofa
def firstWall (K : Set Plane) (θ x : ℝ) : ℝ :=
  (support K (unitNormal θ) - 1 - x * Real.cos θ) / Real.sin θ
def secondWall (K : Set Plane) (θ x : ℝ) : ℝ :=
  (support K (companionNormal θ) - 1 + x * Real.sin θ) / Real.cos θ
def cornerWall (K : Set Plane) (θ x : ℝ) : ℝ := min (firstWall K θ x) (secondWall K θ x)
/-- All visited interior angles, rather than a sampled or contact-only family. -/
def sweptWallValues (K : Set Plane) (α x : ℝ) : Set ℝ :=
  (fun θ => cornerWall K θ x) '' Set.Ioo 0 α
def sweptNiche (K : Set Plane) (α x : ℝ) : ℝ := max (sSup (sweptWallValues K α x)) 0
/-- The true partial barrier includes the entire outgoing first wall. -/
def partialBarrier (K : Set Plane) (α x : ℝ) : ℝ :=
  max (sweptNiche K α x) (firstWall K α x)
end AmbidextrousSofa
