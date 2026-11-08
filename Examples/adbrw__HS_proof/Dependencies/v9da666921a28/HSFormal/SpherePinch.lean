module
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
@[expose] public section
/-!
# The oriented pinch and the round target sphere (Section 7, L492–524)

The target sphere `Sⁿ` of Section 7 is the one-point compactification `OnePoint ℝⁿ` of
coordinate space.

* `HSFormal.pinch ρ`: the oriented pinch `s_ρ : ℝⁿ → Sⁿ`, `v ↦ v / (ρ - ‖v‖)` on `B(0,ρ)` and `∞`
  outside (L492). It is continuous, and a homeomorphism of `B(0,ρ)` onto `Sⁿ ∖ {∞}`
  (`HSFormal.pinchBallHomeomorph`).
* `HSFormal.pinchMap`: its extension `Sⁿ → Sⁿ` by `∞ ↦ ∞`, and `HSFormal.pinchHomotopy`, an
  explicit homotopy rel `∞` from the identity of `Sⁿ` to it (so the pinch has degree one).
* `HSFormal.roundSphere`: stereographic identification of `Sⁿ` with the unit sphere of `ℝⁿ⁺¹`;
  `HSFormal.roundDist` is the induced round (chordal) metric, for which `s_ρ(0)` and `∞` are
  antipodal at distance `2` (L519).
* `HSFormal.SphereSelfMapSurjective`: the classical non-contractibility of spheres, isolated as an
  explicit hypothesis (degree theory is not available in mathlib).
-/
noncomputable section
open Set Filter Metric Module OnePoint
open Topology
open scoped unitInterval
namespace HSFormal
section DivOrInfty
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- `a / d` in the one-point compactification, and `∞` when `d ≤ 0`. -/
def divOrInfty (d : ℝ) (a : E) : OnePoint E :=
  if 0 < d then ((d⁻¹ • a : E) : OnePoint E) else ∞
theorem divOrInfty_of_pos {d : ℝ} (hd : 0 < d) (a : E) :
    divOrInfty d a = ((d⁻¹ • a : E) : OnePoint E) := ite_eq_left hd
theorem divOrInfty_of_nonpos {d : ℝ} (hd : d ≤ 0) (a : E) : divOrInfty d a = ∞ :=
  ite_eq_right hd.not_gt
theorem divOrInfty_eq_infty_iff {d : ℝ} {a : E} : divOrInfty d a = ∞ ↔ d ≤ 0 := by
  rcases lt_or_ge 0 d with hd | hd
  · simp [divOrInfty_of_pos hd, hd.not_ge]
  · simp [divOrInfty_of_nonpos hd, hd]
end DivOrInfty
section Extension
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
end Extension
section Pinch
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The oriented pinch `s_ρ` (L492): `v ↦ v / (ρ - ‖v‖)` on `B(0,ρ)`, and `∞` outside. -/
def pinch (ρ : ℝ) (v : E) : OnePoint E := divOrInfty (ρ - ‖v‖) v
theorem pinch_eq_infty_iff {ρ : ℝ} {v : E} : pinch ρ v = ∞ ↔ ρ ≤ ‖v‖ := by
  rw [pinch, divOrInfty_eq_infty_iff, sub_nonpos]
variable [ProperSpace E]
end Pinch
section RoundSphere
/-- The north pole of the unit sphere in `ℝⁿ⁺¹`. -/
def northPole (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
theorem norm_northPole (n : ℕ) : ‖northPole n‖ = 1 := by simp [northPole]
/-- A linear identification of `ℝⁿ` with the equatorial hyperplane. -/
def hyperplaneEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] (ℝ ∙ northPole n)ᗮ :=
  haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by
    rw [Submodule.finrank_orthogonal_span_singleton (n := n) (by
      intro h; have := norm_northPole n; rw [h, norm_zero] at this; exact zero_ne_one this)]
    simp)).some
/-- The stereographic identification of `Sⁿ = OnePoint ℝⁿ` with the round unit sphere of `ℝⁿ⁺¹`;
`∞` goes to the north pole and `0` to the south pole. -/
def roundSphere (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  (hyperplaneEquiv n).toHomeomorph.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere (norm_northPole n))
def roundDist {n : ℕ} (z z' : OnePoint (EuclideanSpace ℝ (Fin n))) : ℝ :=
  dist (roundSphere n z) (roundSphere n z')
end RoundSphere
end HSFormal
