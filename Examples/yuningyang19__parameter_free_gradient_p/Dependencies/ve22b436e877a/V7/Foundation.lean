import Examples.yuningyang19__parameter_free_gradient_p.Dependencies.ve22b436e877a.O3.Foundation
/-!
# V7 statement-layer foundations

This module contains transparent data carriers only.  It deliberately does
not import any historical O3 result or concrete O3 dispatcher.
-/
namespace V7
abbrev Point := O3.Point
abbrev PairOracle := O3.PairOracle
abbrev Observation := O3.Observation
abbrev pairing {d : ℕ} (x y : Point d) : ℝ := O3.pairing x y
noncomputable abbrev lpNorm (p : ℝ) {d : ℕ} (x : Point d) : ℝ := O3.lpNorm p x
noncomputable abbrev conjugateExponent (p : ℝ) : ℝ := O3.conjugateExponent p
/-- The primitive numerical input of the positive secant model. -/
structure MethodInput (d : ℕ) where
  p : ℝ
  eps : ℝ
  x0 : Point d
  z0 : Point d
  M0 : ℝ
/-- Chronological post-initialization result data. -/
structure PairRunResult (d : ℕ) where
  returned : Point d
  trace : List (Observation d)
end V7
