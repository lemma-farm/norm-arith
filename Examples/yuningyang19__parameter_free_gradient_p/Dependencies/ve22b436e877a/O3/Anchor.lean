import Examples.yuningyang19__parameter_free_gradient_p.Dependencies.ve22b436e877a.O3.Oracle
/-!
# Secant and accepted-anchor certificates

This module proves the parts of the gradient-ray anchor that reduce directly to
finite-dimensional `ell_p/ell_q` Hölder geometry.  It deliberately does not
postulate termination or an accepted trace as data.
-/
namespace O3
structure AnchorConfig (d : ℕ) where
  q : ℝ
  x₀ : Vec d
  f₀ : ℝ
  g₀ : Vec d
  G : ℝ
  M₀ : ℝ
/-- Data returned by the first accepted probe; no correctness claim is a field. -/
structure AnchorResult (d : ℕ) where
  epoch : ℕ
  acceptedScale : ℝ
  acceptedRadius : ℝ
  acceptedPoint : Vec d
  observations : OracleTrace d
end O3
