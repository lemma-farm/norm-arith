-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.HomogeneousGroup.mul
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.HomogeneousGroup.inv
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.Definitions.HomogeneousGroup.dilate
public import Mathlib.Topology.Algebra.MvPolynomial
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)
/-- The origin is a left identity (BB Definition 3.1, p. 94). -/
@[simp] theorem zero_mul (x : Fin N → ℝ) : G.mul 0 x = x := G.zero_left x
/-- The origin is a right identity (BB Definition 3.1, p. 94). -/
@[simp] theorem mul_zero (x : Fin N → ℝ) : G.mul x 0 = x := G.zero_right x
/-- Associativity of the polynomial law (BB Definition 3.1, p. 94). -/
theorem mul_assoc (x y z : Fin N → ℝ) : G.mul (G.mul x y) z = G.mul x (G.mul y z) :=
  G.assoc x y z
/-- The inverse is a left inverse (BB Proposition 3.7, p. 98). -/
@[simp] theorem inv_mul (x : Fin N → ℝ) : G.mul (G.inv x) x = 0 := G.inverse_left x
end RothschildStein.G2
