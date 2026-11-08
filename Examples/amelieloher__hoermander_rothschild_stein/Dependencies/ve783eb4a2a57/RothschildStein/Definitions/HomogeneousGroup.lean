-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.Hormander.Interface.BasisVec
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.polynomialProduct
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.coordinateDilation
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
namespace RothschildStein
structure HomogeneousGroup (N : ℕ) where
  dimension_pos : 0 < N
  weight : Fin N → ℕ
  weight_pos : ∀ j, 0 < weight j
  weight_mono : Monotone weight
  productPolynomial : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℝ
  inversePolynomial : Fin N → MvPolynomial (Fin N) ℝ
  zero_left : ∀ x, polynomialProduct productPolynomial 0 x = x
  zero_right : ∀ x, polynomialProduct productPolynomial x 0 = x
  assoc : ∀ x y z,
    polynomialProduct productPolynomial (polynomialProduct productPolynomial x y) z =
      polynomialProduct productPolynomial x (polynomialProduct productPolynomial y z)
  inverse_left : ∀ x,
    polynomialProduct productPolynomial
      (fun j => MvPolynomial.eval x (inversePolynomial j)) x = 0
  inverse_right : ∀ x,
    polynomialProduct productPolynomial x
      (fun j => MvPolynomial.eval x (inversePolynomial j)) = 0
  dilation_product : ∀ t : ℝ, 0 < t → ∀ x y,
    coordinateDilation weight t (polynomialProduct productPolynomial x y) =
      polynomialProduct productPolynomial
        (coordinateDilation weight t x) (coordinateDilation weight t y)
end RothschildStein
