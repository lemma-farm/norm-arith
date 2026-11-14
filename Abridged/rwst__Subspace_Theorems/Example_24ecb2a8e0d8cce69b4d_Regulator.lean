module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Sum.Order
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.NumberTheory.MahlerMeasure
public import Mathlib.RingTheory.Polynomial.GaussNorm
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Order.Northcott
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.NumberTheory.NumberField.Units.Regulator

-- ==== Examples.rwst__Subspace_Theorems.Examples.Example_24ecb2a8e0d8cce69b4d_Regulator ====
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# The regulator and the heights of a fundamental system

Let `K` be a number field of degree `d = [K : ℚ]` and unit rank `r`, and write `h` for the
absolute logarithmic height. This file compares the regulator of `K` with the heights of a
fundamental system of units, in both directions:

```text
regulator K ≤ (2 d) ^ r * ∏ i, h (ε i)                for every fundamental system ε,
∏ i, h (ε i) ≤ (r !) ^ 2 / (2 ^ (r - 1) * d ^ r) * R  for some fundamental system ε.
```

The first is **Hadamard's inequality**. The regulator is the absolute determinant of the `r × r`
matrix of the logarithmic embeddings of the system (Mathlib's
`NumberField.Units.regOfFamily_eq_det'`); each row of that matrix has ℓ¹ norm at most
`2 d h (ε i)` by Layer 6.1; and the determinant of a square matrix is at most the product of the
ℓ¹ norms of its rows, which is Layer 3.4 in the square form `Matrix.abs_det_le_prod_sum_abs`.

The second is **Bugeaud–Győry's Lemma 1** in the case `S = S∞`, and it is where both halves of
Layer 4 are spent. Minkowski's second theorem (4.2) for `NumberField.Units.unitLattice K`, whose
covolume is the regulator, against the closed ℓ¹ unit ball of the log space, whose volume is
`2 ^ r / r !`, gives `∏ i, λ i ≤ r ! * R`; the basis of Layer 4.6 realizes the `i`-th minimum up
to `max 1 ((i + 1) / 2)` and so costs `r ! / 2 ^ (r - 1)`; and Layer 6.1 turns the ℓ¹ norm of a
lattice vector back into a height, which costs `d ^ (-r)`.

## Main results

* `NumberField.Units.regulator_le_prod_absLogHeight₁`: **Hadamard's bound**, for Mathlib's
  `fundSystem`; `NumberField.Units.regOfFamily_le_prod_absLogHeight₁` is the same bound for an
  arbitrary family and its own regulator, and
  `NumberField.Units.regulator_le_prod_absLogHeight₁_of_closure_sup_torsion_eq_top` for an
  arbitrary fundamental system. `NumberField.Units.regulator_le_prod_logHeight₁` is the relative
  form, where the constant is `2 ^ r`.
* `NumberField.Units.exists_fundSystem_prod_absLogHeight₁_le`: **a fundamental system of small
  height exists**, with the explicit constant `(r !) ^ 2 / (2 ^ (r - 1) d ^ r)`, and
  `NumberField.Units.exists_fundSystem_regulator_le_and_prod_absLogHeight₁_le` says that one and
  the same system satisfies both bounds.
* `NumberField.Units.logBall`: the closed ℓ¹ unit ball of the log space, with
  `NumberField.Units.volume_logBall` its volume `2 ^ r / r !` and
  `NumberField.Units.prod_successiveMinimum_logBall_le` Minkowski's second theorem against it.
* `NumberField.Units.closure_sup_torsion_eq_top_of_span`: a family of units whose logarithmic
  embeddings span the unit lattice over `ℤ` is a fundamental system, and
  `NumberField.Units.regOfFamily_eq_regulator_of_closure_sup_torsion_eq_top`: a fundamental system
  has the regulator of the field for its own regulator.
* `NumberField.Units.prod_absLogHeight₁_pos_of_closure_sup_torsion_eq_top`: no member of a
  fundamental system is a root of unity, so both bounds are bounds between positive numbers.
* `NumberField.Units.regulator_eq_one_of_rank_eq_zero`: at unit rank zero the two bounds meet and
  the regulator is `1`.

## Implementation notes

⚠ **The second statement is an existence statement and cannot be made for `fundSystem`, or for
every fundamental system.** A unimodular change of basis multiplies the heights without touching
the regulator, so no bound in the direction `∏ h (ε i) ≤ c R` can hold uniformly. The family
produced here is built from the successive minima and has nothing to do with Mathlib's
`fundSystem`. What makes it a *fundamental system* rather than merely a family of maximal rank is
that the basis of Layer 4.6 is a basis of the whole unit lattice;
`closure_sup_torsion_eq_top_of_span` is the step that turns that into
`Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤`, through the kernel of `logEmbedding`. Nor is it
a statement with unspecified constants: for a fixed `K`,
`∃ c₁ c₂ > 0, c₁ R ≤ ∏ h (ε i) ≤ c₂ R` is true of any positive numbers and says nothing.

⚠ **Hadamard's inequality is used in the ℓ¹ form, not the familiar ℓ² one.** Layer 3.4 bounds the
Gram determinant `det (A Aᵀ)` by the product of the squared ℓ² norms of the rows, and extracting a
square root of that would need `Real.sqrt`. What Layer 6.1 hands over is the **ℓ¹** norm of a row,
so the ℓ² route would pay a factor `√r` per row and then have to give it back. The square form
added to Layer 3.4 for this layer, `Matrix.abs_det_le_prod_sum_abs`, stays inside the ordered field
and needs no analysis. ⚠ The `2 d` and not `d` in the constant is Layer 6.1's factor `2` — the
price of the coordinate that `logEmbedding` drops — and not a loss in Hadamard's inequality.

⚠ **Unit rank zero is not a degenerate case to be discarded; it is where the two bounds meet.**
Mathlib's `MeasureTheory.volume_sum_rpow_le` wants a nonempty index, so `volume_logBall` does
`r = 0` by hand: the log space is a single point, the ball is all of it, and its volume is
`1 = 2 ^ 0 / 0 !`. Both bounds then read `R ≤ 1` and `1 ≤ R`, and `regulator_eq_one_of_rank_eq_zero`
falls out — a value Mathlib does not record, having only `NumberField.Units.regulator_pos`. The
truncated subtraction in `2 ^ (r - 1)` is what the constant wants: it is `1` at `r = 0` and at
`r = 1`, and `∏_{i < r} max 1 ((i + 1) / 2) = r ! / 2 ^ (r - 1)` on the nose.

⚠ **That the bounds are not vacuous comes from two different places.** Layer 6.2 puts every member
of Mathlib's `fundSystem` strictly above height one, because its logarithmic embedding is a basis
vector of the unit lattice. For an *arbitrary* fundamental system that argument is not available,
and the positivity instead comes from this layer: such a family has maximal rank, because its
regulator is the regulator of `K` and that is nonzero, and a linearly independent family has no
zero member. The acceptance criteria also check that the two constants are mutually consistent,
`1 ≤ (2 d) ^ r * (r !) ^ 2 / (2 ^ (r - 1) d ^ r)`, which the two bounds and the positivity of the
regulator force.

## References

Y. Bugeaud and K. Győry, "Bounds for the solutions of unit equations", *Acta Arithmetica* **74**
(1996), 67–80; Lemma 1 of §3 (p. 71) is the second statement, for `S`-units, and its proof on
pp. 71–72 is the route taken here. Their `h` is the multiplicative absolute height, so their
`log h` is the `absLogHeight₁` of this file.

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter V,
Lemma 8 (p. 135), which is Layer 4.6, and Chapter VIII, Theorem V, which is Layer 4.2.

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.5, where the comparison between the height of a unit and its logarithmic embedding is
Proposition 1.5.12.

This is Layer 6.3 of the `ArithmeticHeights` roadmap.
-/
public section
open Height Module NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem Real
open scoped Pointwise
namespace NumberField.Units
variable {K : Type*} [Field K] [NumberField K]
/-!
### The ℓ¹ unit ball of the log space
-/
open scoped Classical in
/-- The closed ℓ¹ unit ball of `NumberField.Units.dirichletUnitTheorem.logSpace K`, the convex
body Minkowski's second theorem is applied to. -/
def logBall (K : Type*) [Field K] [NumberField K] : Set (logSpace K) :=
  {x | ∑ w, |x w| ≤ 1}

open scoped Classical in
set_option linter.unusedVariables false in
theorem interior_logBall_nonempty 
    (h_NumberField_Units_mem_logBall : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
      {x : NumberField.Units.dirichletUnitTheorem.logSpace K},
      x ∈ NumberField.Units.logBall K ↔
        ∑ w : { w : NumberField.InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀ },
            |x w| ≤
          1)
    : (interior (logBall K)).Nonempty := by
  classical
  set n := Fintype.card {w : InfinitePlace K // w ≠ w₀} with hn
  have hsub : Metric.ball (0 : logSpace K) (1 / (n + 1)) ⊆ logBall K := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [h_NumberField_Units_mem_logBall]
    have hle : ∑ w, |x w| ≤ n * ‖x‖ := by
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset {w : InfinitePlace K // w ≠ w₀})
        (fun w ↦ |x w|) ‖x‖ fun w _ ↦ by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm x w
      rwa [Finset.card_univ, ← hn, nsmul_eq_mul] at this
    have hpos : (0 : ℝ) < n + 1 := by positivity
    have : (n : ℝ) * ‖x‖ ≤ n * (1 / (n + 1)) := by
      exact mul_le_mul_of_nonneg_left hx.le (Nat.cast_nonneg n)
    have hfin : (n : ℝ) * (1 / (n + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one hpos]
      linarith
    linarith
  exact ⟨0, mem_interior.2 ⟨_, hsub, Metric.isOpen_ball, Metric.mem_ball_self (by positivity)⟩⟩

/-!
### The constant of Layer 4.6
-/

/-!
### Fundamental systems
-/

section Examples
end Examples
end NumberField.Units
end
