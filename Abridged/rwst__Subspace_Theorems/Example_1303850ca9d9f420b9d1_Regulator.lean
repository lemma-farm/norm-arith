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

-- ==== Examples.rwst__Subspace_Theorems.Dependencies.vc9097f737192.ArithmeticHeights.SuccessiveMinima ====
public section
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
# The successive minima of a symmetric convex body

For a lattice `L` in a finite-dimensional real normed space `E` and a symmetric convex body `B`,
the `i`-th successive minimum is the least dilation of `B` that contains `i + 1` linearly
independent points of `L`. This file defines it, proves it positive, monotone and homogeneous of
degree `-1` in the body, and proves Cassels' Lemma 1: the minima are attained, by one family of
independent lattice vectors realizing all of them at once.

## Main definitions

* `ZLattice.successiveMinimum`: the `i`-th successive minimum, as the infimum of the admissible
  dilations. For `i ≥ finrank ℝ E` there are none and the value is `sInf ∅ = 0`, so every
  statement below carries `i < finrank ℝ E`.

## Main results

* `gauge_le_iff_mem_smul`: the dictionary between Cassels' distance functions and the convex-body
  form pinned by the roadmap. Membership in `t • B` is having gauge at most `t`, for a **closed**
  body; `mem_smul_of_gauge_lt` is the half that needs no closedness.
* `ZLattice.successiveMinimum_pos`: the minima are positive, which is where boundedness of the
  body is used, and `ZLattice.successiveMinimum_eq_zero_of_le`: they vanish above the dimension.
* `ZLattice.successiveMinimum_le_of_le` and `ZLattice.successiveMinimum_smul`: monotone in the
  index, homogeneous of degree `-1` in the body.
* `ZLattice.exists_linearIndependent_gauge_eq_successiveMinimum`: **Cassels' Lemma 1**. There is
  one linearly independent family of lattice vectors whose gauges are the successive minima. This
  is what every later proof consumes; its body form is
  `ZLattice.exists_linearIndependent_mem_smul_successiveMinimum`, which is where closedness of
  the body is used.
* `Finset.prod_pow_le_prod_range`: the regrouping that turns a bound on the product of all `d * k`
  minima into a bound on a product of `k` `d`-th powers — what Layers 5.3 and 5.4 spend to pass
  from the minima of the lattice of a `k`-dimensional `K`-subspace to `k` heights.
* `ZLattice.successiveMinimum_zero_eq`: the zeroth minimum is the least dilation containing a
  nonzero lattice point — the quantity Minkowski's convex-body theorem bounds — and
  `ZLattice.successiveMinimum_zero_le_one` is that theorem read as the case `i = 0`.

## Implementation notes

The body is carried as four separate hypotheses — convex, symmetric, with nonempty interior,
bounded — plus closedness where it is needed, rather than as one bundled structure, so that each
statement says which of them it uses. Cassels indexes the minima by a distance function `F` and
dilates `{x | F x ≤ 1}`; the convex-body form is the pinned one, and `gauge_le_iff_mem_smul` is
the translation, proved once here.

⚠ **Attainment does not need the body to be closed; only its body form does.** The family of
`ZLattice.exists_linearIndependent_gauge_eq_successiveMinimum` realizes the minima as *gauges*
for any bounded symmetric convex body with nonempty interior, and that statement is the one the
proof produces. Turning `gauge B (v j) = λ j` into `v j ∈ λ j • B` is exactly the dictionary, and
exactly what fails for an open body: for the open unit ball no lattice vector lies in `λ 0 • B`
at all, since anything inside that dilation would already have shown a smaller dilation
admissible. The two statements are therefore kept apart, and only the second carries `IsClosed B`.

⚠ **The minima are not monotone in the index without `i < finrank ℝ E`.** Above the dimension
there is no independent family at all, the set of admissible dilations is empty, and the value is
`sInf ∅ = 0`. So `Monotone (successiveMinimum L B)` is false whenever `E` is nontrivial, and a
statement of Minkowski's second theorem that ranged over all of `ℕ` would multiply by zero.

## References

J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer (1959), Chapter VIII §1:
the definition, Lemma 1 (attainment) and the elementary properties proved here. E. Bombieri and
W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006), Appendix C.2.
Minkowski's first theorem is Mathlib's
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`.

This is Layer 4.1 of the `ArithmeticHeights` roadmap.
-/
public section
open Metric Module MeasureTheory Set
open scoped Pointwise Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E}
/-! ### The body and its gauge

Three facts about a symmetric convex body, none of them about lattices: it is a neighbourhood of
the origin, and its dilations are the sublevel sets of its gauge — from below always, and exactly
when the body is closed. -/

namespace ZLattice
variable {i : ℕ}
/-- The `i`-th **successive minimum** of a set `B` with respect to a lattice `L`: the least
dilation of `B` containing `i + 1` linearly independent points of `L`. The case `i = 0` is the
quantity bounded by Minkowski's convex-body theorem. For `i ≥ finrank ℝ E` there is no such
family and the value is `sInf ∅ = 0`, so every statement about the minima carries
`i < finrank ℝ E`. -/
noncomputable def successiveMinimum (L : Submodule ℤ E) (B : Set E) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ v : Fin (i + 1) → E,
    (∀ j, v j ∈ (t • B) ∩ (L : Set E)) ∧ LinearIndependent ℝ v}
variable {L : Submodule ℤ E}

variable [FiniteDimensional ℝ E]
section Elementary
variable [DiscreteTopology L] [IsZLattice ℝ L]

end Elementary

section Discrete
variable [DiscreteTopology L]

variable [IsZLattice ℝ L]

end Discrete
section Attainment
variable [DiscreteTopology L] [IsZLattice ℝ L]

end Attainment
/-! ### Minkowski's first theorem as the case `i = 0`

The zeroth minimum is the least dilation of the body containing a nonzero lattice point, which is
the quantity Minkowski's convex-body theorem bounds. The identity is measure-free; the bound is
the only statement in this file that mentions a measure. -/

end ZLattice
/-! ### Regrouping a product of minima -/
section Regrouping

end Regrouping
/-! ### Worked examples -/
section Examples
open ZLattice
variable [FiniteDimensional ℝ E] {L : Submodule ℤ E}
end Examples

end
end

-- ==== Examples.rwst__Subspace_Theorems.Examples.Example_1303850ca9d9f420b9d1_Regulator ====
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

/-!
### The constant of Layer 4.6
-/

/-!
### Fundamental systems
-/

open scoped Classical in
set_option linter.unusedVariables false in
/-- **A fundamental system of small height exists** (Bugeaud–Győry 1996, Lemma 1, in the case
`S = S∞`). -/
theorem exists_fundSystem_prod_absLogHeight₁_le (K : Type*) [Field K] [NumberField K] 
    (h_ZLattice_exists_basis_mem_smul_successiveMinimum : ∀ {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {B : Set E}
      [FiniteDimensional ℝ E] (L : Submodule ℤ E) [inst_3 : DiscreteTopology ↥L] [IsZLattice ℝ L],
      Convex ℝ B →
        (∀ x ∈ B, -x ∈ B) →
          (interior B).Nonempty →
            Bornology.IsBounded B →
              IsClosed B →
                ∃ (b : Module.Basis (Fin (Module.finrank ℝ E)) ℤ ↥L),
                  ∀ (i : Fin (Module.finrank ℝ E)),
                    (↑((b : Fin (Module.finrank ℝ E) → ↥L) i) : E) ∈
                      (Max.max 1 (((↑(↑i : ℕ) : ℝ) + 1) / 2) *
                          ZLattice.successiveMinimum L B (↑i : ℕ)) •
                        B)
    (h_NumberField_Units_closure_sup_torsion_eq_top_of_span : ∀ {K : Type u_2} [inst : Field K] [inst_1 : NumberField K] {m : ℕ}
      (ε : Fin m → (NumberField.RingOfIntegers K)ˣ),
      Submodule.span ℤ
            (Set.range fun (i : Fin m) ↦
              (NumberField.Units.logEmbedding K :
                  Additive (NumberField.RingOfIntegers K)ˣ →
                    NumberField.Units.dirichletUnitTheorem.logSpace K)
                ((Additive.ofMul :
                    (NumberField.RingOfIntegers K)ˣ → Additive (NumberField.RingOfIntegers K)ˣ)
                  (ε i))) =
          NumberField.Units.unitLattice K →
        Subgroup.closure (Set.range ε) ⊔ NumberField.Units.torsion K = ⊤)
    (h_NumberField_absLogHeight₁_nonneg : ∀ {K : Type u_2} [inst : Field K] [inst_1 : CharZero K] (x : K), 0 ≤ NumberField.absLogHeight₁ x)
    (h_NumberField_Units_prod_successiveMinimum_logBall_le : ∀ (K : Type u_2) [inst : Field K] [inst_1 : NumberField K],
      ∏ i ∈ Finset.range (NumberField.Units.rank K),
          ZLattice.successiveMinimum (NumberField.Units.unitLattice K) (NumberField.Units.logBall K) i ≤
        (↑(NumberField.Units.rank K).factorial : ℝ) * NumberField.Units.regulator K)
    (h_NumberField_Units_interior_logBall_nonempty : ∀ {K : Type u_2} [inst : Field K] [inst_1 : NumberField K],
      (interior (NumberField.Units.logBall K)).Nonempty)
    (h_ZLattice_successiveMinimum_pos : ∀ {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {B : Set E} {i : ℕ}
      [FiniteDimensional ℝ E] (L : Submodule ℤ E) [inst_3 : DiscreteTopology ↥L] [IsZLattice ℝ L],
      Convex ℝ B →
        (∀ x ∈ B, -x ∈ B) →
          (interior B).Nonempty →
            Bornology.IsBounded B → i < Module.finrank ℝ E → 0 < ZLattice.successiveMinimum L B i)
    (h_NumberField_Units_isClosed_logBall : ∀ {K : Type u_2} [inst : Field K] [inst_1 : NumberField K], IsClosed (NumberField.Units.logBall K))
    (h_NumberField_Units_sum_abs_le_of_mem_smul_logBall : ∀ {K : Type u_2} [inst : Field K] [inst_1 : NumberField K] {t : ℝ},
      0 ≤ t →
        ∀ {x : NumberField.Units.dirichletUnitTheorem.logSpace K},
          x ∈ t • NumberField.Units.logBall K →
            ∑ w : { w : NumberField.InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀ },
                |x w| ≤
              t)
    (h_NumberField_Units_isBounded_logBall : ∀ {K : Type u_2} [inst : Field K] [inst_1 : NumberField K],
      Bornology.IsBounded (NumberField.Units.logBall K))
    (h_NumberField_Units_neg_mem_logBall : ∀ {K : Type u_2} [inst : Field K] [inst_1 : NumberField K]
      {x : NumberField.Units.dirichletUnitTheorem.logSpace K},
      x ∈ NumberField.Units.logBall K → -x ∈ NumberField.Units.logBall K)
    (h_NumberField_Units_convex_logBall : ∀ {K : Type u_2} [inst : Field K] [inst_1 : NumberField K], Convex ℝ (NumberField.Units.logBall K))
    (h_NumberField_Units_prod_max_one_add_one_div_two : ∀ (r : ℕ), ∏ i : Fin r, Max.max 1 (((↑(↑i : ℕ) : ℝ) + 1) / 2) = (↑r.factorial : ℝ) / 2 ^ (r - 1))
    (h_NumberField_Units_absLogHeight₁_le_sum_abs_logEmbedding_div : ∀ {K : Type u_2} [inst : Field K] [inst_1 : NumberField K] (u : (NumberField.RingOfIntegers K)ˣ),
      NumberField.absLogHeight₁ (↑(↑u : NumberField.RingOfIntegers K) : K) ≤
        (∑ w : { w : NumberField.InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀ },
            |(NumberField.Units.logEmbedding K :
                  Additive (NumberField.RingOfIntegers K)ˣ →
                    NumberField.Units.dirichletUnitTheorem.logSpace K)
                ((Additive.ofMul :
                    (NumberField.RingOfIntegers K)ˣ → Additive (NumberField.RingOfIntegers K)ˣ)
                  u)
                w|) /
          (↑(Module.finrank ℚ K) : ℝ))
    :
    ∃ ε : Fin (rank K) → (𝓞 K)ˣ,
      Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤ ∧
        ∏ i, absLogHeight₁ ((ε i : 𝓞 K) : K) ≤
          ((rank K).factorial : ℝ) ^ 2 /
              (2 ^ (rank K - 1) * (finrank ℚ K : ℝ) ^ rank K) * regulator K := by
  classical
  have hrk : finrank ℝ (logSpace K) = rank K := NumberField.Units.finrank_eq_rank K
  have hd : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))
  rw [← hrk]
  obtain ⟨b₀, hb₀⟩ := h_ZLattice_exists_basis_mem_smul_successiveMinimum (unitLattice K)
    h_NumberField_Units_convex_logBall (fun x hx ↦ h_NumberField_Units_neg_mem_logBall hx) h_NumberField_Units_interior_logBall_nonempty
    h_NumberField_Units_isBounded_logBall h_NumberField_Units_isClosed_logBall
  have hex : ∀ j : Fin (finrank ℝ (logSpace K)), ∃ u : (𝓞 K)ˣ,
      logEmbedding K (Additive.ofMul u) = ((b₀ j : unitLattice K) : logSpace K) := by
    intro j
    obtain ⟨z, -, hz⟩ := (b₀ j).2
    exact ⟨Additive.toMul z, hz⟩
  choose u₀ hu₀ using hex
  refine ⟨u₀, h_NumberField_Units_closure_sup_torsion_eq_top_of_span _ ?_, ?_⟩
  · have hcomp : (fun j ↦ logEmbedding K (Additive.ofMul (u₀ j)))
        = (Submodule.subtype (unitLattice K)) ∘ b₀ := funext fun j ↦ hu₀ j
    rw [hcomp, Set.range_comp, ← Submodule.map_span, b₀.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  · have hbound : ∀ j : Fin (finrank ℝ (logSpace K)),
        absLogHeight₁ ((u₀ j : 𝓞 K) : K)
          ≤ max 1 ((((j : ℕ) : ℝ) + 1) / 2) *
              ZLattice.successiveMinimum (unitLattice K) (logBall K) j / finrank ℚ K := by
      intro j
      have hpos : 0 < ZLattice.successiveMinimum (unitLattice K) (logBall K) j :=
        h_ZLattice_successiveMinimum_pos (unitLattice K) h_NumberField_Units_convex_logBall
          (fun x hx ↦ h_NumberField_Units_neg_mem_logBall hx) h_NumberField_Units_interior_logBall_nonempty h_NumberField_Units_isBounded_logBall j.isLt
      have ht : (0 : ℝ) ≤ max 1 ((((j : ℕ) : ℝ) + 1) / 2) *
          ZLattice.successiveMinimum (unitLattice K) (logBall K) j :=
        mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hpos.le
      refine (h_NumberField_Units_absLogHeight₁_le_sum_abs_logEmbedding_div (u₀ j)).trans ?_
      gcongr
      rw [hu₀ j]
      exact h_NumberField_Units_sum_abs_le_of_mem_smul_logBall ht (hb₀ j)
    have hmin : (∏ i ∈ Finset.range (finrank ℝ (logSpace K)),
          ZLattice.successiveMinimum (unitLattice K) (logBall K) i)
        ≤ ((finrank ℝ (logSpace K)).factorial : ℝ) * regulator K := by
      rw [hrk]
      exact h_NumberField_Units_prod_successiveMinimum_logBall_le K
    have hminnn : (0 : ℝ) ≤ ∏ i ∈ Finset.range (finrank ℝ (logSpace K)),
        ZLattice.successiveMinimum (unitLattice K) (logBall K) i := by
      refine Finset.prod_nonneg fun i hi ↦ ?_
      exact (h_ZLattice_successiveMinimum_pos (unitLattice K) h_NumberField_Units_convex_logBall
        (fun x hx ↦ h_NumberField_Units_neg_mem_logBall hx) h_NumberField_Units_interior_logBall_nonempty h_NumberField_Units_isBounded_logBall
        (Finset.mem_range.1 hi)).le
    have hfacnn : (0 : ℝ) ≤ ((finrank ℝ (logSpace K)).factorial : ℝ) /
        2 ^ (finrank ℝ (logSpace K) - 1) := by positivity
    calc ∏ j, absLogHeight₁ ((u₀ j : 𝓞 K) : K)
        ≤ ∏ j : Fin (finrank ℝ (logSpace K)), (max 1 ((((j : ℕ) : ℝ) + 1) / 2) *
            ZLattice.successiveMinimum (unitLattice K) (logBall K) j / finrank ℚ K) :=
          Finset.prod_le_prod₀ (fun j _ ↦ h_NumberField_absLogHeight₁_nonneg _) fun j _ ↦ hbound j
      _ = (((finrank ℝ (logSpace K)).factorial : ℝ) / 2 ^ (finrank ℝ (logSpace K) - 1)) *
            (∏ i ∈ Finset.range (finrank ℝ (logSpace K)),
              ZLattice.successiveMinimum (unitLattice K) (logBall K) i) /
            (finrank ℚ K : ℝ) ^ finrank ℝ (logSpace K) := by
          rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin, h_NumberField_Units_prod_max_one_add_one_div_two,
            Fin.prod_univ_eq_prod_range]
      _ ≤ (((finrank ℝ (logSpace K)).factorial : ℝ) / 2 ^ (finrank ℝ (logSpace K) - 1)) *
            (((finrank ℝ (logSpace K)).factorial : ℝ) * regulator K) /
            (finrank ℚ K : ℝ) ^ finrank ℝ (logSpace K) := by
          gcongr
      _ = ((finrank ℝ (logSpace K)).factorial : ℝ) ^ 2 /
            (2 ^ (finrank ℝ (logSpace K) - 1) *
              (finrank ℚ K : ℝ) ^ finrank ℝ (logSpace K)) * regulator K := by
          field_simp

section Examples
end Examples
end NumberField.Units
end
