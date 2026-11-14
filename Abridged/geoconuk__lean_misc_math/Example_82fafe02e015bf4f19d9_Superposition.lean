module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

-- ==== Examples.geoconuk__lean_misc_math.Dependencies.ve4533931bbb6.MiscMath.Analysis.KolmogorovArnold.InnerSpace ====
public section
/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The inner-function space

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; Layer 1 of the development. Its declarations are proof:
machine-generated, kernel-checked and axiom-audited, and may be read by no one.

The Baire-category proof of the superposition theorem (Hedberg 1971, Kahane 1975) works in a
complete metric space of candidate inner functions and shows that the tuples which work are
residual. This module fixes that space:

* `monoMaps`, the monotone elements of `C(I, ℝ)`, a closed set;
* `Inner`, that set as a type — Hedberg's `H` (his Remark 2) and Kahane's `Φ` without his
  normalisation `φ(0) = 0`, `φ(1) = 1`, which is a proof device we do not need — complete
  because closed subsets of complete spaces are complete;
* `InnerTuple n`, the `2n + 1`-fold product with the sup metric, which is complete and
  therefore a Baire space.

Everything past the closedness proof is an instance Mathlib already supplies. Here `I` is
Mathlib's `unitInterval`, so an inner function is a function on `[0, 1]`; extending to `ℝ` is
the last layer's business.
-/
@[expose] public section
open unitInterval
namespace MiscMath.Analysis.KolmogorovArnold
/-- The monotone (non-decreasing) continuous real functions on `I`, as a set in `C(I, ℝ)`. -/
def monoMaps : Set C(I, ℝ) := {φ | Monotone φ}

/-- The inner-function space `H`: monotone continuous functions `I → ℝ` with the sup metric. -/
abbrev Inner : Type := monoMaps

/-- The space of `2n + 1`-tuples of inner functions, with the sup metric. -/
abbrev InnerTuple (n : ℕ) : Type := Fin (2 * n + 1) → Inner
namespace Inner

end Inner
end MiscMath.Analysis.KolmogorovArnold

end
end

-- ==== Examples.geoconuk__lean_misc_math.Examples.Example_82fafe02e015bf4f19d9_Superposition ====
/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The superposition operator and the approximation sets

Support module for `MiscMath.Analysis.KolmogorovArnold`, where the theorem is stated and where
the reader should start; Layer 1 of the development. Its declarations are proof:
machine-generated, kernel-checked and axiom-audited, and may be read by no one.

Given constants `λ_1, …, λ_n` and a tuple `ψ = (ψ_0, …, ψ_{2n})` of inner functions on
`I = [0, 1]`, the superposition of an outer function `g : ℝ → ℝ` is

  `x ↦ ∑_{q} g (∑_{p} λ_p ψ_q (x_p))`

on the cube `Iⁿ`. The representation theorem says that for a suitable universal `ψ` every
continuous `f` on the cube is such a superposition. The Baire-category proof (Hedberg 1971,
Kahane 1975) gets there by considering, for one fixed `f`, the set of tuples `ψ` that admit a
*one-step approximation* of `f` — an outer function `g` of norm at most `δ` with
`‖f - ∑_q g ∘ y_q‖ < θ` — and showing that this set is open and dense in the complete metric
space of tuples. This module defines the operator and that set, and proves the openness. The
density is Layer 2, and it is where all the work is.

## What this module proves

Fix `n`, constants `λ : Fin n → ℝ`, and a tuple `ψ` of `2n + 1` monotone continuous functions
`I → ℝ`. Write `y_q(x) = ∑_p λ_p ψ_q(x_p)` for the inner sums, continuous on the cube.

* `superpose λ ψ` is the linear operator `g ↦ ∑_q g ∘ y_q` from bounded continuous functions
  on `ℝ` to continuous functions on the cube; it has norm at most `2n + 1`.
* For a continuous `f` on the cube and reals `δ, θ`, the **approximation set**
  `approxSet λ δ θ f` consists of the tuples `ψ` for which some bounded continuous `g` with
  `‖g‖ ≤ δ` has `‖f - superpose λ ψ g‖ < θ`.
* **Theorem** (`isOpen_approxSet`): `approxSet λ δ θ f` is open in the sup metric on tuples.
  Equivalently, if an outer function `g` works for `ψ`, it works for every tuple close enough
  to `ψ`.

The inner sums and the superposition depend continuously on the tuple `ψ`
(`continuous_innerSum`, `continuous_superpose`), which is the whole content of the openness.

## Source

- T. Hedberg, *The Kolmogorov superposition theorem*, Appendix II to H. S. Shapiro, *Topics
  in Approximation Theory*, Lecture Notes in Math. 187, Springer, 1971, pp. 267–275. The set
  `U_f` of his Lemma 2 (p. 269), for `‖f‖ = 1`: the 5-tuples `(φ_1, …, φ_5)` for which some
  `g ∈ C(ℝ)` has `|g(t)| ≤ 1/7` and `|f(x, y) - ∑_i g(φ_i(x) + λ φ_i(y))| < 7/8`. His openness
  argument is the single sentence "if `g` works for a particular 5-tuple, it does so for all
  sufficiently neighboring 5-tuples". Here the constants are parameters `δ, θ`, the dimension
  is general, and the inner functions are the factored `λ_p ψ_q(x_p)` of his Theorem 1.
- J.-P. Kahane, *Sur le théorème de superposition de Kolmogorov*, J. Approx. Theory 13
  (1975) 229–234. The set `Ω(f)` on p. 231, for `f ≠ 0`: the tuples for which some `h ∈ C(I)`
  satisfies his (6), namely `‖h‖ ≤ ‖f‖` and `‖f - ∑_q h(∑_p λ_p φ_q(x_p))‖ < (1 - ε)‖f‖`;
  "visiblement `Ω(f)` est un ouvert". His bounds are relative to `‖f‖`, ours absolute, which
  is why Layer 2 assumes `‖f‖ ≤ 1`.

## Sanity checks

The `example`s below compute the definitions in the `n = 1` case with the identity inner
functions and `λ = 1` — the inner sums are `x ↦ x_0` and the superposition is `3 g(x_0)` —
and check the approximation sets at their edges: for `f = 0` every tuple is in
`approxSet λ δ θ 0` as soon as `0 ≤ δ` and `0 < θ` (take `g = 0`), and `approxSet λ δ θ f` is
empty when `θ ≤ 0`. The first says the definition is not vacuous; the second that the strict
inequality is really there.

## Relation to Mathlib

The operator is a `ContinuousLinearMap` between Mathlib's Banach spaces `ℝ →ᵇ ℝ`
(`BoundedContinuousFunction`) and `C(Fin n → I, ℝ)`; the openness rests on
`ContinuousMap.continuous_postcomp` and `ContinuousMap.continuous_precomp` from
`Topology/CompactOpen.lean`, which apply because the sup-metric topology on `C(K, ℝ)` for
compact `K` is the compact-open topology. Nothing about superpositions of this shape is in
Mathlib.
-/
@[expose] public section
open unitInterval BoundedContinuousFunction
namespace MiscMath.Analysis.KolmogorovArnold
variable {n : ℕ}
/-- The coordinate projection `x ↦ x p` as a continuous map on the cube. -/
def proj (p : Fin n) : C(Fin n → I, I) := ⟨fun x => x p, continuous_apply p⟩

/-- The `q`-th inner sum `y_q(x) = ∑_p λ_p ψ_q(x_p)`, as a continuous map on the cube. -/
def innerSum (lam : Fin n → ℝ) (ψ : InnerTuple n) (q : Fin (2 * n + 1)) : C(Fin n → I, ℝ) :=
  ∑ p, lam p • ((ψ q : C(I, ℝ)).comp (proj p))
set_option linter.unusedVariables false in
axiom _root_.MiscMath.Analysis.KolmogorovArnold.innerSum_apply : ∀ {n : ℕ} (lam : Fin n → ℝ) (ψ : MiscMath.Analysis.KolmogorovArnold.InnerTuple n)
  (q : Fin (2 * n + 1)) (x : Fin n → (↑unitInterval : Type)),
  (MiscMath.Analysis.KolmogorovArnold.innerSum lam ψ q : (Fin n → (↑unitInterval : Type)) → ℝ) x =
    ∑ p : Fin n,
      lam p * ((↑(ψ q) : C((↑unitInterval : Type), ℝ)) : (↑unitInterval : Type) → ℝ) (x p)

/-- The superposition `g ↦ ∑_q g ∘ y_q` as a linear map. -/
def superposeₗ (lam : Fin n → ℝ) (ψ : InnerTuple n) : (ℝ →ᵇ ℝ) →ₗ[ℝ] C(Fin n → I, ℝ) where
  toFun g := ∑ q, g.toContinuousMap.comp (innerSum lam ψ q)
  map_add' g₁ g₂ := by
    ext x
    simp [ContinuousMap.sum_apply, Finset.sum_add_distrib]
  map_smul' c g := by
    ext x
    simp [ContinuousMap.sum_apply, Finset.mul_sum]
theorem norm_superposeₗ_le (lam : Fin n → ℝ) (ψ : InnerTuple n) (g : ℝ →ᵇ ℝ) :
    ‖superposeₗ lam ψ g‖ ≤ (2 * n + 1) * ‖g‖ := by
  calc ‖superposeₗ lam ψ g‖
      = ‖∑ q, g.toContinuousMap.comp (innerSum lam ψ q)‖ := rfl
    _ ≤ ∑ q : Fin (2 * n + 1), ‖g.toContinuousMap.comp (innerSum lam ψ q)‖ := norm_sum_le _ _
    _ ≤ ∑ _q : Fin (2 * n + 1), ‖g‖ :=
        Finset.sum_le_sum fun q _ =>
          (ContinuousMap.norm_le _ (norm_nonneg g)).mpr fun x => g.norm_coe_le_norm _
    _ = (2 * n + 1) * ‖g‖ := by simp

/-! ## Sanity checks -/
section SanityChecks

end SanityChecks
end MiscMath.Analysis.KolmogorovArnold
