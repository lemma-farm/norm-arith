module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.v9b9f861369a1.ForTauCeti.Analysis.OperatorIdeal.Family.Basic ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Thinking
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option warningAsError true
/-!
# Operator ideal families

An **operator ideal** in the sense of Pietsch is a rule assigning to every pair
of spaces `E`, `F` a linear subspace of `E →L[𝕜] F` that is stable under
composition with arbitrary bounded maps on either side, together with a norm on
that subspace dominating the operator norm and submultiplicative against outer
compositions.  Because Davis--Kahan compares operators *between different
spaces*, the ideal must be handled as a coherent family across all pairs at
once, not as a norm on a single endomorphism algebra.

The families here range over **Hilbert** spaces, with source and target still in
independent universes.  See "Why Hilbert and not Banach" below: the restriction
is forced by the examples, not by the laws.

## The single-field representation

The family is presented by exactly one datum, an extended-real-valued **gauge**

```
gauge : (E →L[𝕜] F) → ℝ≥0∞
```

defined on *all* operators, with the ideal recovered as its finiteness domain
`OperatorIdealFamily.carrier`.  This is the classical presentation of a symmetric
norming function (Gohberg--Krein): an operator lies in the ideal exactly when its
ideal norm is finite.  Three things follow.

* **Extensionality is structural.**  Two families with the same gauge are equal
  (`OperatorIdealFamily.ext`), because the gauge is the only field.  A
  representation carrying membership and a gauge as *independent* data cannot
  have such a theorem: the gauge is then unconstrained off the ideal, so two
  families can agree on every ideal element and still differ.
* **Every law is unconditional.**  In `ℝ≥0∞` the triangle inequality, the
  homogeneity `gauge (c • A) = ‖c‖ₑ * gauge A`, and the ideal bound
  `gauge (L ∘L A ∘L R) ≤ ‖L‖ₑ * gauge A * ‖R‖ₑ` all hold verbatim at
  non-members, so no law needs a membership hypothesis and no lemma needs to
  carry one.
* **The axiom list is short.**  Four laws suffice.  Closure of the ideal under
  `0`, `+`, `•`, `-`, and finite sums is a *consequence* (it is
  `Submodule` membership for `carrier`), `gauge 0 = 0` follows from homogeneity
  at `c = 0`, and definiteness follows from `enorm_le_gauge`.

## Why Hilbert and not Banach

The four laws are statements about a norm, and every one of them is meaningful
verbatim for Banach `E`, `F`.  The *examples* are not.  Of the five gauges this
development has — the operator norm, the finite Ky Fan gauges, Schatten `p`,
trace class and Hilbert--Schmidt — only the first survives outside Hilbert
space, and the obstruction is `gauge_add_le`, not the definition.  Concretely,
for the finite Ky Fan gauge `∑_{n < k} aₙ(A)` the *gauge* is defined at full
Banach generality (`ContinuousLinearMap.approximationNumber` is stated for
seminormed spaces over a `NontriviallyNormedField`) while its subadditivity is
Hilbertian: the proof runs through singular values and majorization, and the
classical additivity of approximation numbers,
`a_{m+n}(S + T) ≤ aₘ(S) + aₙ(T)`, does **not** recover it — already at `k = 2`
that bound only gives `a₀(S) + 2a₀(T) + a₁(S)`, which is not
`∑_{n<2} aₙ(S) + ∑_{n<2} aₙ(T)`.

So a Banach-wide version of this structure would be a notion with one instance
and no way to acquire the motivating ones.  The parameters are therefore Hilbert
throughout.  Re-widening is a purely mechanical edit should an instance ever
appear: no proof in this file uses the inner product, only the norm.

## Layering

`OperatorIdealFamily` keeps **independent source and target universes**.  Adjoint
symmetry cannot be added at that generality: `A✝` swaps the roles of source and
target, so a family closed under adjoints must be defined on a single universe.
That is `SymmetricOperatorIdealFamily`, which extends the diagonal
instantiation.

The two universes occur only through `max v w` in the type of the structure
itself, so `linter.checkUnivs` flags them.  **They stay independent, and the
argument is the layering itself rather than an appeal to generality**:

* `SymmetricOperatorIdealFamily` extends `OperatorIdealFamily.{u, v, v}` — it
  *is* the diagonal instantiation.  Collapse `v` and `w` and `.{u, v, v}` becomes
  `.{u, v}`: the two structures acquire the same generality, and the distinction
  this section is about stops existing.  The rectangular layer earns its second
  universe by being the thing the symmetric layer specializes.
* `Family/OperatorNorm.lean` carries a hand-written specialization of
  `instIsCompleteOperatorNormIdealFamily` precisely because the general instance
  is stated at three independent universes and instance search cannot see it once
  the symmetric family equates the last two.

So the independence is exercised, not merely declared; the linter's heuristic
reads the structure's type, where it is invisible.

## Main definitions

* `TauCeti.OperatorIdealFamily`: the gauge and its four laws.
* `TauCeti.OperatorIdealFamily.carrier`: the ideal, as a `Submodule`.
* `TauCeti.OperatorIdealFamily.Elem`: the ideal as a normed space in its own
  right — a type synonym for the carrier carrying the *ideal* norm rather than
  the operator norm inherited from the ambient space.
* `TauCeti.OperatorIdealFamily.IsComplete`: completeness of the ideal, expressed
  as `CompleteSpace` for that norm rather than as a hand-rolled Cauchy criterion.
* `TauCeti.SymmetricOperatorIdealFamily`: the adjoint-invariant diagonal layer.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/OperatorIdeal/UnitarilyInvariant/RectangularFamily.lean`
  (`RectangularSymmetricIdealFamily`, Jon Crall / OpenAI GPT-5.6 Thinking); Apache 2.0.
* Extraction class: **redesigned**.  Per the signature-polish backlog the free-data presentation
  (`Mem` plus a total real gauge constrained only on members, one universe,
  hand-rolled completeness, fourteen fields) is replaced here by the
  single-gauge presentation above, and this is the only presentation of an
  operator ideal in the library.  The legacy structure was retired downstream on
  2026-08-27, together with both directions of the conversion between the two and
  the four concrete ideals that were built by converting a canonical family into a
  legacy record and back.  Its free data survives only as
  `SymmetricOperatorIdealFamily.Core` in
  `DavisKahan/OperatorIdeal/UnitarilyInvariant/FamilyCore.lean`: constructor
  arguments for `ofCore`, carrying no gauge of their own and used by the two
  source-facing Hilbert--Schmidt ideals, which are families from the moment they
  are defined.
-/
public section
namespace TauCeti
open scoped ENNReal
universe u v w
-- What the linter reports, verbatim, with the suppression removed:
--   `OperatorIdealFamily`: universes `v`, `w` only occur together.  This usually
--   means there is a `max` expression in the type where none of these universes
--   appear on their own.
-- The observation is correct and the conclusion does not follow here.  `v` and `w`
-- are invisible apart *in this structure's type*, which is all the linter reads;
-- they are apart in its fields, and one consumer depends on exactly that:
-- `SymmetricOperatorIdealFamily` extends `OperatorIdealFamily.{u, v, v}`.  It is the
-- diagonal instantiation of this structure, so collapsing `v` and `w` would make the
-- two layers equally general and delete the distinction the module docstring calls
-- the point of the design.  `Family/OperatorNorm.lean`'s specialization of
-- `instIsCompleteOperatorNormIdealFamily` is a second place the independence bites:
-- it exists because instance search cannot find the three-universe instance once the
-- symmetric family equates the last two.
-- Decided after measuring both alternatives; the earlier
-- version of this comment said the fix was to collapse them and deferred to that lane.
-- Written here rather than left silent because this is the only one
-- of the library's ten linter suppressions with no reason at its site, and
-- `ForTauCeti/README.md` §207 forbids silencing a linter without one.
set_option linter.checkUnivs false in
/-- A **rectangular operator ideal family** over `𝕜`, presented by its gauge.

`gauge A` is the ideal norm of `A`, taken in `ℝ≥0∞` so that it is defined on
every bounded operator: `A` belongs to the ideal exactly when `gauge A ≠ ∞`
(`OperatorIdealFamily.carrier`).  Source and target are Hilbert spaces in
independent universes (see the module docstring for why Hilbert); adjoint
symmetry is added on the diagonal by `SymmetricOperatorIdealFamily`. -/
structure OperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  /-- The ideal norm, extended by `∞` off the ideal. -/
  gauge : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → ℝ≥0∞
  /-- The gauge is subadditive. -/
  gauge_add_le : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A B : E →L[𝕜] F), gauge (A + B) ≤ gauge A + gauge B
  /-- The gauge is absolutely homogeneous.  At `c = 0` this forces
  `gauge 0 = 0`, ruling out the everywhere-infinite gauge. -/
  gauge_smul : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (c : 𝕜) (A : E →L[𝕜] F), gauge (c • A) = ‖c‖ₑ * gauge A
  /-- The gauge dominates the operator norm.  Together with `gauge_add_le` this
  makes the gauge a genuine norm on the ideal rather than a seminorm. -/
  enorm_le_gauge : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), ‖A‖ₑ ≤ gauge A
  /-- The two-sided ideal law.  Finiteness of `‖L‖ₑ` and `‖R‖ₑ` makes this
  imply that the ideal is stable under outer composition. -/
  gauge_comp_le : ∀ {E H : Type v} {F G : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
      [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
      (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E),
      gauge (L ∘L A ∘L R) ≤ ‖L‖ₑ * gauge A * ‖R‖ₑ
namespace OperatorIdealFamily
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E H : Type v} {F G : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (N : OperatorIdealFamily.{u, v, w} 𝕜)

/-- The gauge of the zero operator is zero. -/
@[simp]
axiom gauge_zero : N.gauge (0 : E →L[𝕜] F) = 0
/-- The gauge is definite: only the zero operator has gauge zero.  This is forced rather than
assumed -- it follows from `enorm_le_gauge`, since the operator norm is already definite. -/
axiom gauge_eq_zero {A : E →L[𝕜] F} (h : N.gauge A = 0) : A = 0

/-- The gauge is unchanged by negation. -/
@[simp]
axiom gauge_neg (A : E →L[𝕜] F) : N.gauge (-A) = N.gauge A

/-- The ideal itself: the operators of finite gauge, as a submodule.

Closure under `0`, `+` and `•` is a consequence of the gauge laws, so the
module structure of the ideal does not have to be assumed. -/
@[expose]
def carrier : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {A | N.gauge A ≠ ∞}
  zero_mem' := by simp
  add_mem' {A B} hA hB := by
    refine ne_top_of_le_ne_top ?_ (N.gauge_add_le A B)
    exact ENNReal.add_ne_top.mpr ⟨hA, hB⟩
  smul_mem' c A hA := by
    rw [Set.mem_ofPred_eq, N.gauge_smul]
    exact ENNReal.mul_ne_top (by simp) hA

/-- The ideal between `E` and `F`, as a type carrying the **ideal** norm.

This is deliberately a type synonym rather than the subtype itself: the subtype
already inherits the *operator* norm from `E →L[𝕜] F`, and the two norms differ.

**`@[expose]`, and this is the one place in the group that needs it.**  `Elem` is
a *type*: the compiler has to see that it is a subtype in order to infer the same
representation for `Elem.val` and `Elem.mk` here as in any consuming module, and
it says so — *"locally inferred compilation type differs from type that would be
inferred in other modules"*.  That is not the `api-design` rubric's
expose-instead-of-a-lemma anti-pattern, which is about proofs relying on defeq;
no lemma can substitute for a type's representation.
-/
@[expose]
def Elem (N : OperatorIdealFamily.{u, v, w} 𝕜) (E : Type v) (F : Type w)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] : Type max v w :=
  _root_.Subtype fun A : E →L[𝕜] F => A ∈ N.carrier
namespace Elem
variable {N}
/-- The underlying operator of an ideal element. -/
-- `@[expose]` forced by the same compiler limitation as `Elem` above: accessors on an
-- unexposed type synonym re-infer a different compilation type downstream. Revisit when
-- the limitation the compiler reports is lifted.
@[expose]
def val (A : N.Elem E F) : E →L[𝕜] F := Subtype.val (p := fun A => A ∈ N.carrier) A

/-- An ideal element has finite gauge -- the fact that makes `toReal` lossless on it, and hence
the reason the ideal norm can be real-valued while the gauge is `ℝ≥0∞`-valued. -/
axiom gauge_val_ne_top (A : N.Elem E F) : N.gauge A.val ≠ ∞

/-- Ideal elements are equal when their underlying operators are.  Tagged `@[ext]`, so `ext`
reduces any such goal to the operators. -/
@[ext] axiom ext {A B : N.Elem E F} (h : A.val = B.val) : A = B

/-- The ideal is an additive subgroup of the bounded operators, inherited from its carrier. -/
instance : AddCommGroup (N.Elem E F) :=
  inferInstanceAs (AddCommGroup (N.carrier : Submodule 𝕜 (E →L[𝕜] F)))

/-- The zero ideal element is the zero operator. -/
@[simp] axiom val_zero : (0 : N.Elem E F).val = 0
/-- Addition of ideal elements is addition of operators. -/
@[simp] axiom val_add (A B : N.Elem E F) : (A + B).val = A.val + B.val
/-- Negation of an ideal element is negation of the operator. -/
@[simp] axiom val_neg (A : N.Elem E F) : (-A).val = -A.val

/-- The ideal norm, as a real-valued norm on the ideal. -/
noncomputable instance : NormedAddCommGroup (N.Elem E F) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun A => (N.gauge A.val).toReal
      map_zero' := by
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        change (N.gauge (0 : N.Elem E F).val).toReal = 0
        rw [val_zero, N.gauge_zero, ENNReal.toReal_zero]
      add_le' := fun A B => by
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        change (N.gauge (A + B).val).toReal ≤ (N.gauge A.val).toReal + (N.gauge B.val).toReal
        rw [val_add, ← ENNReal.toReal_add A.gauge_val_ne_top B.gauge_val_ne_top]
        exact ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨A.gauge_val_ne_top, B.gauge_val_ne_top⟩)
          (N.gauge_add_le A.val B.val)
      neg' := fun A => by
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        change (N.gauge (-A).val).toReal = (N.gauge A.val).toReal
        rw [val_neg, N.gauge_neg]
      eq_zero_of_map_eq_zero' := fun A hA => by
        refine ext ?_
        rw [val_zero]
        exact N.gauge_eq_zero
          (((ENNReal.toReal_eq_zero_iff _).mp hA).resolve_right A.gauge_val_ne_top) }

end Elem
/-- Completeness of an ideal family, stated as `CompleteSpace` for the ideal
norm rather than as a hand-rolled Cauchy criterion.

Completeness of the target is available from the ambient assumptions, exactly as
for `E →L[𝕜] F`: an ideal norm cannot repair an incomplete target. -/
class IsComplete (N : OperatorIdealFamily.{u, v, w} 𝕜) : Prop where
  completeSpace : ∀ {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
    CompleteSpace (N.Elem E F)

end OperatorIdealFamily
/-- A **symmetric** (adjoint-invariant) operator ideal family on Hilbert spaces.

Adjoint invariance is stated on the diagonal instantiation of
`OperatorIdealFamily` because `ContinuousLinearMap.adjoint` exchanges the source
and target spaces: a family closed under adjoints cannot keep the two universes
independent. -/
structure SymmetricOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    extends OperatorIdealFamily.{u, v, v} 𝕜 where
  /-- The gauge is unchanged by passing to the adjoint. -/
  gauge_adjoint : ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), toOperatorIdealFamily.gauge A.adjoint = toOperatorIdealFamily.gauge A
namespace SymmetricOperatorIdealFamily
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

variable (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)

end SymmetricOperatorIdealFamily
end TauCeti

end
end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Dependencies.v9b9f861369a1.DavisKahan.OperatorIdeal.CanonicalRealView ====
public section
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Real-valued view of a canonical symmetric ideal family

`TauCeti.SymmetricOperatorIdealFamily` stores its gauge in `ℝ≥0∞`, extended by `∞`
off the ideal.  That is the right presentation for the library: it makes the gauge
total, gives the structure an `ext` lemma, and is what a Mathlib-bound development
wants.  The Davis--Kahan estimates, by contrast, are stated and proved in `ℝ` — the
paper's constants are real, and the proofs run on `linarith`, `nlinarith` and
`mul_le_mul_of_nonneg_*`, none of which work over `ℝ≥0∞`.

This file supplies the missing `ℝ` view, so that migrating a theorem off the
historical free-data record — a membership predicate plus a real gauge, since
retired — is a **retype and not a re-proof**.

## Why this file exists at all

Phase C of the §13.2 migration was released three times without being started, and
the recorded reason each time was that it is "a re-proof over a differently-valued
gauge": every conclusion changes type from `ℝ` to `ℝ≥0∞`, `gauge_nonneg` goes
vacuous, `∞` cases appear, and Neumann summability in `ℝ` and in `ℝ≥0∞` are
different theorems.

All of that is true, and all of it is about a question the lane does not have to
answer.  *Which structure parameterizes a theorem* and *which numeric type its
estimate lives in* are separable, and they had been conflated because the canonical
family had no `ℝ` view to migrate onto — only `KyFanDominantIdealFamily` had one,
and that structure is strictly stronger, so retyping onto it would weaken every
theorem it touched.  With the view below, the 18 remaining legacy-binder modules
change their binder and keep their proofs; restating the estimates in `ℝ≥0∞` becomes
a separate and genuinely optional decision.

## Where the `ℝ≥0∞` arithmetic lives

Phase C stated every lemma here over `gaugeReal`/`Mem` but *proved* it through the
historical record, so that retyping the tree cost no proof work.  Phase D paid that debt: every proof below now runs on the canonical laws
directly, and this file no longer imports the adapter.

The design point is where the bill landed.  Turning an `ℝ≥0∞` law into an `ℝ` one needs
a finiteness side condition at each step -- `ENNReal.toReal_mono` wants the larger side
finite, `toReal_add` wants both summands finite -- and that reasoning appears **in this
file only**, not at the 117 call sites across 30 modules that a direct migration would
have had to re-prove.  Every `Mem` hypothesis below is exactly the finiteness those
conversions consume.

Completeness is the one law that genuinely needs `IsComplete`, so that instance is
assumed on `gaugeReal_complete` alone rather than on the section; the other laws hold
for any canonical symmetric family.
-/
open scoped ENNReal
namespace TauCeti
namespace SymmetricOperatorIdealFamily
universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)
/-- Membership in the ideal: the gauge is finite.

The same predicate as `OperatorIdealFamily.carrier`, spelled as the `Mem` the
Davis--Kahan statements are written against. -/
abbrev Mem (A : E →L[𝕜] F) : Prop :=
  N.toOperatorIdealFamily.gauge A ≠ ∞
/-- The ideal gauge read in `ℝ`.  Meaningful on members; off the ideal the stored
gauge is `∞` and `ENNReal.toReal` sends it to `0`, which is why every lemma below
that needs a value carries a `Mem` hypothesis. -/
noncomputable abbrev gaugeReal (A : E →L[𝕜] F) : ℝ :=
  (N.toOperatorIdealFamily.gauge A).toReal

/-! ### The ideal laws, in `ℝ` -/

/-- The real gauge is nonnegative on members. -/
axiom gaugeReal_nonneg {A : E →L[𝕜] F} (_hA : N.Mem A) : 0 ≤ N.gaugeReal A

/-- The two-sided estimate, in `ℝ`. -/
axiom gaugeReal_comp_le (L : F →L[𝕜] G) (R : H →L[𝕜] E) {A : E →L[𝕜] F}
    (hA : N.Mem A) :
    N.gaugeReal (L ∘L A ∘L R) ≤ ‖L‖ * N.gaugeReal A * ‖R‖

/-! ### Consequences -/

variable {ι : Type*}

/-! ### The operator-norm family -/

end SymmetricOperatorIdealFamily
end TauCeti

end

-- ==== Examples.AIQ_Kitware__aiq_davis_kahan_1970_rotation_eigenvectgors_perturbation_formalization.Examples.Example_25198d002aa92b7ec531_Bounded ====
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Bound/inverse Sylvester estimates

This module isolates the exact dimension-free form of Davis--Kahan Theorem 5.1.
The Neumann construction and ideal-norm convergence are separated so that the
analytic difficulty is visible in the dependency graph.
-/
namespace TauCeti
namespace DavisKahan
namespace Sylvester
open scoped InnerProductSpace
universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
/-- Explicit bounded two-sided inverse data for an endomorphism. -/
structure BoundedInverseData (A : E →L[𝕜] E) where
  inv : E →L[𝕜] E
  left_inv : inv ∘L A = ContinuousLinearMap.id 𝕜 E
  right_inv : A ∘L inv = ContinuousLinearMap.id 𝕜 E
namespace BoundedInverseData

end BoundedInverseData
omit [CompleteSpace E] in
/-- Powers of a continuous endomorphism satisfy the expected operator-norm bound. -/
axiom opNorm_pow_le (T : E →L[𝕜] E) (n : ℕ) :
    ‖T ^ n‖ ≤ ‖T‖ ^ n
/-- The `n`th term in the Neumann construction for `A X - X B = C`. -/
noncomputable def sylvesterNeumannTerm
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) (n : ℕ) : F →L[𝕜] E :=
  (hA.inv ^ (n + 1)) ∘L C ∘L (B ^ n)


/-- Geometric bound for one Neumann term. -/
theorem gauge_sylvesterNeumannTerm_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →L[𝕜] E}
    (hA : BoundedInverseData A) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C) (n : ℕ) :
    N.gaugeReal (sylvesterNeumannTerm hA B C n)
      ≤ ‖hA.inv‖ ^ (n + 1) * N.gaugeReal C * ‖B‖ ^ n := by
  unfold sylvesterNeumannTerm
  have hcomp := N.gaugeReal_comp_le (hA.inv ^ (n + 1)) (B ^ n) hC
  have hinv := opNorm_pow_le hA.inv (n + 1)
  have hBpow := opNorm_pow_le B n
  have hgauge := N.gaugeReal_nonneg hC
  calc
    N.gaugeReal ((hA.inv ^ (n + 1)) ∘L C ∘L (B ^ n))
        ≤ ‖hA.inv ^ (n + 1)‖ * N.gaugeReal C * ‖B ^ n‖ := hcomp
    _ ≤ (‖hA.inv‖ ^ (n + 1) * N.gaugeReal C) * ‖B ^ n‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinv hgauge) (norm_nonneg (B ^ n))
    _ ≤ (‖hA.inv‖ ^ (n + 1) * N.gaugeReal C) * ‖B‖ ^ n := by
      exact mul_le_mul_of_nonneg_left hBpow
        (mul_nonneg (pow_nonneg (norm_nonneg hA.inv) _) hgauge)

end Sylvester
end DavisKahan
end TauCeti