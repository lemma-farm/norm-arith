import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Real.Pointwise
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Spectrum

-- ==== Examples.SauersML__group_approximation.Dependencies.v0a2f74d14b3e.GroupApproximation.Analysis.CStarTensorProductSeminorm ====
section
set_option warningAsError true
/-!
# C⋆-seminorms on a complex ⋆-algebra, and the ones coming from representations

## Why this file exists

The minimal (spatial) tensor product `A ⊗_min B` is, by definition, the
completion of the algebraic tensor product `A ⊙ B` in the norm

  `‖x‖_min = ‖(π ⊗ ρ)(x)‖`,

the operator norm of the image of `x` under a product representation on
`H ⊗ K`, for faithful representations `π : A → B(H)`, `ρ : B → B(K)`.  Two
separate things have to be proved about that recipe:

1. the resulting function really is a C⋆-norm on the ⋆-algebra `A ⊙ B`;
2. it does not depend on the choice of `π` and `ρ` (Takesaki).

This file settles (1) **in complete generality**, once and for all: the
operator seminorm attached to *any* representation of a complex ⋆-algebra by
adjointable operators on an inner product space is a C⋆-seminorm, and is a
C⋆-norm as soon as the representation is injective.  (Only that direction is
proved.  The converse --- definiteness forces injectivity --- is immediate from
`seminorm_eq_zero_iff` but is not stated, so "exactly when", as an earlier
version of this paragraph put it, overstates what is here.)  When the product
representation of `A ⊙ B` on `H ⊗ K` is eventually constructed, its C⋆-property
is then immediate from `StarRep.isCStarSeminorm` below; nothing about tensor
products has to be re-proved.

Point (2) is the hard theorem and is **not** proved anywhere in this
development; see the roadmap in `CStarTensorProduct.lean`.

As in `CStarTensorProductAdjointable.lean`, no completeness is assumed
anywhere: a representation on a pre-Hilbert space already gives a C⋆-seminorm.
This is what allows the spatial construction to live on the *algebraic* tensor
product `H ⊗[ℂ] K`, whose completion Mathlib does not have.

## Contents

* `IsCStarSeminorm` --- a submultiplicative seminorm satisfying the
  C⋆-identity `p (star a * a) = p a * p a`.  Star-invariance is deliberately
  *not* an axiom: it is a theorem (`IsCStarSeminorm.map_star`).
* `IsCStarNorm` --- a definite C⋆-seminorm.
* `StarRep` --- a representation of a complex ⋆-algebra by adjointable
  operators on an inner product space.
* `StarRep.isCStarSeminorm`, `StarRep.isCStarNorm_of_injective`.

## Manuscript status

Infrastructure only; certifies no manuscript step.  The exactness and
nuclearity rows of `non_mf_groups_exist.tex` remain **MISSING**.
-/
namespace GroupApproximation
namespace CStarTensor
open scoped InnerProductSpace
universe u v
/-! ## C⋆-seminorms -/
/-- A **C⋆-seminorm** on a complex ⋆-algebra: a submultiplicative seminorm
satisfying the C⋆-identity.

Star-invariance is not assumed; it follows (`IsCStarSeminorm.map_star`). -/
structure IsCStarSeminorm {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
    (p : A → ℝ) : Prop where
  /-- A seminorm is nonnegative. -/
  nonneg : ∀ a : A, 0 ≤ p a
  /-- The triangle inequality. -/
  add_le : ∀ a b : A, p (a + b) ≤ p a + p b
  /-- Absolute homogeneity for the complex scalars. -/
  smul : ∀ (c : ℂ) (a : A), p (c • a) = ‖c‖ * p a
  /-- Submultiplicativity. -/
  mul_le : ∀ a b : A, p (a * b) ≤ p a * p b
  /-- The C⋆-identity. -/
  cstar : ∀ a : A, p (star a * a) = p a * p a
namespace IsCStarSeminorm
variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] {p : A → ℝ}
/-- A C⋆-seminorm vanishes at zero. -/
axiom map_zero (h : IsCStarSeminorm p) : p 0 = 0

end IsCStarSeminorm
/-- A **C⋆-norm** on a complex ⋆-algebra: a definite C⋆-seminorm. -/
structure IsCStarNorm {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
    (p : A → ℝ) : Prop where
  /-- The underlying C⋆-seminorm.  Spelled as a field rather than by
  `extends`, so that the declaration is insensitive to the Lean version's
  placement of the `extends` clause relative to the `: Prop` ascription. -/
  isCStarSeminorm : IsCStarSeminorm p
  /-- Definiteness. -/
  eq_zero : ∀ a : A, p a = 0 → a = 0
/-! ## Representations by adjointable operators -/

namespace StarRep
variable {A : Type u} {V : Type v} [Ring A] [StarRing A] [Algebra ℂ A]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

end StarRep
end CStarTensor
end GroupApproximation

end

-- ==== Examples.SauersML__group_approximation.Dependencies.v0a2f74d14b3e.GroupApproximation.Analysis.CStarSeminormQuotient ====
section
set_option warningAsError true
/-!
# Star-stable ideals, quotients, and suprema of C⋆-seminorms

## Where this sits in the tensor-product lane

`CStarTensorProduct.lean` records the roadmap for the missing minimal tensor
product.  Stage A is done: the operator seminorm of a ⋆-representation is a
C⋆-seminorm (`StarRep.isCStarSeminorm`), a C⋆-norm when the representation is
faithful.  The two things the roadmap then names are

* a *canonical* norm, which the textbook route gets from Takesaki's
  independence theorem (Stage C, research scale), and for which the roadmap
  records a cheap alternative: *"define the minimal norm as a supremum over a
  set of representations manufactured from states.  The pointwise supremum of
  a bounded family of C⋆-seminorms is a C⋆-seminorm --- squaring is monotone
  on `[0, ∞)`, so the C⋆-identity survives the supremum --- so this is
  cheap."*  That sentence is `isCStarSeminorm_iSup` below, proved.
* quotients, which `CStarExactness.lean` lists among the things Mathlib does
  not have: *"`Mathlib/Analysis/Normed/Group/Quotient.lean` has
  `Ideal.Quotient.semiNormedCommRing` and `normedCommRing`, both commutative
  only; nothing makes `B ⧸ J` a C⋆-algebra."*

This file supplies the parts of both that are reachable at the pin, and is
explicit about the part that is not.

## What is proved here

* `IsStarStable` --- a two-sided ideal closed under the involution --- and the
  `Star`, `InvolutiveStar` and `StarRing` structures it induces on `A ⧸ I`.
  Mathlib has none of these: they are built here the same way
  `Analysis/NormMatrixCorona.lean` builds them for the matrix corona, by
  lifting the involution along `QuotientAddGroup.lift`.  This is the
  *algebraic* half of a C⋆-quotient and it is unconditional.
* `IsCStarSeminorm.comp` --- a C⋆-seminorm pulls back along a
  ⋆-homomorphism.
* `isCStarSeminorm_iSup` --- the pointwise supremum of a nonempty pointwise
  bounded family of C⋆-seminorms is a C⋆-seminorm.  The C⋆-identity is the
  only interesting field, and it is proved by `Real.sqrt` rather than by a
  monotone-image-of-a-supremum lemma, so nothing about continuity is needed.
* `IsCStarSeminorm.nullIdeal` --- the null set of a C⋆-seminorm is a two-sided
  star-stable ideal, and the seminorm is constant on its cosets.
* `exists_isCStarNorm_on_quotient` --- **the payoff**: every C⋆-seminorm on a
  complex ⋆-algebra descends to a genuine C⋆-*norm* on the quotient by its
  null ideal.  Combined with `isCStarSeminorm_iSup` and
  `StarRep.isCStarSeminorm`, an arbitrary nonempty bounded family of
  ⋆-representations of `A` now yields a C⋆-normed ⋆-algebra canonically
  attached to that family, with no faithfulness hypothesis on any member.

## What is *not* proved here, and why

**This is not the C⋆-quotient theorem.**  For a C⋆-algebra `B` and a closed
two-sided ideal `J`, the assertion that the *quotient norm*
`‖b + J‖ = inf {‖b + j‖ : j ∈ J}` satisfies the C⋆-identity is a genuine
theorem whose standard proof runs through an approximate unit of `J` and the
identity `‖b + J‖ = lim_λ ‖b - b e_λ‖`.  Nothing below proves it, and nothing
below is a substitute for it: the norms handled here are C⋆-seminorms *given
in advance*, and the descent to the quotient by the null ideal is the trivial
direction (the null ideal is exactly where the given seminorm already
vanishes, so no infimum is ever taken).  The pin does carry
`Mathlib/Analysis/CStarAlgebra/ApproximateUnit.lean`, so the quotient theorem
is not obviously out of reach, but it is not done here.  For the one quotient
this development needs it for — the tracial matrix quotient — it *is* now
done, through a bespoke approximate unit of its null ideal: the identity in
`Analysis/TracialQuotientCStarIdentity.lean`, the instances and the exact
norm formula in `Analysis/TracialQuotientCStar.lean`.  The theorem for a
general `B` and `J` remains unformalized.

Consequently the exactness rows of `non_mf_groups_exist.tex` (`SO.16`) and the
nuclearity row (`RE.05`) are untouched: exactness is defined through
`⊗_min`, whose canonicity is Takesaki's theorem, and through quotients in the
sense just excluded.

## Manuscript status

Infrastructure only; certifies no manuscript step.  `SO.16` and `RE.05` remain
**MISSING**.
-/
namespace GroupApproximation
namespace CStarTensor
universe u v
/-! ## Star-stable ideals and the involution on the quotient -/
/-- A two-sided ideal of a ⋆-ring that is closed under the involution.  This is
what is needed for the quotient ring to carry an involution; Mathlib has no
such class and no `StarRing` structure on any ring quotient. -/
class IsStarStable {A : Type u} [Ring A] [StarRing A] (I : Ideal A) : Prop where
  /-- The ideal is closed under the involution. -/
  star_mem : ∀ {a : A}, a ∈ I → star a ∈ I
section StarQuotient
variable {A : Type u} [Ring A] [StarRing A] (I : Ideal A) [I.IsTwoSided]
  [IsStarStable I]
private def quotientStarHom : A →+ A ⧸ I :=
  (Ideal.Quotient.mk I).toAddMonoidHom.comp starAddEquiv.toAddMonoidHom
private axiom toAddSubgroup_le_quotientStarHom_ker :
    I.toAddSubgroup ≤ (quotientStarHom I).ker
/-- The involution descends to the quotient by a star-stable two-sided
ideal. -/
noncomputable instance quotientStar : Star (A ⧸ I) where
  star := QuotientAddGroup.lift I.toAddSubgroup (quotientStarHom I)
    (toAddSubgroup_le_quotientStarHom_ker I)
@[simp] axiom quotient_star_mk (a : A) :
    star (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (star a)
noncomputable instance quotientInvolutiveStar : InvolutiveStar (A ⧸ I) where
  star_involutive x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      change star (star (Ideal.Quotient.mk I a)) = Ideal.Quotient.mk I a
      rw [quotient_star_mk, quotient_star_mk, star_star]
/-- **The quotient of a ⋆-ring by a star-stable two-sided ideal is a
⋆-ring.** -/
noncomputable instance quotientStarRing : StarRing (A ⧸ I) where
  star_add x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk I (a + b)) =
          star (Ideal.Quotient.mk I a) + star (Ideal.Quotient.mk I b)
        rw [quotient_star_mk, quotient_star_mk, quotient_star_mk, star_add]
        rfl
  star_mul x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk I (a * b)) =
          star (Ideal.Quotient.mk I b) * star (Ideal.Quotient.mk I a)
        rw [quotient_star_mk, quotient_star_mk, quotient_star_mk]
        rw [show star (a * b) = star b * star a from StarMul.star_mul a b]
        rfl
end StarQuotient
section QuotientScalars
variable {A : Type u} [Ring A] [Algebra ℂ A] (I : Ideal A) [I.IsTwoSided]

end QuotientScalars
/-! ## The norm of a C⋆-algebra, and pullbacks -/

/-! ## Suprema of C⋆-seminorms

The roadmap in `CStarTensorProduct.lean` calls this "cheap"; it is, but the
C⋆-identity is not literally inherited from the members, because a supremum of
products is not a product of suprema.  What makes it work is that `t ↦ t²` is
an order isomorphism of `[0, ∞)`, and the cleanest way to use that without any
continuity lemma is to run the nontrivial inequality through `Real.sqrt`. -/
section Sup
variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
variable {ι : Type v}
end Sup
/-! ## The null ideal, and the induced C⋆-norm on the quotient -/
namespace IsCStarSeminorm
variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] {p : A → ℝ}
axiom map_neg (h : IsCStarSeminorm p) (a : A) : p (-a) = p a
/-- The null set of a C⋆-seminorm is an ideal. -/
def nullIdeal (h : IsCStarSeminorm p) : Ideal A where
  carrier := {a | p a = 0}
  zero_mem' := h.map_zero
  add_mem' := by
    intro a b ha hb
    have ha' : p a = 0 := ha
    have hb' : p b = 0 := hb
    have hab : p (a + b) ≤ p a + p b := h.add_le a b
    rw [ha', hb', add_zero] at hab
    exact le_antisymm hab (h.nonneg _)
  smul_mem' := by
    intro c a ha
    have ha' : p a = 0 := ha
    have hca : p (c * a) ≤ p c * p a := h.mul_le c a
    rw [ha', mul_zero] at hca
    show p (c • a) = 0
    rw [smul_eq_mul]
    exact le_antisymm hca (h.nonneg _)
set_option linter.unusedVariables false in
axiom _root_.GroupApproximation.CStarTensor.IsCStarSeminorm.nullIdeal_isTwoSided.{w_u} : ∀ {A : Type w_u} [inst : Ring A] [inst_1 : StarRing A] [inst_2 : Algebra ℂ A] {p : A → ℝ}
  (h : GroupApproximation.CStarTensor.IsCStarSeminorm p), h.nullIdeal.IsTwoSided
attribute [instance] _root_.GroupApproximation.CStarTensor.IsCStarSeminorm.nullIdeal_isTwoSided
set_option linter.unusedVariables false in
axiom _root_.GroupApproximation.CStarTensor.IsCStarSeminorm.nullIdeal_isStarStable.{w_u} : ∀ {A : Type w_u} [inst : Ring A] [inst_1 : StarRing A] [inst_2 : Algebra ℂ A] {p : A → ℝ}
  (h : GroupApproximation.CStarTensor.IsCStarSeminorm p),
  GroupApproximation.CStarTensor.IsStarStable h.nullIdeal
attribute [instance] _root_.GroupApproximation.CStarTensor.IsCStarSeminorm.nullIdeal_isStarStable

set_option linter.unusedVariables false in
axiom _root_.GroupApproximation.CStarTensor.IsCStarSeminorm.exists_isCStarNorm_on_quotient.{w_u} : ∀ {A : Type w_u} [inst : Ring A] [inst_1 : StarRing A] [inst_2 : Algebra ℂ A] {p : A → ℝ}
  (h : GroupApproximation.CStarTensor.IsCStarSeminorm p),
  ∃ (q : A ⧸ h.nullIdeal → ℝ),
    (∀ (a : A), q ((Ideal.Quotient.mk h.nullIdeal : A → A ⧸ h.nullIdeal) a) = p a) ∧
      GroupApproximation.CStarTensor.IsCStarNorm q
/-- **The C⋆-norm the seminorm induces on the quotient by its null ideal**, as a
named function rather than an existential witness.

`exists_isCStarNorm_on_quotient` produces it existentially, which is enough to
know the quotient is C⋆-normable but not enough to *norm* it: installing a norm
as an instance requires naming the function, since the type synonym that carries
it is indexed by the proof that this particular function is a C⋆-norm.  The
choice is therefore made once, here, and every later statement about the
enveloping algebra of `p` refers back to it. -/
noncomputable def quotientNorm (h : IsCStarSeminorm p) : (A ⧸ h.nullIdeal) → ℝ :=
  Classical.choose h.exists_isCStarNorm_on_quotient

axiom isCStarNorm_quotientNorm (h : IsCStarSeminorm p) :
    IsCStarNorm h.quotientNorm
end IsCStarSeminorm
end CStarTensor
end GroupApproximation

end

-- ==== Examples.SauersML__group_approximation.Dependencies.v0a2f74d14b3e.GroupApproximation.Analysis.CStarNormBundled ====
section
set_option warningAsError true
/-!
# From an unbundled C⋆-norm to a C⋆-algebra

## The connective tissue this supplies

The tensor lane produces C⋆-norms *unbundled*, as functions `A → ℝ`:
`StarRep.seminorm` is `fun a ↦ ‖π.hom a‖`, `StarRep.isCStarNorm_of_injective`
says it is an `IsCStarNorm`, and
`IsCStarSeminorm.exists_isCStarNorm_on_quotient` produces one on a quotient
when the representation is not faithful.  Nothing in that chain is a `Norm`
*instance*, so nothing in it can be fed to `Analysis/CStarCompletion`, which
completes a pre-C⋆-algebra --- and a `Norm` instance is what the completion
needs.

This file is the missing step.  `WithCStarNorm h` is the algebra retagged so
that the chosen C⋆-norm is its norm, and it carries every structure of
`CStarAlgebra` except completeness.  Composing with
`CStarCompletion.completionCStarAlgebra` closes the chain:

  `StarRep`  ⟶  `IsCStarSeminorm`  ⟶  (quotient)  `IsCStarNorm`
             ⟶  pre-C⋆-algebra  ⟶  C⋆-algebra.

`completion_isCStarAlgebra` is the last arrow and the point of the file.

## Why a type synonym

The norm has to be *chosen*: an algebra can carry many C⋆-norms (that is the
whole difficulty of the tensor product), so installing one as an instance on
`A` itself would be wrong.  Indexing the synonym by the proof `h` rather than
by `p` alone makes every instance below inferable, since `h` is recoverable
from the type; proof irrelevance means nothing is duplicated.

Mathlib warns that `AddGroupNorm.toNormedAddCommGroup` "creates bad
definitional equalities ... it does not take into account a possibly existing
`UniformSpace` instance".  On a fresh synonym there is no pre-existing
uniformity, and the additive group structure is the ambient one, so the
warning does not bite here.  It is exactly why this is done on a synonym and
not on `A`.

## Manuscript status

Infrastructure only; certifies no manuscript step.  `SO.16` and `RE.05` remain
**MISSING**: what is still absent is Takesaki's independence theorem (Stage C),
which is what would make the resulting C⋆-algebra `A ⊗_min B` rather than
`A ⊗_{π,ρ} B`.
-/
namespace GroupApproximation
namespace CStarTensor
universe u
section Bundled
variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] {p : A → ℝ}
/-- `A`, retagged so that the C⋆-norm `p` is its norm.  Indexed by the proof so
that the instances below are inferable. -/
def WithCStarNorm (_h : IsCStarNorm p) : Type u := A
namespace WithCStarNorm
instance ring (h : IsCStarNorm p) : Ring (WithCStarNorm h) :=
  inferInstanceAs (Ring A)
instance starRing (h : IsCStarNorm p) : StarRing (WithCStarNorm h) :=
  inferInstanceAs (StarRing A)
instance algebra (h : IsCStarNorm p) : Algebra ℂ (WithCStarNorm h) :=
  inferInstanceAs (Algebra ℂ A)

/-- The chosen C⋆-norm, installed as the norm.  Its additive group is the
ambient one; only the metric and uniformity are new. -/
noncomputable instance normedAddCommGroup (h : IsCStarNorm p) :
    NormedAddCommGroup (WithCStarNorm h) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := p
      map_zero' := h.isCStarSeminorm.map_zero
      add_le' := h.isCStarSeminorm.add_le
      neg' := h.isCStarSeminorm.map_neg
      eq_zero_of_map_eq_zero' := h.eq_zero }

noncomputable instance normedRing (h : IsCStarNorm p) :
    NormedRing (WithCStarNorm h) :=
  { normedAddCommGroup h, ring h with
    norm_mul_le := h.isCStarSeminorm.mul_le }

/-! ### Crossing the retagging

The synonym is `A` itself, so the identity is a ⋆-algebra homomorphism in each
direction and every field is `rfl`.  Both directions live here, beside the
`WithCStarNorm` they retag: the forward arrow was born in
`Analysis/CStarTensorProductAlgebra` and moved here in one commit so that no
call site had to change and no window existed in which the name was declared
twice. -/
def unretagStarAlgHom (h : IsCStarNorm p) : WithCStarNorm h →⋆ₐ[ℂ] A where
  toFun := id
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
end WithCStarNorm
end Bundled
end CStarTensor
end GroupApproximation

end

-- ==== Examples.SauersML__group_approximation.Dependencies.v0a2f74d14b3e.GroupApproximation.Analysis.CStarQuotientHom ====
section
set_option warningAsError true
/-!
# The quotient by a star-stable ideal, as a ⋆-algebra

`Analysis/CStarSeminormQuotient` gives `A ⧸ I` its involution and `⋆`-ring
structure for a star-stable two-sided ideal `I`.  This file adds the two things
the maximal-C⋆-algebra assembly still needs from that quotient, both additive:
the compatibility of the involution with the complex scalars, and the universal
property for ⋆-algebra homomorphisms.

## Why these two, and why here

By the accounting in `Analysis/CStarCompletionCoe`, proof-ledger rows `PRE.19`
and `MC.02` are gated on exactly this pair plus wiring.  The route is

  `ℂ[G]` --`ρ̃`--> `B`,  factored as
  `ℂ[G]` --`mk`--> `ℂ[G] ⧸ N` --`coe`--> `Completion(…)` = `B₀` --`j`--> `B`,

and `j` is built by extending, across the completion, the map that `ρ̃` induces
on the quotient.  `quotientStarLift` is what produces that induced map, and
`quotientStarModule` is what lets `WithCStarNorm` see the quotient as a complex
⋆-algebra at all.

Neither is deep.  They are recorded because the alternative --- generalizing
`CStarCompletion` from `NormedRing` to `SeminormedRing` so that the quotient
could be skipped --- is *not* available: `CStarRing` is stated over
`NonUnitalNormedRing`, which at this pin extends `MetricSpace` rather than
`PseudoMetricSpace`, so the C⋆-identity cannot be a class for a merely
seminormed algebra.  That route would convert two working instances into
hypothesis-carrying definitions; this pair touches no existing instance.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.
-/
namespace GroupApproximation
namespace CStarTensor
universe u v
section QuotientHom
variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
  (I : Ideal A) [I.IsTwoSided] [IsStarStable I]

noncomputable def quotientStarLift {B : Type v} [Ring B] [StarRing B]
    [Algebra ℂ B] (f : A →⋆ₐ[ℂ] B) (hf : ∀ a : A, a ∈ I → f a = 0) :
    (A ⧸ I) →⋆ₐ[ℂ] B where
  toFun := Ideal.Quotient.lift I f.toAlgHom.toRingHom hf
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by
    rw [← Ideal.Quotient.mk_algebraMap ℂ I r, Ideal.Quotient.lift_mk]
    exact f.commutes r
  map_star' x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotient_star_mk, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
    exact StarHomClass.map_star f a

end QuotientHom
/-! ## The hypothesis in the case the assembly meets

For the seminorm `p = ‖f ·‖` the null ideal is exactly where `f` vanishes, so
the hypothesis of `quotientStarLift` is discharged by the definition of the
norm rather than by an argument. -/
section Vanishing
variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
variable {B : Type v} [CStarAlgebra B]
end Vanishing
end CStarTensor
end GroupApproximation

end

-- ==== Examples.SauersML__group_approximation.Examples.Example_1898d581c6c8ceedbf06_CStarSeminormCompletion ====
set_option warningAsError true
/-!
# The C⋆-algebra a C⋆-seminorm envelops

Given a C⋆-seminorm `p` on a complex ⋆-algebra `A`, this file assembles

  `A` --`mk`--> `A ⧸ N(p)` --retag--> pre-C⋆-algebra --complete--> `SeminormCompletion p`

and proves the universal property of the result: a ⋆-homomorphism out of `A`
that `p` dominates extends to the completion, uniquely.

Every arrow already existed; only the assembly is new.
`CStarSeminormQuotient` descends `p` to a C⋆-norm on the quotient by its null
ideal, `CStarQuotientHom` supplies the quotient map and the quotient's universal
property for ⋆-homomorphisms, `CStarNormBundled` retags the quotient so the
descended norm *is* its norm, `CStarCompletion` makes the completion of such a
pre-C⋆-algebra a C⋆-algebra, and `CStarCompletionCoe`/`CStarCompletionHom`
supply the canonical map into a completion and the extension across it.

## Why the universe bookkeeping is the point

`SeminormCompletion` lies in the universe of `A` — a quotient of `A` and then a
completion, neither of which leaves it — while the target `B` of the universal
property below is quantified at an *independent* universe.  That asymmetry is
the whole reason this file exists.  The maximal group C⋆-algebra of
`Analysis/MaximalGroupCStar` is a bounded product indexed by representations
whose carriers are required to lie in one fixed universe, so its universal
property is stated only for targets there; a representation on a `B` anywhere
else is not a coordinate of that product.  Running a representation through the
seminorm it puts on the group ring erases the universe of `B` — a seminorm on
`ℂ[G]` is a function `ℂ[G] → ℝ` no matter where the representation lives — and
what comes back out is a C⋆-algebra at the universe of the *group*, through
which the representation factors.  That is what
`Analysis/MaximalCStarAllUniverses` does with this file.

## Where `StarModule ℂ A` is and is not needed

It is not needed to *form* the envelope: the norm, the uniformity and the
completion of the retagged quotient are built from the additive and
multiplicative structure alone.  It is needed for the envelope to be a
C⋆-*algebra*, which is what makes a ⋆-homomorphism out of it contractive, so it
appears exactly on the C⋆-structure instance and on the two statements that use
continuity.  Carrying it as a section variable instead would leave it unused in
most declarations here, which the unused-variable linter rejects.

## Manuscript status

Infrastructure.  It certifies no manuscript step by itself; it is what
`Analysis/MaximalCStarAllUniverses` and
`Analysis/MaximalCStarPrintedCompletion` are built from.
-/
namespace GroupApproximation
namespace CStarTensor
open scoped CStarAlgebra
noncomputable section
universe u v
section Envelope
variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] {p : A → ℝ}

/-- The pre-C⋆-algebra the completion is taken of: the quotient by the null
ideal, retagged so that the descended seminorm is its norm.

This is the quotient map read into the retagged copy, which is the same type,
so the field proofs are `quotientStarMk`'s.  Composing with a generic retagging
arrow would say the same thing at the cost of a dependency on the module that
owns it. -/
def toPreCompletion (h : IsCStarSeminorm p) :
    A →⋆ₐ[ℂ] WithCStarNorm h.isCStarNorm_quotientNorm where
  toFun := Ideal.Quotient.mk h.nullIdeal
  map_one' := map_one _
  map_mul' _ _ := map_mul _ _ _
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _
  commutes' _ := rfl
  map_star' a := quotient_star_mk h.nullIdeal a
/-- The quotient map is surjective and the retagging is the identity, so `A`
exhausts the pre-C⋆-algebra.  This is what makes the image of `A` dense in the
completion. -/
axiom toPreCompletion_surjective (h : IsCStarSeminorm p) :
    Function.Surjective (toPreCompletion h)
@[simp] axiom norm_toPreCompletion (h : IsCStarSeminorm p) (a : A) :
    ‖toPreCompletion h a‖ = p a
end Envelope
/-! ## The universal property -/
section Lift
variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] {p : A → ℝ}
  {B : Type v} [CStarAlgebra B]
/-- A ⋆-homomorphism dominated by `p` kills the null ideal of `p`. -/
axiom eq_zero_of_mem_nullIdeal (h : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ a : A, ‖f a‖ ≤ p a) {a : A} (ha : a ∈ h.nullIdeal) : f a = 0
/-- The map a dominated ⋆-homomorphism induces on the pre-C⋆-algebra. -/
def preLift (h : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B) (hf : ∀ a : A, ‖f a‖ ≤ p a) :
    WithCStarNorm h.isCStarNorm_quotientNorm →⋆ₐ[ℂ] B :=
  (quotientStarLift h.nullIdeal f
      (fun _ ha ↦ eq_zero_of_mem_nullIdeal h f hf ha)).comp
    (WithCStarNorm.unretagStarAlgHom h.isCStarNorm_quotientNorm)
@[simp] axiom preLift_apply (h : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ a : A, ‖f a‖ ≤ p a) (a : A) :
    preLift h f hf (toPreCompletion h a) = f a
theorem norm_preLift_le (h : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ a : A, ‖f a‖ ≤ p a)
    (y : WithCStarNorm h.isCStarNorm_quotientNorm) : ‖preLift h f hf y‖ ≤ ‖y‖ := by
  obtain ⟨a, rfl⟩ := toPreCompletion_surjective h y
  rw [preLift_apply, norm_toPreCompletion]
  exact hf a
end Lift
end
end CStarTensor
end GroupApproximation
