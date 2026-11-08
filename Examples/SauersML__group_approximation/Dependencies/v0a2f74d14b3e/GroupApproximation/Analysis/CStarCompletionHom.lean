import Examples.SauersML__group_approximation.Dependencies.v0a2f74d14b3e.GroupApproximation.Analysis.CStarCompletion
set_option warningAsError true
/-!
# Extending a ⋆-homomorphism along the completion

`Analysis/CStarCompletion` makes `Completion A` a C⋆-algebra when `A` is a
pre-C⋆-algebra.  This file supplies the other half of the universal property
of that completion: a ⋆-homomorphism out of `A` into a C⋆-algebra extends to
the completion, uniquely, as a ⋆-homomorphism.

## Why this is needed and what it is for

It is step (iii) of the route to the universal property of `Cmax(G)` for a
target in an arbitrary universe (proof-ledger rows `PRE.19` and `MC.02`).
`Analysis/MaximalCStarAnyUniverse.maximalGroupCStar_existsUnique_lift_of_factors`
reduces that row to producing, for `ρ : G → U(B)` with `B` in any universe, a
C⋆-algebra `B₀` **at the universe of `G`** together with `ρ₀ : G → U(B₀)` and
a unital ⋆-homomorphism `j : B₀ → B` with `j ∘ ρ₀ = ρ`.  The only construction
of such a `B₀` that stays at the universe of `G` is a completion, so `j` is
necessarily an extension along a completion --- which is exactly
`extendStarAlgHom` below.

Mathlib has `UniformSpace.Completion.extensionHom`, which extends a *ring*
homomorphism.  It does not extend the scalars or the involution, and a
`→⋆ₐ[ℂ]` is what the factoring datum requires.

## The uniform-continuity hypothesis, and why it costs nothing here

`extendStarAlgHom` takes `UniformContinuous f` as a hypothesis rather than
deriving it.  A ⋆-homomorphism from a *Banach* ⋆-algebra to a C⋆-algebra is
automatically contractive, but `A` here is exactly the case that is **not**
complete, so that theorem does not apply and assuming continuity would be
circular.  In the intended application the map is isometric by construction
--- the norm on `A` is *defined* as `‖ρ̃(·)‖_B` --- so
`uniformContinuous_of_norm_map` below discharges the hypothesis outright, and
nothing is left conditional.

## Contents

* `uniformContinuous_of_norm_map` --- a norm-preserving additive map is
  uniformly continuous.
* `extendStarAlgHom` --- the extension, as a `Completion A →⋆ₐ[ℂ] B`, with
  `extendStarAlgHom_coe` computing it on the dense image.
* `extendStarAlgHom_unique` --- uniqueness among *continuous* extensions,
  which is the form density gives.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `PRE.19`/`MC.02`
still need the involution on the group algebra `ℂ[G]`, which Mathlib does not
have at the pinned revision (there is no `star` anywhere under
`Mathlib/Algebra/MonoidAlgebra/`), and the assembly on top of it.
-/
namespace GroupApproximation
namespace CStarCompletion
open UniformSpace UniformSpace.Completion
/-! ### Uniform continuity from norm preservation

Stated in its own section, carrying only the instances it uses: a
⋆-homomorphism needs `Star` and `Algebra` on the source but neither
`NormedStarGroup` nor `StarModule`, so including those here would leave
section variables unused. -/
section Isometric
variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
variable {B : Type*} [CStarAlgebra B]
end Isometric
section Extend
-- `StarModule ℂ A` is deliberately absent: the completion's `Algebra ℂ`
-- instance is built by density from the module laws and never touches `star`,
-- and a `→⋆ₐ[ℂ]` needs only `Algebra` and `Star` on each side.  Including it
-- would leave it unused in `extendStarAlgHom_coe`.
variable {A : Type*} [NormedRing A] [StarRing A] [NormedStarGroup A]
  [NormedAlgebra ℂ A]
variable {B : Type*} [CStarAlgebra B]
end Extend
end CStarCompletion
end GroupApproximation
