module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Set.Basic
@[expose] public section
/-!
# Configuration space and particle permutations

The configuration space of `n` planar particles is `Fin n → ℂ`.  This file
defines particle relabelling, symmetric and alternating observables, and the
collision locus.  It contains no measure-theoretic or analytic input.
-/
namespace GinibrePoincare
/-- The configuration space of `n` labelled particles in the complex plane. -/
abbrev Configuration (n : ℕ) := Fin n → ℂ
/-- The symmetric group acting on `n` labelled particles. -/
abbrev ParticlePermutation (n : ℕ) := Equiv.Perm (Fin n)
/-- Relabelling of a configuration by a permutation. -/
def permute {n : ℕ} (σ : ParticlePermutation n) (z : Configuration n) :
    Configuration n :=
  fun i => z (σ i)
def IsSymmetric {n : ℕ} {α : Type*} (f : Configuration n → α) : Prop :=
  ∀ (σ : ParticlePermutation n) (z : Configuration n),
    f (permute σ z) = f z
/-- The complex scalar corresponding to the sign of a permutation. -/
def permutationSign {n : ℕ} (σ : ParticlePermutation n) : ℂ :=
  ((↑(Equiv.Perm.sign σ) : ℤ) : ℂ)
def CollisionFree {n : ℕ} (z : Configuration n) : Prop :=
  Function.Injective z
end GinibrePoincare
