module
public import Examples.adbrw__HS_proof.Dependencies.v9da666921a28.HSFormal.PadicStabilizers
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
@[expose] public section
/-!
# Section 7, first step: a free point of an effective p-adic action

`HSFormal.PointwisePeriodicIsPeriodic` is the published input [Rob75, Theorem 2] in the only case
used by the manuscript (L37, L458): the discrete group `ℤ`, i.e. Montgomery's theorem on pointwise
periodic homeomorphisms. It is an explicit hypothesis, never an axiom.

`HSFormal.exists_stabilizer_eq_bot` is the free-point claim of L458: an effective continuous
`ℤ_[p]`-action on a connected manifold without boundary has a point with trivial stabilizer.
-/
namespace HSFormal
/-- **[Mon37] = [Rob75, Theorem 2] for `Γ = ℤ`** (L37, L458).
D. Montgomery, *Pointwise periodic homeomorphisms*, Amer. J. Math. 59 (1937), 118–120: a
homeomorphism of a connected manifold without boundary all of whose points are periodic is
periodic. J. W. Roberts, *Pointwise finite families of mappings*, Canad. Math. Bull. 18 (1975),
Theorem 2, is the same statement for transformation groups with finite orbits (finite image
modulo the global kernel); for `ℤ` acting through `f` this is exactly the periodicity of `f`.
Manifolds are Hausdorff, second countable, connected, topological (no smoothness), without
boundary, of some dimension `n` (the case `n = 0` is trivial). -/
def PointwisePeriodicIsPeriodic : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M] (f : M ≃ₜ M),
    (∀ x, ∃ k, 0 < k ∧ f^[k] x = x) → ∃ m, 0 < m ∧ ∀ x, f^[m] x = x
variable {p : ℕ} [Fact p.Prime] {X : Type*} [AddAction ℤ_[p] X]
end HSFormal
