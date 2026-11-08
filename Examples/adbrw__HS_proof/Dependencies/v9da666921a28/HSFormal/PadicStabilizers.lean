module
public import Examples.adbrw__HS_proof.Dependencies.v9da666921a28.HSFormal.PadicSubgroups
@[expose] public section
/-!
# Stabilizers of points moved by a p-adic tail

Power subgroups of `ℤ_[p]` are ordered by reversed exponents. Together with the
closed-subgroup classification, this shows that a closed subgroup that does not
contain `p^j ℤ_[p]` lies in `p^(j+1) ℤ_[p]`.

For a continuous action on a Hausdorff space, point stabilizers are closed.
Consequently, a point outside the fixed-point set of the `j`th tail has its
stabilizer inside the next tail. This conclusion uses actual nonfixedness of
the point; it does not assert existence of such points or exclude faithful
p-adic actions on manifolds.
-/
namespace HSFormal
open Topology
section SubgroupOrder
variable {p : ℕ} [Fact p.Prime]
end SubgroupOrder
section Stabilizers
variable {p : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
  [T2Space X] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X]
end Stabilizers
end HSFormal
