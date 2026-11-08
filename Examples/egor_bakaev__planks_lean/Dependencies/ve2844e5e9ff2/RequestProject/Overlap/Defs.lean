module
public import Examples.egor_bakaev__planks_lean.Dependencies.ve2844e5e9ff2.RequestProject.Overlap.Basic
public import Mathlib
/-!
# Definitions for pruning and dense overlap

Deep and central planks, candidate and removable pairs, final pruning families, the final
hole, and `δ`-dense disks with the dense region `U_δ`.  All notions are computed from a
fixed indexed base family `P : ι → Plank`.

Compared with the notes, the hull used in the removability condition is the convex hull
`K₀ = conv(J_P ∪ J_Q)` of the two chords `J_P = ℓ_P ∩ ρD`, `J_Q = ℓ_Q ∩ ρD`
(rather than the convex hull of the plank pieces).  Both the pruning theorem and the price
estimate for removable pairs go through with this choice.
-/
@[expose] public section
open MeasureTheory Set Metric Real
open scoped ENNReal
noncomputable section
namespace Annulus
section Family
variable {ι : Type*} [Fintype ι]
end Family
end Annulus
end
