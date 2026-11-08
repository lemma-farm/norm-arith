module
/-
The matching relation over the full automorphism group: `fullSim R₀ n` is
matchability of two labellings of `𝔹_n` by some rooted automorphism. The
group is `AutK 1` of the `Support` support layer: at `k = 1` every
vertex carries a swap bit, which is the full group, and the recursion

    fullSim (n+1) = R₀ ⊗ (fullSim n)^(2)

is the `k = 1` swap-phase recursion. This file restates the recursion through
the typed wrappers `leaf`/`branch` (pointwise, as an `Iff`), and proves that
matching forces root compatibility, the fact behind the kernel-mismatch layer.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v1728b582a71a.GraphMarkovMatching.Process.Basic
@[expose] public section
namespace GraphMarkovMatching
open GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {S : Type u}
end GraphMarkovMatching
