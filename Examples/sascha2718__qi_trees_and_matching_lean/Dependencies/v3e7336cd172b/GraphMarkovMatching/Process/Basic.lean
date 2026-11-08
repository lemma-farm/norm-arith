module
/-
Abstract Markov label systems: a state space `S` with a child kernel `P : S → PMF (S × S)`, the height-`n` tree law `muM`
started from a frozen root state, and the pair mixture `pairMix` that the
recursion consumes.

Design notes:

* Labellings reuse `FullLab` from the `Support` support layer; the state at a
  vertex is
  its label, so the root state of a sample is `rootLab`.
* `FullLab S 0` and `FullLab S (n+1)` unfold definitionally to `S` and to a
  product, and elaboration happily mixes the unfolded and folded types, which
  then defeats `rw`'s syntactic matching. All constructions therefore go
  through the explicitly typed wrappers `leaf` and `branch`, keeping every
  term uniformly at the `FullLab` type.
* `muM P s (n+1)` is *defined* as the pushforward of `pairMix P s n` under
  `branch s`, so the measure recursion is definitional.
* The change-of-variable helpers `tsum_bind_mul` / `tsum_map_mul` are the
  only measure-theoretic moves the potential layer needs: everything is a
  `tsum` in `ℝ≥0∞` and is unconditionally covered by Fubini's theorem as in
  the support layer.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Support.Tree
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
@[expose] public section
namespace GraphMarkovMatching
open GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {S : Type u}
/-! ### Change of variables for `tsum` against `bind` and `map` -/
variable (P : S → PMF (S × S))
end GraphMarkovMatching
