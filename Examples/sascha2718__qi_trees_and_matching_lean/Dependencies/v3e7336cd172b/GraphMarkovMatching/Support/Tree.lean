module
/-
The `G_k` tree layer: full labellings of `𝔹_n`, the restricted automorphism
group, and the phase recursions.

Indexing convention: `m` is the *swap distance* of the root, the number of
levels down to the next admissible swap level. `m = 0` means the root itself
carries a swap (phase `j = k-1`); its children restart at distance
`k-1`. For `m+1` the root has no swap and the children are at distance `m`.
The matching theorems root the tree at distance `k-1` (levels `≡ k-1 (mod k)`
are admissible, so the root at level `0` is `k-1` levels above the first).
At `k = 1` every vertex has `m = 0` and the group is the full automorphism
group, the case the Markov layer consumes.

Phase-dependent labels: the label law at a vertex of swap distance `m` is
`ν m`, for a given family `ν : ℕ → PMF V` (the applications use `ν` constant
on `{0,…,k-1}`-classes; only the values `m ≤ k-1` ever occur).

The recursions proved here:

    ≈(m,0)    = R₀
    ≈(0,n+1)  = R₀ ⊗ (≈(k-1,n))^(2)     (swap phase: symmetrised square)
    ≈(m+1,n+1)= R₀ ⊗ (≈(m,n) ⊗ ≈(m,n))  (product phase: no choice)

together with reflexivity/symmetry propagation and the product-measure
recursions, all definitional or by the `SquareRel`/`ProdRel` lemmas.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Support.Square
@[expose] public section
namespace GraphMarkovMatching.Support
open scoped ENNReal Classical
universe u
variable {V : Type u}
/-! ### Full labellings -/
def AutK (k : ℕ) : ℕ → ℕ → Type
  | _, 0 => Unit
  | 0, n + 1 => Bool × AutK k (k - 1) n × AutK k (k - 1) n
  | m + 1, n + 1 => AutK k m n × AutK k m n
example : AutK 2 0 1 = (Bool × AutK 2 1 0 × AutK 2 1 0) := rfl
example : AutK 2 1 1 = (AutK 2 0 0 × AutK 2 0 0) := rfl
/-- `AutK` is finite at every level (needed for the König step). -/
instance autK_finite (k : ℕ) : ∀ m n, Finite (AutK k m n)
  | _, 0 => by unfold AutK; infer_instance
  | 0, n + 1 => by
      have := autK_finite k (k - 1) n
      unfold AutK; infer_instance
  | m + 1, n + 1 => by
      have := autK_finite k m n
      unfold AutK; infer_instance
/-- `AutK` is nonempty at every level (the identity). -/
instance autK_nonempty (k : ℕ) : ∀ m n, Nonempty (AutK k m n)
  | _, 0 => ⟨()⟩
  | 0, n + 1 => by
      have h := autK_nonempty k (k - 1) n
      exact ⟨(false, h.some, h.some)⟩
  | m + 1, n + 1 => by
      have h := autK_nonempty k m n
      exact ⟨(h.some, h.some)⟩
/-! ### Matching under a restricted automorphism -/
end GraphMarkovMatching.Support
