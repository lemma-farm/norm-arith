/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module
public import Examples.willmfeldman__one_phase_critical_dim.Dependencies.ved80ba4ba870.OnePhaseDimension.Certificate.Ops
public import Examples.willmfeldman__one_phase_critical_dim.Dependencies.ved80ba4ba870.OnePhaseDimension.Certificate.Bounds.Contraction
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The connected components of scalar graphs with cubic vertices

After the edges between vectors are split off, a scalar graph retained by the closure lemma
(at most two copies of `X`, every copy with three incidences) is a product of connected
components of the following seven shapes, where a *leaf* is a copy of `p` or `ℓ`:

* `c100`: one `X`, three leaves;
* `c110`: one `X` with a self-edge and one leaf;
* `c201`, `c202`, `c203`: two copies joined by `r = 1, 2, 3` edges, the other slots at leaves;
* `c211`: two copies joined by one edge, the first with a self-edge, the second with two
  leaves;
* `c221`: two copies joined by one edge, each with a self-edge.

For each shape we compute the value of the graph key (`Comp.eval_eq`) and prove the bound
`(value)² ≤ L² ∏ |leaf|² |X|^{2·#X}` (`Comp.eval_sq_le`), with `L²` given by the product rule of
the 2026-09-24 version (section "Bounds for scalar graphs"): `θ^k` for an edge of power `k`
between distinct vertices, `5/7` or `θ^{k-1}` for a self-edge of power `k = 1` or `k ≥ 2`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/
@[expose] public noncomputable section
namespace OnePhaseDimension.Certificate
open Matrix Finset
/-! ### Leaves -/
section Unfold
variable (d : CertData) (ι : ℕ → Fin 5) (F : XRecord → ℝ)
end Unfold
def selfFactor : ℕ → ℚ
  | 0 => 0
  | 1 => 5 / 7
  | k + 2 => (4 / 5) ^ (k + 1)
theorem selfFactor_nonneg (k : ℕ) : 0 ≤ selfFactor k := by
  rcases k with _ | _ | k <;> simp only [selfFactor] <;> positivity
inductive Comp where
  /-- One `X`, three leaves. -/
  | c100 (u₁ : Endpoint) (k₁ : ℕ) (u₂ : Endpoint) (k₂ : ℕ) (u₃ : Endpoint) (k₃ : ℕ)
  /-- One `X` with a self-edge of power `s` and one leaf. -/
  | c110 (s : ℕ) (u : Endpoint) (k : ℕ)
  /-- Two copies joined by one edge of power `m`, two leaves at each. -/
  | c201 (m : ℕ) (u₁ : Endpoint) (k₁ : ℕ) (u₂ : Endpoint) (k₂ : ℕ) (v₁ : Endpoint) (l₁ : ℕ)
      (v₂ : Endpoint) (l₂ : ℕ)
  /-- Two copies joined by two edges, one leaf at each. -/
  | c202 (m₁ m₂ : ℕ) (u : Endpoint) (k : ℕ) (v : Endpoint) (l : ℕ)
  /-- Two copies joined by three edges. -/
  | c203 (m₁ m₂ m₃ : ℕ)
  /-- Two copies joined by one edge, a self-edge at the first, two leaves at the second. -/
  | c211 (s m : ℕ) (v₁ : Endpoint) (l₁ : ℕ) (v₂ : Endpoint) (l₂ : ℕ)
  /-- Two copies joined by one edge, each with a self-edge. -/
  | c221 (s₁ s₂ m : ℕ)
  deriving DecidableEq, Repr
namespace Comp
/-- The edges of a component, with copies `X₀` (and `X₁`). -/
def edges : Comp → List Edge
  | c100 u₁ k₁ u₂ k₂ u₃ k₃ => [⟨.x 0, u₁, k₁⟩, ⟨.x 0, u₂, k₂⟩, ⟨.x 0, u₃, k₃⟩]
  | c110 s u k => [⟨.x 0, .x 0, s⟩, ⟨.x 0, u, k⟩]
  | c201 m u₁ k₁ u₂ k₂ v₁ l₁ v₂ l₂ =>
    [⟨.x 0, .x 1, m⟩, ⟨.x 0, u₁, k₁⟩, ⟨.x 0, u₂, k₂⟩, ⟨.x 1, v₁, l₁⟩, ⟨.x 1, v₂, l₂⟩]
  | c202 m₁ m₂ u k v l => [⟨.x 0, .x 1, m₁⟩, ⟨.x 0, .x 1, m₂⟩, ⟨.x 0, u, k⟩, ⟨.x 1, v, l⟩]
  | c203 m₁ m₂ m₃ => [⟨.x 0, .x 1, m₁⟩, ⟨.x 0, .x 1, m₂⟩, ⟨.x 0, .x 1, m₃⟩]
  | c211 s m v₁ l₁ v₂ l₂ => [⟨.x 0, .x 0, s⟩, ⟨.x 0, .x 1, m⟩, ⟨.x 1, v₁, l₁⟩, ⟨.x 1, v₂, l₂⟩]
  | c221 s₁ s₂ m => [⟨.x 0, .x 0, s₁⟩, ⟨.x 1, .x 1, s₂⟩, ⟨.x 0, .x 1, m⟩]
def nX : Comp → ℕ
  | c100 .. | c110 .. => 1
  | _ => 2
end Comp
/-! ### Bounds for the component values

Each lemma bounds the nested sum produced by the edges of one component shape, for arbitrary
matrices with operator bounds and arbitrary leaf vectors. -/
section ShapeBounds
variable (X : Fin 5 → Fin 5 → Fin 5 → ℝ)
theorem sum_comm₃' (H : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ a, ∑ b, ∑ c, H a b c = ∑ c, ∑ a, ∑ b, H a b c :=
  (sum_comm₃ H).trans (sum_comm₃ fun b c a => H a b c)
theorem bound_c203 {M₁ M₂ M₃ : Matrix (Fin 5) (Fin 5) ℝ} {κ₁ κ₂ κ₃ : ℝ} (hM₁ : OpBound M₁ κ₁)
    (hM₂ : OpBound M₂ κ₂) (hM₃ : OpBound M₃ κ₃) (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) :
    (∑ a, ∑ b, M₁ a b * ∑ a', ∑ b', M₂ a' b' * ∑ a'', ∑ b'', M₃ a'' b'' *
      (X a a' a'' * X b b' b'')) ^ 2 ≤ κ₁ * κ₂ * κ₃ * sq3 X * sq3 X := by
  set W : Fin 5 → Fin 5 → Fin 5 → ℝ := fun a a' a'' =>
    ∑ b, M₁ a b * ∑ b', M₂ a' b' * ∑ b'', M₃ a'' b'' * X b b' b''
  have e : ∑ a, ∑ b, M₁ a b * ∑ a', ∑ b', M₂ a' b' * ∑ a'', ∑ b'', M₃ a'' b'' *
      (X a a' a'' * X b b' b'') = ∑ a, ∑ a', ∑ a'', X a a' a'' * W a a' a'' := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [W, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [sum_comm₃']
    exact Finset.sum_congr rfl fun a'' _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun b'' _ => by ring
  rw [e]
  have hW : sq3 W ≤ κ₁ * κ₂ * κ₃ * sq3 X := sq3_triOp_le hM₁ hM₂ hM₃ hκ₁ hκ₂ X
  calc _ ≤ sq3 X * sq3 W := sum3_mul_sq_le X W
    _ ≤ sq3 X * (κ₁ * κ₂ * κ₃ * sq3 X) := mul_le_mul_of_nonneg_left hW (sq3_nonneg X)
    _ = _ := by ring
end ShapeBounds
/-! ### Values and bounds of the components -/
/-- Nonnegativity of the factors in the component bounds. -/
local macro "bound_nonneg" : tactic =>
  `(tactic| first
    | positivity
    | exact sq1_nonneg _
    | exact sq3_nonneg _
    | exact_mod_cast selfFactor_nonneg _)
namespace Comp
end Comp
end OnePhaseDimension.Certificate
