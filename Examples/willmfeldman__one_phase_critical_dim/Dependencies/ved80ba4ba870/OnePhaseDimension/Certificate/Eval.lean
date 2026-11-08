/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module
public import Examples.willmfeldman__one_phase_critical_dim.Dependencies.ved80ba4ba870.OnePhaseDimension.Certificate.Graph
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Semantics of graph keys

`CertData` collects the data `A, p, ℓ, X, g, w, z` on `ℝ⁵`, and `CertData.Admissible` the
constraints under which the trace reductions hold: `A` symmetric and trace-free with
`tr A² = 1`, and `X` symmetric and trace-free.

`Key.eval k d ι` is the value of the monomial `k` at the data `d`, with free slot `i` set to
the coordinate index `ι i`. Each edge carries its own pair of summation indices for its two
endpoints; a `p` or `ℓ` endpoint contributes the corresponding coordinate, a free slot a
Kronecker delta, and the incidences at the copy `c` of `X` are collected in order of
occurrence and contribute one factor `X_{abc}`.

## Main results (keys without `X`)

* `Key.eval_eq_prod_of_hasX_eq_false`: the value factors over the edges.
* `Key.eval_canon_of_hasX_eq_false`: canonicalization is sound on admissible data.
* `Key.eval_mul_of_hasX_eq_false`: the tensor product evaluates to the product.

The general results (with copies of `X`) are in `OnePhaseDimension.Certificate.Ops`, built on
`evalEdgesWith` below.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/
@[expose] public section
namespace OnePhaseDimension.Certificate
open Finset
/-- The data on which graph keys are evaluated. -/
structure CertData where
  /-- The symmetric matrix. -/
  A : Matrix (Fin 5) (Fin 5) ℝ
  /-- The vector `p`. -/
  p : Fin 5 → ℝ
  /-- The vector `ℓ`. -/
  ell : Fin 5 → ℝ
  /-- The cubic tensor. -/
  X : Fin 5 → Fin 5 → Fin 5 → ℝ
  /-- The scalar `g`. -/
  g : ℝ
  /-- The scalar `w`. -/
  w : ℝ
  /-- The scalar `z`. -/
  z : ℝ
namespace CertData
/-- The constraint set: `A` symmetric, trace-free, with `tr A² = 1`, and `X` symmetric and
trace-free. -/
structure Admissible (d : CertData) : Prop where
  isSymm : d.A.IsSymm
  trace_eq_zero : d.A.trace = 0
  trace_sq_eq_one : (d.A ^ 2).trace = 1
  X_swap₁₂ : ∀ a b c, d.X a b c = d.X b a c
  X_swap₂₃ : ∀ a b c, d.X a b c = d.X a c b
  X_trace : ∀ c, ∑ a, d.X a a c = 0
/-- The weight of an endpoint carrying the coordinate index `a`: a coordinate of `p` or `ℓ`, a
Kronecker delta for a free slot (with slot assignment `ι`), and `1` at an `X` incidence. -/
def weight (d : CertData) (ι : ℕ → Fin 5) : Endpoint → Fin 5 → ℝ
  | .p, a => d.p a
  | .ell, a => d.ell a
  | .x _, _ => 1
  | .slot i, a => if a = ι i then 1 else 0
/-- The value of one copy of `X` from the list of indices at its incidences. -/
def xFactor (d : CertData) : List (Fin 5) → ℝ
  | [] => 1
  | [a, b, c] => d.X a b c
  | _ => 0
/-- A symmetric cubic tensor is invariant under cyclic permutation of its slots. -/
theorem Admissible.X_cycle {d : CertData} (hd : d.Admissible) (a b c : Fin 5) :
    d.X a b c = d.X c a b := by
  rw [hd.X_swap₁₂, hd.X_swap₂₃ b a c, hd.X_swap₁₂ b c a, hd.X_swap₂₃ c b a]
end CertData
/-- Record the index `a` at an endpoint: incidences at the copy `c` of `X` are appended to the
list of that copy. -/
def pushIdx (acc : ℕ → List (Fin 5)) : Endpoint → Fin 5 → ℕ → List (Fin 5)
  | .x c, a => Function.update acc c (acc c ++ [a])
  | _, _ => acc
/-- The internal sum over a list of edges. `acc` holds the indices already placed at the
incidences of each copy of `X`, and `nX` bounds the copies of `X`. -/
def evalEdges (d : CertData) (ι : ℕ → Fin 5) (nX : ℕ) :
    List Edge → (ℕ → List (Fin 5)) → ℝ
  | [], acc => ∏ c ∈ range nX, d.xFactor (acc c)
  | e :: es, acc => ∑ a, ∑ b, d.weight ι e.u a * d.weight ι e.v b * (d.A ^ e.pow) a b *
      evalEdges d ι nX es (pushIdx (pushIdx acc e.u a) e.v b)
namespace Key
/-- The scalar prefactor `g^h w^a z^b ∏ tr A^k` of a key. -/
def prefactor (k : Key) (d : CertData) : ℝ :=
  d.g ^ k.gPow * d.w ^ k.wPow * d.z ^ k.zPow * (k.traces.map fun t => (d.A ^ t).trace).prod
/-- The value of a key at the data `d`, with free slot `i` assigned the index `ι i`. -/
def eval (k : Key) (d : CertData) (ι : ℕ → Fin 5) : ℝ :=
  k.prefactor d * evalEdges d ι k.xBound k.edges fun _ => []
end Key
def Poly.eval (P : Poly) (d : CertData) (ι : ℕ → Fin 5) : ℝ :=
  (P.map fun t => (t.2 : ℝ) * (Key.unpack t.1).eval d ι).sum
/-! ### Keys without `X` -/
namespace Key
end Key
/-! ### Canonicalization -/
namespace Key
end Key
/-! ### The decoding examples of the paper

The three examples of the decimal encoding in the 2026-09-24 version:
`𝓜₀(200550) = g²|p|²`, `𝓜₄(000500520131)_{lijk} = p_l p_j A_{ik}` and
`𝓜₁(000771700)_l = q_l = X_{lij} A_{ij}`. -/
example (d : CertData) (ι : ℕ → Fin 5) :
    (decodeWord 0 (wordDigits 6 200550)).eval d ι = d.g ^ 2 * ∑ a, d.p a ^ 2 := by
  rw [show decodeWord 0 (wordDigits 6 200550) = ⟨0, 2, 0, 0, [], [⟨.p, .p, 0⟩]⟩ from rfl]
  simp [Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges, CertData.weight,
    Matrix.one_apply, sq]
example (d : CertData) (ι : ℕ → Fin 5) :
    (decodeWord 4 (wordDigits 12 500520131)).eval d ι =
      d.p (ι 0) * d.p (ι 2) * d.A (ι 1) (ι 3) := by
  rw [show decodeWord 4 (wordDigits 12 500520131) =
    ⟨4, 0, 0, 0, [], [⟨.p, .slot 0, 0⟩, ⟨.p, .slot 2, 0⟩, ⟨.slot 1, .slot 3, 1⟩]⟩ from rfl]
  simp [Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges, CertData.weight,
    Matrix.one_apply]
  ring
example (d : CertData) (hd : d.Admissible) (ι : ℕ → Fin 5) :
    (decodeWord 1 (wordDigits 9 771700)).eval d ι = ∑ i, ∑ j, d.X (ι 0) i j * d.A i j := by
  rw [show decodeWord 1 (wordDigits 9 771700) =
    ⟨1, 0, 0, 0, [], [⟨.x 0, .x 0, 1⟩, ⟨.x 0, .slot 0, 0⟩]⟩ from rfl]
  calc _ = ∑ i, ∑ j, d.A i j * d.X i j (ι 0) := by
        simp [Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges, CertData.weight,
          Matrix.one_apply, pushIdx, CertData.xFactor, Function.update_apply]
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [hd.X_cycle, mul_comm]
/-! ### Evaluation with a general final functional

`evalEdgesWith d ι F es acc` runs the nested sums over the index pairs of the edges `es`,
recording the indices at the copies of `X` in `acc`, and applies `F` to the final record.
`evalEdges` is the case where `F` is the product of the `X` factors over a range of copies. -/
/-- A record of the indices placed at the incidences of each copy of `X`. -/
abbrev XRecord := ℕ → List (Fin 5)
section EvalEdgesWith
variable (d : CertData) (ι : ℕ → Fin 5)
end EvalEdgesWith
/-! ### Invariance under reordering, using the symmetry of `X` -/
/-- Two records that agree up to reordering at each copy. -/
def XRecord.Equiv (acc acc' : XRecord) : Prop := ∀ c, (acc c).Perm (acc' c)
theorem XRecord.Equiv.pushIdx {acc acc' : XRecord} (h : acc.Equiv acc') (e : Endpoint)
    (a : Fin 5) : XRecord.Equiv (OnePhaseDimension.Certificate.pushIdx acc e a)
      (OnePhaseDimension.Certificate.pushIdx acc' e a) := by
  intro c
  cases e with
  | x c' =>
    simp only [OnePhaseDimension.Certificate.pushIdx, Function.update_apply]
    split_ifs with hc
    · subst hc; exact (h c).append_right _
    · exact h c
  | _ => exact h c
namespace CertData
variable (d : CertData)
end CertData
namespace Key
end Key
end OnePhaseDimension.Certificate
