/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.Digits.Defs
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Graph keys for scalar tensor monomials

A *graph key* describes a tensor monomial in a symmetric matrix `A`, vectors `p, ℓ`, a cubic
tensor `X` and scalars `g, w, z` on `ℝ⁵`:

  `g^h w^a z^b ∏ tr(A^{k_i}) · ∑_{internal indices} ∏_{edges} (A^k)_{uv} · (vector and X entries)`.

An edge carries a matrix power `A^k` (with `A^0 = δ`) between two endpoints. An endpoint is a
free slot, a copy of `p`, a copy of `ℓ`, or an incidence at one of the copies of `X`. Copies of
`p` and `ℓ` are degree-one vertices; each copy of `X` has three incidences.

This file contains only the combinatorial side, designed so that everything reduces in the
Lean kernel:

* `Endpoint`, `Edge`, `Key` and their numeric codes;
* `Key.pack : Key → ℕ`, an injective (on bounded keys) packing into a single natural number in
  base `256`, used as the sort key of polynomials; `Key.unpack` is its inverse;
* `Key.normalize` (sorting) and `Key.reduce` (trace and `X`-trace reductions), combined in
  `Key.canon`;
* `Key.mul` (disjoint union) and `Key.contract` (contraction of two free slots);
* `Poly`, sorted association lists from packed keys to integer coefficients, with a
  structurally recursive merge;
* `decodeWord`, the decimal digit-word encoding of the tables.

The semantics is in `OnePhaseDimension.Certificate.Eval`.

## Encoding

The decimal encoding of the tables (the 2026-09-24 version, Section "Tensor monomials") uses
labels `0, …, r-1` for free slots, `5` for `p`, `6` for `ℓ`, `7, 8` for the first and second
copy of `X`. Internally we use the numeric endpoint codes

  `X_1 ↦ 0`, `X_0 ↦ 1`, `ℓ ↦ 2`, `p ↦ 3`, `slot i ↦ 4 + 2i`, and `X_c ↦ 2c + 1` for `c ≥ 2`,

so that the code is injective for any number of slots and of `X` copies. On keys with at most
two copies of `X` (the only ones that occur) this is the order of the 2026-09-24 version, which
replaces the labels `5, 6, 7, 8` by `-1, -2, -3, -4`: our canonical form is then exactly the
paper's (sorted endpoints, sorted edges, sorted traces, and the lexicographically larger edge
list under the exchange of the two copies of `X`).

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/
@[expose] public section
namespace OnePhaseDimension.Certificate
/-- The base of the packed key encoding. -/
abbrev packBase : ℕ := 256
/-! ### Endpoints and edges -/
/-- An endpoint of an edge of a graph key. -/
inductive Endpoint where
  /-- A copy of the vector `p`. -/
  | p
  /-- A copy of the vector `ℓ`. -/
  | ell
  /-- An incidence at the `c`-th copy of the cubic tensor `X`. -/
  | x (c : ℕ)
  /-- The `i`-th free slot. -/
  | slot (i : ℕ)
  deriving DecidableEq, Repr, Inhabited
namespace Endpoint
/-- The numeric code of an endpoint: `X_1 ↦ 0`, `X_0 ↦ 1`, `ℓ ↦ 2`, `p ↦ 3`,
`slot i ↦ 4 + 2i`, and `X_c ↦ 2c + 1` for `c ≥ 2`. -/
def code : Endpoint → ℕ
  | x c => if c = 0 then 1 else if c = 1 then 0 else 2 * c + 1
  | ell => 2
  | p => 3
  | slot i => 4 + 2 * i
/-- Inverse of `Endpoint.code`. -/
def ofCode (n : ℕ) : Endpoint :=
  if n = 0 then x 1 else if n = 1 then x 0 else if n = 2 then ell else if n = 3 then p
  else if n % 2 = 0 then slot ((n - 4) / 2) else x ((n - 1) / 2)
def ofDigit (d : ℕ) : Endpoint :=
  if d = 5 then p else if d = 6 then ell else if d = 7 then x 0 else if d = 8 then x 1
  else slot d
end Endpoint
/-- An unoriented edge carrying the matrix `A ^ pow` between endpoints `u` and `v`. -/
structure Edge where
  /-- First endpoint. -/
  u : Endpoint
  /-- Second endpoint. -/
  v : Endpoint
  /-- The power of `A` carried by the edge. -/
  pow : ℕ
  deriving DecidableEq, Repr, Inhabited
namespace Edge
/-- The code of an edge, ordered lexicographically by `(u.code, v.code, pow)` for bounded
codes. -/
def code (e : Edge) : ℕ := (e.u.code * packBase + e.v.code) * packBase + e.pow
def digits (e : Edge) : List ℕ := [e.u.code, e.v.code, e.pow]
end Edge
/-! ### Keys -/
/-- A graph key: the rank, the powers of `g, w, z`, the list of powers `k` of trace factors
`tr A^k`, and the list of edges. -/
structure Key where
  /-- Number of free slots. -/
  rank : ℕ
  /-- Power of `g`. -/
  gPow : ℕ
  /-- Power of `w`. -/
  wPow : ℕ
  /-- Power of `z`. -/
  zPow : ℕ
  /-- Powers `k` of the trace factors `tr A^k`. -/
  traces : List ℕ
  /-- The edges. -/
  edges : List Edge
  deriving DecidableEq, Repr, Inhabited
namespace Key
/-- The digit list of a key: `rank, gPow, wPow, zPow, #traces, traces…, #edges, edges…`, each
edge contributing `u.code, v.code, pow`. -/
def digits (k : Key) : List ℕ :=
  [k.rank, k.gPow, k.wPow, k.zPow, k.traces.length] ++ k.traces ++
    k.edges.length :: k.edges.flatMap Edge.digits
/-- All digits are below the packing base. -/
def Bounded (k : Key) : Prop := ∀ d ∈ k.digits, d < packBase
instance (k : Key) : Decidable k.Bounded := inferInstanceAs (Decidable (∀ d ∈ _, _))
def digitsLE : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else n % packBase :: digitsLE fuel (n / packBase)
/-- Parse `count` edges from a digit list. -/
def parseEdges : ℕ → List ℕ → List Edge
  | 0, _ => []
  | n + 1, u :: v :: k :: rest => ⟨.ofCode u, .ofCode v, k⟩ :: parseEdges n rest
  | _ + 1, _ => []
/-- Parse a digit list produced by `Key.digits`. -/
def ofDigits : List ℕ → Key
  | r :: h :: a :: b :: nt :: rest =>
    match rest.drop nt with
    | ne :: rest' => ⟨r, h, a, b, rest.take nt, parseEdges ne rest'⟩
    | [] => ⟨r, h, a, b, rest.take nt, []⟩
  | _ => ⟨0, 0, 0, 0, [], []⟩
/-- Inverse of `Key.pack` on bounded keys. -/
def unpack (n : ℕ) : Key := ofDigits ((digitsLE (n + 1) n).reverse.drop 1)
/-! ### Packing is invertible on bounded keys -/
def xBound (k : Key) : ℕ :=
  k.edges.foldr (fun e acc => max acc (max (bound e.u) (bound e.v))) 0
where
  /-- One more than the copy index of an `X` endpoint, zero otherwise. -/
  bound : Endpoint → ℕ
    | .x c => c + 1
    | _ => 0
end Key
/-! ### Decoding the decimal tables -/
/-- Read a digit list in consecutive triples. -/
def triples : List ℕ → List (ℕ × ℕ × ℕ)
  | a :: b :: c :: rest => (a, b, c) :: triples rest
  | _ => []
/-- The key of a rank-`r` tensor monomial encoded by a decimal digit word: the first triple
`h b j` gives `g^h (tr A^3)^b w^[j=1] z^[j=2]`, and each later triple `u v k` an edge carrying
`A^k` between the endpoints labelled `u` and `v`. -/
def decodeWord (r : ℕ) (word : List ℕ) : Key :=
  match triples word with
  | [] => ⟨r, 0, 0, 0, [], []⟩
  | (h, b, j) :: es =>
    { rank := r, gPow := h
      wPow := if j = 1 then 1 else 0
      zPow := if j = 2 then 1 else 0
      traces := List.replicate b 3
      edges := es.map fun e => ⟨.ofDigit e.1, .ofDigit e.2.1, e.2.2⟩ }
/-- The `len` decimal digits of `n`, most significant first, with leading zeros. Written with
the recursor `Nat.rec` and an accumulator, which the kernel reduces faster than a compiled
pattern match. -/
def wordDigits (len n : ℕ) : List ℕ :=
  (Nat.rec (motive := fun _ => ℕ → List ℕ → List ℕ) (fun _ acc => acc)
    (fun _ ih m acc => ih (m / 10) ((m % 10) :: acc)) len) n []
/-! ### Polynomials -/
/-- A polynomial in graph keys: an association list from packed keys to integer coefficients,
kept sorted by increasing key with no zero coefficients. -/
abbrev Poly := List (ℕ × ℤ)
namespace Poly
end Poly
namespace Poly
end Poly
namespace Key
end Key
/-! ### Text dump in the reference format

`r<r>g<g>w<w>z<z>|t<k1>,<k2>,…|<U><V><k>,…`, where an endpoint is printed as `Y X L P` for the
second copy of `X`, the first copy of `X`, `ℓ`, `p`, and as its index for a free slot. These
functions are for `#eval` dumps only and are not used in kernel computations. -/
end OnePhaseDimension.Certificate
