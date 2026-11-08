/-
Development copy (Solution side) of the Challenge for the paper: Well-separated (0,3k,3)-nets in every base q ≥ 4: one linear scramble of the
Faure–Hammersley net (draft, revision 4, 2026-10-07).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
The centred residue `cres` is adapted from Lennart Rudolph's Palomar formalization of the
even-order Grünschloß–Keller nets (github.com/lennrt/palomar-formalizations, MIT licence).
-/
module
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Definitions (verbatim copy of the definitions in `Challenge.lean`)

Keep in sync with `Challenge.lean`; Comparator checks that the Solution declarations have the
same types and values.
-/
namespace Z3Net
open Matrix
/-! ## Digital nets, elementary boxes, distances -/
def tau (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i l => (-1) ^ (i : ℕ) * ((m - 1 - (l : ℕ)).choose (i : ℕ) : ℤ)
/-- `T = s_k τ` with `s_k = (-1)^(k+1)`, on `ℤ[t]_{<3k}`. -/
def T (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  ((-1 : ℤ) ^ (k + 1)) • tau (3 * k)
/-- `K`: lower-triangular Toeplitz matrix of `(1-t)^(-k)`, `K_{ij} = C(i-j+k-1, k-1)`
for `i ≥ j`. -/
def K (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  fun i j => if j ≤ i then (((i : ℕ) - j + k - 1).choose (k - 1) : ℤ) else 0
/-- `E`: the identity except in rows `k-2, k-1, k`:
`(Ed)_{k-2} = d_0 + … + d_{k-2}`, `(Ed)_{k-1} = -d_{k-1}`, `(Ed)_k = d_{k-1} + d_k`.
(For `k = 1` row `k-2` does not exist.) -/
def E (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  fun i j =>
    if (i : ℕ) + 2 = k then (if (j : ℕ) + 2 ≤ k then 1 else 0)
    else if (i : ℕ) + 1 = k then (if j = i then -1 else 0)
    else if (i : ℕ) = k then (if (j : ℕ) + 1 = k ∨ (j : ℕ) = k then 1 else 0)
    else (if j = i then 1 else 0)
/-- The scramble `L = E K`. -/
def L (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ := E k * K k
end Z3Net
