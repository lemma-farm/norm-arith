module
public import Mathlib
public import Examples.lgruen__quasi_uniform_sequences_lean.Dependencies.v30e4bfa02a7b.Z3Net.Defs
set_option autoImplicit false
@[expose] public section
/-!
# Theorem 2 (`thm:two`), part 1: the Möbius map `τ` as a polynomial map

`tauL N P = ∑_{l ≤ N} P_l (1 - X)^(N - l)` is `τ` on `ℤ[t]_{≤ N}` (`(τV)(t) = (1-t)^N V(1/(1-t))`).
Key facts: multiplicativity `τ_{a+b}(PQ) = τ_a(P) τ_b(Q)` (degree bounds `a`, `b`), hence
`τ³ = (-1)^N`; the matrix `tau m` is `tauL (m-1)` on coefficient vectors.
-/
namespace Z3Net.Two
open Polynomial Finset Matrix
noncomputable section
end
end Z3Net.Two
