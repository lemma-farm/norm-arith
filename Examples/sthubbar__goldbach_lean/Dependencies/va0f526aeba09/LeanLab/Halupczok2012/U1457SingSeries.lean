module
public import Examples.sthubbar__goldbach_lean.Dependencies.va0f526aeba09.LeanLab.Halupczok2012.U1452MainTermMV
/-!
# P0077 Halupczok 2012, the main term step reduced to Theorem 3 and an elementary input, U-1457

AI wrote the Lean code, Claude, run 20261022T0003Z-15508. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.

The paper's main term step, the displays after (10) in the proof of Theorem 2, rests on two
things: Theorem 3 of Perelli-Pintz-Salerno, used through the CRT step `crtStep` of U-1452, and a
purely elementary statement about the singular series, with no primes in it. This file names the
second as `SingSeriesApprox` and proves

* `mainTermMV_of_inputs : Theorem3 → SingSeriesApprox → MainTermMV`. CONDITIONAL ON both.
* `theorem2Zeroed_of_three`: the F-0008 repair, CONDITIONAL ON `Theorem3`, `Theorem5` and
  `SingSeriesApprox`.

`SingSeriesApprox` says: under the hypotheses of Theorem 2 there are a finite set `Z` of moduli
`s ≤ L^D`, `s ≤ X₁`, at most `L^D` of them, and `s`-periodic weights `g_s` bounded by a constant
`K`, such that
(i) TAIL: `∑_{q ≤ Q, (a,q)=1} ∑_{m ∈ (X₁, X₁+Y₁], m ≡ a (q)} log m |𝔖(n - m) - ∑_{s ∈ Z} g_s(m)|
    ≪ Y₁ L^{-A}`, a sum over ALL integers `m`, no primes;
(ii) EULER PRODUCT: `∑_{q ≤ Q, (a,q)=1} |∑_{s ∈ Z} Y₁/φ([q,s]) ∑_{b ∈ G(a,q,s)} g_s(b) - 𝔗(n,q,a) Y₁|
    ≪ Y₁ L^{-A}`.
In the paper `Z` is the squarefree `s ≤ L^C` and `g_s(m) = μ(s)² c_s(n - m)/φ(s)²`, the
Ramanujan expansion of `𝔖`.

Toward proving `SingSeriesApprox`, the local algebra:

* `local_factor_div`, `local_factor_ndiv`: for an odd prime `p`,
  `1 + c_p(r)/(p-1)²` equals `(1 - 1/(p-1)²)(p-1)/(p-2)` if `p ∣ r` and `1 - 1/(p-1)²` if not,
  with `c_p(r) = p - 1` or `-1`. PROVED.
* `euler_expand`: `∏_{p ∈ P} (1 + f p) = ∑_{t ⊆ P} ∏_{p ∈ t} f p`, the squarefree expansion. PROVED.
* `ramanujanP_periodic`: the weight `∏_{p ∈ t} c_p(n - m)` is `∏ t`-periodic in `m`. PROVED.
* `truncS_expand`: the truncated singular series over a finite set `P` of odd primes,
  `∏_{p ∈ P} (1 - 1/(p-1)²) ∏_{p ∈ P, p ∣ r} (p-1)/(p-2)`, equals the sum over `t ⊆ P` of
  `∏_{p ∈ t} c_p(r)/(p-1)²`. PROVED.
-/
@[expose] public section
namespace LeanLab.Halupczok2012
open Finset
/-! ### The elementary input -/
end LeanLab.Halupczok2012
