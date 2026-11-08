/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.LinearMap
/-!
# s-Numbers: rank definition and the Pietsch axioms

This file collects:

* `ContinuousLinearMap.rank` — a thin wrapper around `LinearMap.rank` providing
  dot notation for continuous linear maps. Auxiliary rank facts live in
  `SNumbers.Helpers`.
* The five Pietsch axioms (S1)–(S5) characterising an *s-number sequence*,
  packaged in the structure `IsSNumberSequence`.
* The strengthening (S5') and the structure `IsStrictSNumberSequence`.
* **Homogeneity** (`norm_smul_sn`): every s-number sequence satisfies
  `sₙ(c • T) = ‖c‖ · sₙ(T)`, with the two one-sided inequalities
  `sn_smul_le` and `norm_smul_le_sn`. This is a consequence of the axioms
  (essentially (S3)), so it belongs here with the abstract theory.
* **Norm bound** (`IsSNumberSequence.le_norm`): every s-number sequence
  satisfies `sₙ S ≤ ‖S‖`, since `sₙ S ≤ s₀ S = ‖S‖` (antitonicity + (S1a)).
  Like homogeneity, a consequence of the axioms belonging with the abstract
  theory; the concrete `…_le_norm` lemmas in each file are its instances.

An s-number sequence assigns to every bounded linear operator
`S : X →L[𝕜] Y` between (real or complex) Banach spaces a sequence
`(s_n S)_{n ∈ ℕ}` of non-negative reals satisfying:

* (S1) `0 ≤ s (n+1) S ≤ s n S` and `s 0 S = ‖S‖`,
* (S2) `s n (S + T) ≤ s n S + ‖T‖`,
* (S3) `s n (B ∘ S ∘ A) ≤ ‖B‖ * s n S * ‖A‖`,
* (S4) `s n S = 0` whenever `rank S ≤ n`,
* (S5) `s n (id_{ℓ₂^{n+1}}) = 1`.

A *strict* s-number sequence additionally satisfies the strengthening
(S5') `s n (id_X) = 1` for every `X` with `dim X > n`, not just `ℓ₂^{n+1}`.

## Index convention

We use **0-based indexing**, shifted by one from Pietsch's original convention:
Pietsch's `s_1 S = ‖S‖` is our `s_0 S`, and Pietsch's `s_{n+1}` is our `s_n`.
This fits the convention used in the context of n-width and information-based
complexity.


## Implementation notes

The carrier is a universe-polymorphic family — see `Family` — mirroring
Pietsch's class function on `𝓛 = ⋃_{X,Y} 𝓛(X,Y)`. Completeness is **not**
required at the level of axioms; downstream constructions add
`[CompleteSpace X]` where needed.
-/
universe u
open scoped Cardinal
namespace ContinuousLinearMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
/-- The rank of a continuous linear map, defined as the dimension of its
range as a `Cardinal`. -/
noncomputable abbrev rank (S : X →L[𝕜] Y) : Cardinal :=
  LinearMap.rank (S : X →ₗ[𝕜] Y)
end ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
end SNumbers
