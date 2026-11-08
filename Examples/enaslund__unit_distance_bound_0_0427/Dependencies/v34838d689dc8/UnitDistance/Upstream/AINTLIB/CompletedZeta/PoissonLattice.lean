/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
Modified for enaslund/unit-distance-bound: import lines relocated from
DedekindResidue.* to UnitDistance.Upstream.AINTLIB.* and `public import Mathlib`
narrowed to specific Mathlib modules for the Lean 4.32.0 / Mathlib 81a5d257 pin;
proof text unchanged. Upstream and local hashes: third-party/aintlib/manifest.json.
-/
module
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v34838d689dc8.UnitDistance.Upstream.AINTLIB.CompletedZeta.DualLattice
/-!
# Poisson summation over a general `ℤ`-lattice  (SP1-AGP, leaf P.3)

Transport of the `ℤ^ι` Poisson formula (`tsum_eq_tsum_fourier_zpoint`) to an arbitrary
`ℤ`-lattice `L ⊂ EuclideanSpace ℝ ι`: conjugate by the linear equivalence sending the standard
lattice to `L`. The Fourier side transforms by the **`GL` change-of-variables law**
(`fourier_comp_linearEquiv`, new to this development: mathlib only has the isometry case
`Real.fourier_comp_linearIsometry`), the dual lattice appears via `dualZLattice_eq_span`
(P.1), and the covolume factor via `ZLattice.covolume_eq_det_mul_measureReal`.

## Main results (this file)
* `DedekindResidue.fourier_comp_linearEquiv` —
  `𝓕(g ∘ T) w = |det T|⁻¹ • 𝓕 g ((T⁻¹)^* w)` for `T ∈ GL(EuclideanSpace ℝ ι)`.
* `DedekindResidue.tsum_eq_tsum_fourier_zlattice` — **Poisson summation over a `ℤ`-lattice**:
  `∑'_{v ∈ L} g(v) = covol(L)⁻¹ • ∑'_{w ∈ L♯} 𝓕g(w)`.
-/
namespace DedekindResidue
@[expose] public section
open MeasureTheory Complex TopologicalSpace
open scoped FourierTransform
variable {ι : Type*} [Fintype ι]
open LinearMap.BilinForm
open scoped RealInnerProductSpace
end
end DedekindResidue
