module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/TensorBundle/SmoothOrthoFrame.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream package-option restoration, and pinned API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Mathlib
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.Shared.Algebraic.Auxiliary.OrthonormalBasisDiagonal
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Metric.RiemannianMetric
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.TangentBundle.TangentSmooth
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.TensorBundle.SmoothOrthoFrame.ChartBasis
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.TensorBundle.SmoothOrthoFrame.Orthonormality
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain the upstream independent metric binders rather than changing theorem contracts.
set_option linter.overlappingInstances false
/-!
# Smooth orthonormal local frame from the chart frame

For a Riemannian manifold $(M, g)$ and a base point $\alpha : M$:

* `chartBasisVecFiber α i b` — the $i$-th tangent vector at $b$ obtained
  by transporting the $i$-th model-space basis vector through the
  inverse of the tangent trivialization centred at $\alpha$ (smooth on
  the trivialization base set, junk off it).
* `chartFrameNormFiber g α b i` — fiberwise $g$-Gram-Schmidt
  orthonormalisation of `chartBasisVecFiber α · b`.
* `smoothOrthoFrame g α i` — globally-smooth tangent-bundle section
  obtained by multiplying `chartFrameNorm g α i` by a smooth bump
  function whose support lies in the chart source; identically zero off
  the chart source, equal to the un-bumped Gram-Schmidt frame on
  `smoothOrthoFrameNbhd α`.

Used downstream by the heart-of-Bochner sum identity, where the smooth
orthonormal frame is the basis along which $\nabla^2(\nabla f)$'s trace
becomes $\Delta_g f$.

**Ground truth**: do Carmo §1 (chart-frame trivialization); Lee §3
(smooth bump functions); Petersen §1 (Gram-Schmidt). The construction
follows an external `differential-geometry` lib analog.
-/
noncomputable section
open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff Bundle
namespace Riemannian
namespace Tensor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
/-! ## Stage 3: bump-cutoff to produce a global section

The chart-frame normalised Gram-Schmidt is $C^\infty$ only on the chart
source. To produce a globally smooth tangent-bundle section, we
multiply by a smooth bump function centred at $\alpha$ whose support
lies inside the chart source. -/
variable [hm : HasMetric I M]
open scoped InnerProductSpace
end Tensor
end Riemannian
end
