module
/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/TangentBundle/TangentSmooth.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream package-option restoration, and pinned API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Mathlib
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.TangentBundle.LocallyConstant
public import Examples.nihargargava__systole_bound.Dependencies.v8bdaaae6d5ee.Vendored.DoCarmo.DoCarmoLib.Riemannian.Util.Chart.FlatChartDerivs
@[expose] public section
-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
/-!
# Tangent bundle smoothness API

Smoothness of tangent vector fields and chart-frame derivatives. The
file collects:

* `IsLocallyConstantChartedSpace` — chart-coherence typeclass needed for
  parametric chart-mfderiv smoothness.
* `TangentSmoothAt` + closure under the $C^\infty(M)$-module operations.
* Flat-codomain chart-frame trivializations `symmLFlat`,
  `continuousLinearMapAtFlat` and their basepoint smoothness.
* Bundled smooth vector fields `SmoothVectorField`.
* Chart-frame `mfderiv` smoothness in constant and smoothly-varying
  directions.

Reference: Lee, *Smooth Manifolds*, Ch. 8 and Ch. 11.
-/
open scoped ContDiff Manifold Topology
-- `IsLocallyConstantChartedSpace` typeclass + chart-constancy lemma +
-- strict-interior nbhd propagation live in
-- `TangentBundle/LocallyConstant.lean`.
-- Flat-codomain chart-derivative wrappers + parametric chart-mfderiv
-- smoothness live in `Util/FlatChartDerivs.lean`.
/-! ## Tangent vector field smoothness predicate

`TangentSmoothAt V x` is the framework's canonical smoothness predicate
for tangent sections, equivalent to the bundle-form
`MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y ↦ ⟨y, V y⟩) x` but
opaque to elaborator unfolding for tactic-search performance.
-/
namespace Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
/-- **Math.** The section $V \colon M \to TM$ is **smooth at $x$**:
$y \mapsto \langle y, V(y)\rangle$ is `MDifferentiableAt` at $x$ as a
map $M \to TM$. -/
def TangentSmoothAt (V : (y : M) → TangentSpace I y) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (fun y => (⟨y, V y⟩ : TangentBundle I M)) x
namespace TangentSmoothAt
theorem mk {V : (y : M) → TangentSpace I y} {x : M}
    (h : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) x) :
    TangentSmoothAt V x := h
theorem toBundleSection {V : (y : M) → TangentSpace I y} {x : M}
    (h : TangentSmoothAt V x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) x := h
/-- **Eng.** Chart-coordinate form: `y ↦ (trivAt x ⟨y, V y⟩).2 : M → E` is smooth. -/
theorem coordSmoothAt {V : (y : M) → TangentSpace I y} {x : M}
    (hV : TangentSmoothAt V x) :
    MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => ((trivializationAt E (TangentSpace I) x) ⟨y, V y⟩).2) x := by
  have h := hV.toBundleSection
  rw [mdifferentiableAt_totalSpace] at h
  exact h.2
theorem iff_coord {V : (y : M) → TangentSpace I y} {x : M} :
    TangentSmoothAt V x ↔
      MDifferentiableAt I 𝓘(ℝ, E)
        (fun y => ((trivializationAt E (TangentSpace I) x) ⟨y, V y⟩).2) x := by
  unfold TangentSmoothAt
  rw [mdifferentiableAt_totalSpace]
  exact ⟨And.right, fun h => ⟨mdifferentiableAt_id, h⟩⟩
theorem add {Y Z : (y : M) → TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    TangentSmoothAt (Y + Z) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  have hY' := hY.coordSmoothAt
  have hZ' := hZ.coordSmoothAt
  apply (hY'.add hZ').congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, (Y + Z) y⟩).2 = (e ⟨y, Y y⟩).2 + (e ⟨y, Z y⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  show (e.continuousLinearMapAt ℝ y) ((Y + Z) y)
      = (e.continuousLinearMapAt ℝ y) (Y y) + (e.continuousLinearMapAt ℝ y) (Z y)
  show (e.continuousLinearMapAt ℝ y) (Y y + Z y)
      = (e.continuousLinearMapAt ℝ y) (Y y) + (e.continuousLinearMapAt ℝ y) (Z y)
  exact ContinuousLinearMap.map_add _ _ _
theorem neg {V : (y : M) → TangentSpace I y} {x : M}
    (hV : TangentSmoothAt V x) :
    TangentSmoothAt (-V) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  have hV' := hV.coordSmoothAt
  apply hV'.neg.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, (-V) y⟩).2 = -(e ⟨y, V y⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  show (e.continuousLinearMapAt ℝ y) ((-V) y) = -(e.continuousLinearMapAt ℝ y) (V y)
  show (e.continuousLinearMapAt ℝ y) (-V y) = -(e.continuousLinearMapAt ℝ y) (V y)
  exact ContinuousLinearMap.map_neg _ _
theorem sub {Y Z : (y : M) → TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    TangentSmoothAt (Y - Z) x := by
  have h_eq : (Y - Z : (y : M) → TangentSpace I y) = Y + (-Z) := by
    funext y
    show Y y - Z y = Y y + -Z y
    exact sub_eq_add_neg _ _
  rw [h_eq]
  exact hY.add hZ.neg
theorem smul {f : M → ℝ} {V : (y : M) → TangentSpace I y} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hV : TangentSmoothAt V x) :
    TangentSmoothAt (fun y => f y • V y) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  have hV' := hV.coordSmoothAt
  apply (hf.smul hV').congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, f y • V y⟩).2 = f y • (e ⟨y, V y⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  show (e.continuousLinearMapAt ℝ y) (f y • V y)
      = f y • (e.continuousLinearMapAt ℝ y) (V y)
  exact ContinuousLinearMap.map_smul _ _ _
end TangentSmoothAt
end Riemannian
-- Flat-codomain chart-derivative wrappers (`symmLFlat`,
-- `continuousLinearMapAtFlat`, `mfderivWithinFlat`) and their basepoint
-- smoothness theorems live in `Util/FlatChartDerivs.lean`.
-- They are reachable through the import above.
/-! ## Bundled smooth vector fields

`SmoothVectorField I M` packages a tangent section with its $C^\infty$
smoothness witness. Algebraic operations (zero, add, sub, neg, smul,
constant section) are defined; clients use the bundled type to avoid
threading `ContMDiff` premises through every theorem.
-/
namespace Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
structure SmoothVectorField (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- Underlying tangent section. -/
  toFun : Π y : M, TangentSpace I y
  /-- Smoothness of the bundle section. -/
  smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
    (fun y => (⟨y, toFun y⟩ : TangentBundle I M))
namespace SmoothVectorField
instance : CoeFun (SmoothVectorField I M) fun _ => Π y : M, TangentSpace I y :=
  ⟨toFun⟩
lemma coe_mk (f : Π y : M, TangentSpace I y) (h) :
    ⇑(⟨f, h⟩ : SmoothVectorField I M) = f := rfl
/-- The smooth vector field that is zero at every point. -/
noncomputable def zero : SmoothVectorField I M where
  toFun := fun _ => 0
  smooth := Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M)) (n := ∞)
noncomputable instance : Zero (SmoothVectorField I M) := ⟨zero⟩
@[simp] lemma zero_apply (y : M) : (0 : SmoothVectorField I M) y = 0 := rfl
/-- Pointwise addition of smooth vector fields. -/
noncomputable def add (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => X y + Y y
  smooth := ContMDiff.add_section X.smooth Y.smooth
noncomputable instance : Add (SmoothVectorField I M) := ⟨add⟩
@[simp] lemma add_apply (X Y : SmoothVectorField I M) (y : M) :
    (X + Y) y = X y + Y y := rfl
/-- Pointwise negation of a smooth vector field. -/
noncomputable def neg (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => -X y
  smooth := ContMDiff.neg_section X.smooth
noncomputable instance : Neg (SmoothVectorField I M) := ⟨neg⟩
noncomputable def sub (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => X y - Y y
  smooth := ContMDiff.sub_section X.smooth Y.smooth
noncomputable instance : Sub (SmoothVectorField I M) := ⟨sub⟩
@[simp] lemma sub_apply (X Y : SmoothVectorField I M) (y : M) :
    (X - Y) y = X y - Y y := rfl
/-- Pointwise scalar multiplication of a smooth vector field by a constant real number. -/
noncomputable def constSMul (a : ℝ) (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => a • X y
  smooth := ContMDiff.const_smul_section (a := a) X.smooth
noncomputable instance : SMul ℝ (SmoothVectorField I M) := ⟨constSMul⟩
noncomputable def smul (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => f y • X y
  smooth := ContMDiff.smul_section hf X.smooth
@[simp] lemma smul_apply (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) (y : M) :
    (smul f hf X) y = f y • X y := rfl
/-- **Math.** Constant `E`-valued section as a `SmoothVectorField`. -/
noncomputable def const [_root_.IsLocallyConstantChartedSpace H M] (v : E) :
    SmoothVectorField I M where
  toFun := fun _ => v
  smooth := TangentBundle.contMDiff_constSection_TangentSpace v
@[simp] lemma const_apply [_root_.IsLocallyConstantChartedSpace H M] (v : E) (y : M) :
    (const (I := I) v) y = v := rfl
end SmoothVectorField
end Riemannian
/-! ## `mfderiv` smoothness in chart-frame directions

For a globally smooth scalar $f : M \to \mathbb{R}$ and either a
constant direction $v : E$ or a smoothly-varying direction $V : M \to E$,
the function $y \mapsto \mathrm{d}f_y(V(y))$ is smooth at every point.

These are boundary-agnostic: the chart-pullback formula
$\mathrm{d}f_y = \mathrm{fderivWithin}_{\mathrm{range}\, I}(f \circ
\mathrm{chart.symm})$ combined with `IsLocallyConstantChartedSpace`
(which makes `extChartAt I y = extChartAt I x` constant on a
neighborhood of `x`) lifts $C^\infty$ regularity from the chart side
to the manifold side via `comp_of_preimage_mem_nhdsWithin`.
-/
namespace Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
end Riemannian
