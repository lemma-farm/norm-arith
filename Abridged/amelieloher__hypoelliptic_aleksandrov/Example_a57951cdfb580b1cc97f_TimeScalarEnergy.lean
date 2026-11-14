module

public import Mathlib
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Ambient.Basic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Ambient carriers

The common finite-dimensional carriers used by the PDE libraries. The
inherited norm on `Vec d` is the finite-product supremum norm; Euclidean
quadratic structure is defined explicitly in `PDEFoundation.Ambient.EuclideanNorm`.
-/
@[expose] public section
namespace PDE
/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ
end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Measure.RestrictedVolume ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Restricted Lebesgue volume

One restricted-volume convention for every later `Lp`, Sobolev, and weak PDE
module.
-/
@[expose] public section
namespace PDE
/-- Lebesgue volume restricted to a native-vector domain. -/
noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U
namespace IsOpenBoundedConvexDomain
end IsOpenBoundedConvexDomain
namespace IsSobolevRegularDomain
end IsSobolevRegularDomain
end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Ambient.Basis ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coordinate basis of the native ambient space

The coordinate basis and its exact dot-product and Euclidean-length formulas.
-/
@[expose] public section
namespace PDE
/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)
end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Sobolev.WeakDerivative ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Weak first derivatives on native vector domains

The raw integration-by-parts predicates remain compatible with LIH. A bundled
test-function facade packages smoothness, compact support, and support
containment for later PDE proofs.
-/
@[expose] public section
namespace PDE
/-- A smooth compactly supported test function whose topological support lies
inside `U`. -/
structure WeakTestFunction {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  contDiff : ContDiff ℝ (⊤ : ℕ∞) toFun
  hasCompactSupport : HasCompactSupport toFun
  tsupport_subset : tsupport toFun ⊆ U
instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (WeakTestFunction U) (fun _ => Vec d → ℝ) where
  coe φ := φ.toFun
/-- The classical `i`th derivative of a bundled test function. -/
noncomputable def WeakTestFunction.partialDeriv
    {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (i : Fin d) (x : Vec d) : ℝ :=
  (fderiv ℝ φ.toFun x) (basisVec i)
/-- `gi` is the `i`th weak derivative of `u` on `U`. -/
def HasWeakPartialDerivOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume
/-- `Du` is a coordinate weak gradient of `u` on `U`. -/
def HasWeakGradientOn {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)

namespace HasWeakPartialDerivOn
end HasWeakPartialDerivOn

axiom HasWeakGradientOn.of_contDiff {d : ℕ}
    {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    HasWeakGradientOn U f
      (fun x i => (fderiv ℝ f x) (basisVec i))
end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Sobolev.W1p.Basic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Representative-level `W^{1,p}`

This compatibility carrier stores concrete value and gradient representatives.
The later Banach carrier is the closed weak-gradient graph modulo a.e.
equality; the two layers intentionally serve different purposes.
-/
@[expose] public section
open scoped ENNReal
namespace PDE
/-- Scalar `L^p` membership on a restricted domain. -/
abbrev MemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u p (volumeOn U)
/-- Coordinatewise gradient `L^p` membership, retained for exact LIH
compatibility. -/
def GradMemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemLpOn U p (fun x => Du x i)
/-- A concrete representative and a chosen coordinate weak gradient. -/
structure W1pFunction {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memLp : MemLpOn U p toFun
  gradMemLp : GradMemLpOn U p grad
  hasWeakGradient : HasWeakGradientOn U toFun grad
instance {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞} :
    CoeFun (W1pFunction U p) (fun _ => Vec d → ℝ) where
  coe u := u.toFun

namespace W1pFunction

/-- Package a compactly supported `C¹` function as a Sobolev
representative. -/
noncomputable def ofContDiff {d : ℕ}
    {U : Set (Vec d)} (_hUOpen : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f)
    (hfSupport : HasCompactSupport f) (p : ℝ≥0∞) :
    W1pFunction U p where
  toFun := f
  grad := fun x i => (fderiv ℝ f x) (basisVec i)
  memLp := by
    have hfCont : Continuous f :=
      (hf.differentiable (by simp)).continuous
    exact (hfCont.memLp_of_hasCompactSupport hfSupport).restrict U
  gradMemLp := by
    intro i
    have hderivCont :
        Continuous (fun x => (fderiv ℝ f x) (basisVec i)) := by
      simpa using
        (hf.continuous_fderiv (by simp)).clm_apply continuous_const
    have hderivSupport :
        HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec i)) := by
      simpa using hfSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact (hderivCont.memLp_of_hasCompactSupport hderivSupport).restrict U
  hasWeakGradient := HasWeakGradientOn.of_contDiff hf
end W1pFunction
end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Ambient.HilbertVec ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Internal Hilbert realization of native vectors

Functional-analytic constructions sometimes need the Euclidean norm as the
typeclass norm. This file provides an internal `PiLp 2` realization together
with exact conversions to the native carrier `PDE.Vec`.

The native carrier remains the public ambient-space API. The wrapper in this
file is used only behind the conversion and norm identities below.
-/
@[expose] public section
namespace PDE
/-- Internal Hilbert realization of a native `d`-vector. -/
abbrev HilbertVec (d : ℕ) :=
  PiLp 2 (fun _ : Fin d => ℝ)
/-- Put a native vector into the internal Hilbert realization. -/
def Vec.toHilbertVec {d : ℕ} (x : Vec d) : HilbertVec d :=
  WithLp.toLp 2 x

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Measure.LpSpace ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Quotient `L^p` spaces on restricted volume

This file names the scalar and internal Hilbert-vector `L^p` spaces used by
closed Sobolev graph constructions. Their measure is always volume restricted
to the displayed domain.
-/
@[expose] public section
open scoped ENNReal
noncomputable section
namespace PDE
/-- Scalar `L^p(U)` modulo equality almost everywhere. -/
abbrev ScalarLp {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) :=
  MeasureTheory.Lp ℝ p (volumeOn U)
/-- `L^p(U)` fields valued in the internal Euclidean Hilbert realization.

Native vector representatives are recovered through the exact bridges in
`PDEFoundation.Ambient.HilbertVec`.
-/
abbrev HilbertVectorLp {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) :=
  MeasureTheory.Lp (HilbertVec d) p (volumeOn U)
end PDE

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Sobolev.W1p.Graph ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The closed weak-gradient graph in `L^p`

For `1 ≤ p`, weak differentiation is encoded by continuous scalar constraints
on a product of quotient `L^p` spaces. Intersecting their kernels gives a
closed submodule, hence a complete subtype.

The vector-valued factor uses the internal Hilbert realization from
`PDEFoundation.Ambient.HilbertVec`; its coordinate and norm bridges keep the
native `PDE.Vec` convention at the project boundary.
-/
@[expose] public section
open scoped ENNReal
noncomputable section
namespace PDE
open MeasureTheory
set_option linter.unusedVariables false in
axiom _root_.PDE.factOneLeConjExponent : ∀ (p : ENNReal) [Fact (1 ≤ p)], Fact (1 ≤ p.conjExponent)
attribute [instance] _root_.PDE.factOneLeConjExponent
namespace WeakTestFunction
/-- A bundled test function belongs to every scalar `L^r(U)`. -/
axiom memLp_toFun {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (r : ℝ≥0∞) :
    MemLp φ.toFun r (volumeOn U)
/-- A directional derivative of a bundled test function belongs to every
scalar `L^r(U)`. -/
axiom memLp_partialDeriv {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (i : Fin d) (r : ℝ≥0∞) :
    MemLp (φ.partialDeriv i) r (volumeOn U)
/-- A bundled test function as an element of scalar `L^r(U)`. -/
def toScalarLp {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (r : ℝ≥0∞) :
    ScalarLp U r :=
  (φ.memLp_toFun r).toLp φ.toFun
/-- A directional derivative of a bundled test function as an element of
scalar `L^r(U)`. -/
def partialDerivToScalarLp {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (i : Fin d) (r : ℝ≥0∞) :
    ScalarLp U r :=
  (φ.memLp_partialDeriv i r).toLp (φ.partialDeriv i)

end WeakTestFunction
/-- The ambient product containing value and weak-gradient `L^p` classes. -/
abbrev WeakGradientLpPair {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) :=
  ScalarLp U p × HilbertVectorLp U p
/-- Coordinate projection on Hilbert-vector-valued `L^p` classes. -/
def hilbertVectorLpCoord {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (i : Fin d) :
    HilbertVectorLp U p →L[ℝ] ScalarLp U p :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL p (volumeOn U)

/-- The scalar Hölder pairing between `L^p(U)` and `L^{p'}(U)`. -/
def scalarLpDualPairing {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] :
    ScalarLp U p →L[ℝ] ScalarLp U p.conjExponent →L[ℝ] ℝ := by
  exact (ContinuousLinearMap.mul ℝ ℝ).lpPairing
    (volumeOn U) p p.conjExponent

/-- The integration-by-parts constraint for coordinate `i` and test function
`φ`. Membership in its kernel says
`∫ u ∂ᵢφ + ∫ (Dᵢu) φ = 0`. -/
def weakGradientConstraint {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (i : Fin d) (φ : WeakTestFunction U) :
    WeakGradientLpPair U p →L[ℝ] ℝ :=
  ((scalarLpDualPairing U p).flip
      (φ.partialDerivToScalarLp i p.conjExponent)).comp
      (ContinuousLinearMap.fst ℝ (ScalarLp U p) (HilbertVectorLp U p)) +
    ((scalarLpDualPairing U p).flip
      (φ.toScalarLp p.conjExponent)).comp
      ((hilbertVectorLpCoord U p i).comp
        (ContinuousLinearMap.snd ℝ (ScalarLp U p) (HilbertVectorLp U p)))

/-- The closed submodule of value-gradient pairs satisfying every weak
integration-by-parts constraint. -/
def weakGradientGraph {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] :
    ClosedSubmodule ℝ (WeakGradientLpPair U p) :=
  ⨅ i : Fin d, ⨅ φ : WeakTestFunction U,
    (⊥ : ClosedSubmodule ℝ ℝ).comap (weakGradientConstraint U p i φ)

/-- Complete quotient-level `W^{1,p}` carrier, realized as the closed
weak-gradient graph. -/
abbrev W1pGraph {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] :=
  ↥(weakGradientGraph U p).toSubmodule

namespace W1pGraph
end W1pGraph
end PDE

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Sobolev.H1.Graph ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The canonical complete `H¹` carrier

The complete quotient-level carrier for `H¹(U)` is not a second graph
construction. It is the `p = 2` specialization of `W1pGraph`, whose value and
gradient components are `L²` equivalence classes satisfying the closed weak
gradient constraints.

`H1Function U` remains the field-name-compatible concrete-representative
interface. A representative-to-graph map belongs to the generic `W^{1,p}`
bridge and is intentionally not duplicated here.
-/
@[expose] public section
open scoped ENNReal
namespace PDE
/-- The canonical complete quotient-level `H¹(U)` carrier. Completeness and
the normed linear structure are inherited definitionally from `W1pGraph U 2`.
-/
abbrev H1Graph {d : ℕ} (U : Set (Vec d)) :=
  W1pGraph U (2 : ℝ≥0∞)
namespace H1Graph
end H1Graph
end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Sobolev.H1.HilbertGraph ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Hilbert realization of the complete `H¹` graph

`H1Graph U` deliberately inherits the maximum norm on the product used by the
general-`p` graph.  At `p = 2`, Lax--Milgram and Riesz representation instead
need the equivalent `ℓ²` product norm.  This file pulls the same closed graph
back through `WithLp.prodContinuousLinearEquiv`; it does not conflate the two
norms.
-/
@[expose] public section
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace PDE
/-- The `ℓ²`-normed product ambient for the `p = 2` weak-gradient graph. -/
abbrev H1HilbertAmbient {d : ℕ} (U : Set (Vec d)) :=
  WithLp 2
    (ScalarLp U (2 : ℝ≥0∞) × HilbertVectorLp U (2 : ℝ≥0∞))
/-- The standard continuous linear equivalence from the `ℓ²` product
realization to the ordinary product carrier. -/
abbrev h1HilbertAmbientEquiv {d : ℕ} (U : Set (Vec d)) :
    H1HilbertAmbient U ≃L[ℝ]
      WeakGradientLpPair U (2 : ℝ≥0∞) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ
    (ScalarLp U (2 : ℝ≥0∞))
    (HilbertVectorLp U (2 : ℝ≥0∞))
/-- The same weak-gradient graph, pulled back to the Hilbert product norm. -/
abbrev h1HilbertClosedSubmodule {d : ℕ} (U : Set (Vec d)) :
    ClosedSubmodule ℝ (H1HilbertAmbient U) :=
  (weakGradientGraph U (2 : ℝ≥0∞)).comap
    (h1HilbertAmbientEquiv U).toContinuousLinearMap
/-- Submodule view used to inherit the Hilbert-space instances. -/
abbrev h1HilbertSubmodule {d : ℕ} (U : Set (Vec d)) :
    Submodule ℝ (H1HilbertAmbient U) :=
  (h1HilbertClosedSubmodule U).toSubmodule
/-- The complete Hilbert realization of `H1Graph U`. -/
abbrev H1HilbertGraph {d : ℕ} (U : Set (Vec d)) :=
  ↥(h1HilbertSubmodule U)
namespace H1HilbertGraph
variable {d : ℕ} {U : Set (Vec d)}
noncomputable instance : SeminormedAddCommGroup (H1HilbertGraph U) := by
  exact inferInstanceAs (SeminormedAddCommGroup (h1HilbertSubmodule U))
noncomputable instance : NormedAddCommGroup (H1HilbertGraph U) := by
  exact inferInstanceAs (NormedAddCommGroup (h1HilbertSubmodule U))
noncomputable instance : NormedSpace ℝ (H1HilbertGraph U) := by
  exact inferInstanceAs (NormedSpace ℝ (h1HilbertSubmodule U))

def valueCLM :
    H1HilbertGraph U →L[ℝ] ScalarLp U (2 : ℝ≥0∞) :=
  (WithLp.fstL
      (p := 2) (𝕜 := ℝ)
      (α := ScalarLp U (2 : ℝ≥0∞))
      (β := HilbertVectorLp U (2 : ℝ≥0∞))).comp
    (h1HilbertSubmodule U).subtypeL
end H1HilbertGraph
end PDE

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Sobolev.W1p.EuclideanGradient ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Euclidean-gradient `L^p` representatives

The native gradient carrier `PDE.Vec d` has the finite-product supremum norm.
For Sobolev estimates, the gradient magnitude is instead the explicit
Euclidean norm `PDE.vecEuclideanNorm`.  This file transports native vector
fields to the internal Hilbert carrier and records the exact, factor-free
norm and `L^p` membership identities.

The coordinatewise predicate `PDE.GradMemLpOn` remains the compatibility
surface for existing developments.  Its equivalence with Hilbert-vector
`L^p` membership is exact and holds for every exponent.
-/
@[expose] public section
open scoped ENNReal
noncomputable section
namespace PDE
open MeasureTheory
/-- Reinterpret a native vector field in the internal Euclidean Hilbert
carrier. -/
def toHilbertVecField {d : ℕ} (F : Vec d → Vec d) :
    Vec d → HilbertVec d :=
  fun x => (F x).toHilbertVec

axiom gradMemLpOn_iff_memLp_toHilbertVecField
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {Du : Vec d → Vec d} :
    GradMemLpOn U p Du ↔
      MemLp (toHilbertVecField Du) p (volumeOn U)
namespace MemLpOn
/-- Promote a scalar representative on `U` to its quotient `L^p(U)` class. -/
def toScalarLp {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} (hu : MemLpOn U p u) :
    ScalarLp U p :=
  hu.toLp u

end MemLpOn
namespace GradMemLpOn
def toHilbertVectorLp {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {Du : Vec d → Vec d} (hDu : GradMemLpOn U p Du) :
    HilbertVectorLp U p :=
  (gradMemLpOn_iff_memLp_toHilbertVecField.mp hDu).toLp
    (toHilbertVecField Du)

end GradMemLpOn
end PDE

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Sobolev.W1p.RepresentativeGraph ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# From Sobolev representatives to the closed weak-gradient graph

This file packages a concrete scalar representative and its native coordinate
gradient into the quotient `L^p` product used by `PDE.W1pGraph`.  Graph
membership is proved from the literal integral characterization
`PDE.mem_weakGradientGraph_iff_integral`; no distributional condition is
hidden in a new assumption.
-/
@[expose] public section
open scoped ENNReal
noncomputable section
namespace PDE
open MeasureTheory
/-- The quotient `L^p` value-gradient pair associated with concrete
representatives. -/
def weakGradientLpPairOfRepresentatives
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du) :
    WeakGradientLpPair U p :=
  (hu.toScalarLp, hDu.toHilbertVectorLp)

/-- Concrete weak-gradient representatives determine an element of the
closed weak-gradient graph. -/
axiom weakGradientLpPairOfRepresentatives_mem_weakGradientGraph
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (hweak : HasWeakGradientOn U u Du) :
    weakGradientLpPairOfRepresentatives hu hDu ∈
      weakGradientGraph U p
def w1pGraphOfRepresentatives
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (hweak : HasWeakGradientOn U u Du) :
    W1pGraph U p :=
  ⟨weakGradientLpPairOfRepresentatives hu hDu,
    weakGradientLpPairOfRepresentatives_mem_weakGradientGraph
      hu hDu hweak⟩

namespace W1pFunction
/-- Send a concrete representative-level Sobolev function to the complete
closed-graph carrier. -/
def toW1pGraph
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1pFunction U p) :
    W1pGraph U p :=
  w1pGraphOfRepresentatives u.memLp u.gradMemLp u.hasWeakGradient

end W1pFunction
end PDE

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.PDEFoundation.Sobolev.W1p.ZeroBoundary ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Zero-boundary `W^{1,p}` as a closed graph

This file defines the canonical complete zero-boundary Sobolev carrier as the
closure, inside `W1pGraph`, of the range of actual bundled globally smooth
functions with compact support contained in the domain.  It also retains the
representative-level supported-approximation certificate used by local PDE
arguments.

## Main definitions

- `W1pFunction.SupportedSmoothApproximation`: concrete supported smooth
  approximation data for a representative.
- `smoothCompactlySupportedW1pGraphSubmodule`: the range submodule of the
  exact linear map from supported smooth test functions.
- `W10pGraph`: the closed zero-boundary graph carrier.

## Main results

- `W1pFunction.SupportedSmoothApproximation.tendsto_toW1pGraph` upgrades the
  explicit value and coordinate-gradient convergence to graph convergence.
- `W1pFunction.mem_w10pGraph_of_supportedSmoothApproximation` sends a
  representative certificate to the complete zero-boundary carrier.
- `W10pGraph.exists_tendsto_smooth` gives an actual sequence of bundled
  smooth test functions converging to every complete-carrier point.

The complete carrier is deliberately a closure in the existing `W1pGraph`;
there is no second weak-gradient relation and no extra boundary condition
hidden in a structure field.
-/
@[expose] public section
open scoped ENNReal Topology
namespace PDE
open Filter MeasureTheory
namespace WeakTestFunction
variable {d : ℕ} {U : Set (Vec d)}
/-- Smooth compactly supported weak test functions are closed under the
linear operations used by zero-boundary density. -/
instance : Zero (WeakTestFunction U) where
  zero :=
    { toFun := 0
      contDiff := contDiff_zero_fun
      hasCompactSupport := HasCompactSupport.zero
      tsupport_subset := by simp only [tsupport_zero, Set.empty_subset] }
instance : Add (WeakTestFunction U) where
  add φ ψ :=
    { toFun := φ.toFun + ψ.toFun
      contDiff := φ.contDiff.add ψ.contDiff
      hasCompactSupport := φ.hasCompactSupport.add ψ.hasCompactSupport
      tsupport_subset :=
        (tsupport_add φ.toFun ψ.toFun).trans
          (Set.union_subset φ.tsupport_subset ψ.tsupport_subset) }
instance : Neg (WeakTestFunction U) where
  neg φ :=
    { toFun := -φ.toFun
      contDiff := φ.contDiff.neg
      hasCompactSupport := φ.hasCompactSupport.neg
      tsupport_subset := by
        rw [tsupport_neg]
        exact φ.tsupport_subset }
instance : Sub (WeakTestFunction U) where
  sub φ ψ :=
    { toFun := φ.toFun - ψ.toFun
      contDiff := φ.contDiff.sub ψ.contDiff
      hasCompactSupport := φ.hasCompactSupport.sub ψ.hasCompactSupport
      tsupport_subset :=
        (tsupport_sub φ.toFun ψ.toFun).trans
          (Set.union_subset φ.tsupport_subset ψ.tsupport_subset) }
instance : SMul ℝ (WeakTestFunction U) where
  smul c φ :=
    { toFun := c • φ.toFun
      contDiff := φ.contDiff.const_smul c
      hasCompactSupport := φ.hasCompactSupport.smul_left
      tsupport_subset :=
        (tsupport_smul_subset_right (fun _ : Vec d => c) φ.toFun).trans
          φ.tsupport_subset }

axiom toFun_injective : Function.Injective (fun φ : WeakTestFunction U => φ.toFun)
instance : SMul ℕ (WeakTestFunction U) where
  smul n φ := (n : ℝ) • φ
instance : SMul ℤ (WeakTestFunction U) where
  smul n φ := (n : ℝ) • φ
instance : AddCommGroup (WeakTestFunction U) :=
  Function.Injective.addCommGroup
    (fun φ : WeakTestFunction U => φ.toFun) toFun_injective rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun φ n => by
      funext x
      change ((n : ℝ) • φ.toFun) x = (n • φ.toFun) x
      simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul])
    (fun φ n => by
      funext x
      change ((n : ℝ) • φ.toFun) x = (n • φ.toFun) x
      simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul])
/-- The underlying-function additive homomorphism transfers the standard
real module structure to bundled weak test functions. -/
def toFunAddMonoidHom : WeakTestFunction U →+ (Vec d → ℝ) where
  toFun := fun φ => φ.toFun
  map_zero' := rfl
  map_add' _ _ := rfl
instance : Module ℝ (WeakTestFunction U) :=
  Function.Injective.module ℝ toFunAddMonoidHom toFun_injective
    (fun _ _ => rfl)
end WeakTestFunction
namespace W1pFunction
variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
variable {u : W1pFunction U p}

end W1pFunction
variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
/-- The complete graph point associated to a globally smooth function with
compact support contained in `U`. -/
noncomputable def smoothCompactlySupportedW1pGraph
    [Fact (1 ≤ p)] (hU : IsOpen U) (φ : WeakTestFunction U) :
    W1pGraph U p :=
  (W1pFunction.ofContDiff hU
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph
/-- The graph image of supported smooth test functions respects addition. -/
axiom smoothCompactlySupportedW1pGraph_add
    [Fact (1 ≤ p)] (hU : IsOpen U) (φ ψ : WeakTestFunction U) :
    smoothCompactlySupportedW1pGraph (p := p) hU (φ + ψ) =
      smoothCompactlySupportedW1pGraph (p := p) hU φ +
        smoothCompactlySupportedW1pGraph (p := p) hU ψ
/-- The graph image of supported smooth test functions respects real scalar
multiplication. -/
axiom smoothCompactlySupportedW1pGraph_smul
    [Fact (1 ≤ p)] (hU : IsOpen U) (c : ℝ) (φ : WeakTestFunction U) :
    smoothCompactlySupportedW1pGraph (p := p) hU (c • φ) =
      c • smoothCompactlySupportedW1pGraph (p := p) hU φ
/-- The exact linear map from bundled smooth compactly supported test
functions to the complete weak-gradient graph. -/
noncomputable def smoothCompactlySupportedW1pGraphLinearMap
    [Fact (1 ≤ p)] (hU : IsOpen U) :
    WeakTestFunction U →ₗ[ℝ] W1pGraph U p where
  toFun := smoothCompactlySupportedW1pGraph (p := p) hU
  map_add' := smoothCompactlySupportedW1pGraph_add hU
  map_smul' := smoothCompactlySupportedW1pGraph_smul hU

namespace W1pFunction
variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
end W1pFunction
namespace W10pGraph
variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
end W10pGraph
end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Hilbert realization of spatial `H¹₀`

This module defines spatial `H¹₀(Ω)` as the closure in the Hilbert realization
of the weak-gradient graph of the image of actual bundled smooth compactly
supported test functions.  It then proves that this carrier agrees with the
existing maximum-norm graph realization from `PDEFoundation`.

No density result for the value map into spatial `L²` is asserted here.
-/
@[expose] public section
open Filter
open scoped ENNReal RealInnerProductSpace Topology
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
variable {d : ℕ} {Ω : Set (PDE.Vec d)}
/-- The continuous linear equivalence from the Hilbert-norm weak-gradient
graph to the corresponding maximum-norm graph. -/
noncomputable def h1HilbertGraphContinuousLinearEquiv
    (Ω : Set (PDE.Vec d)) :
    PDE.H1HilbertGraph Ω ≃L[ℝ] PDE.H1Graph Ω :=
  (PDE.h1HilbertAmbientEquiv Ω).ofSubmodule'
    (PDE.weakGradientGraph Ω (2 : ℝ≥0∞)).toSubmodule
noncomputable def smoothCompactlySupportedH1HilbertGraphLinearMap
    (hΩ : IsOpen Ω) :
    PDE.WeakTestFunction Ω →ₗ[ℝ] PDE.H1HilbertGraph Ω :=
  (h1HilbertGraphContinuousLinearEquiv Ω).symm.toLinearMap.comp
    (PDE.smoothCompactlySupportedW1pGraphLinearMap
      (p := (2 : ℝ≥0∞)) hΩ)
/-- The submodule of Hilbert-graph points coming from actual bundled smooth
compactly supported test functions. -/
noncomputable def smoothCompactlySupportedH1HilbertGraphSubmodule
    (hΩ : IsOpen Ω) :
    Submodule ℝ (PDE.H1HilbertGraph Ω) :=
  LinearMap.range (smoothCompactlySupportedH1HilbertGraphLinearMap hΩ)
/-- The closed Hilbert-graph submodule defining spatial `H¹₀`. -/
noncomputable def h10HilbertGraphClosedSubmodule
    (hΩ : IsOpen Ω) :
    ClosedSubmodule ℝ (PDE.H1HilbertGraph Ω) :=
  (smoothCompactlySupportedH1HilbertGraphSubmodule hΩ).closure
/-- The complete Hilbert realization of spatial `H¹₀(Ω)`. -/
noncomputable abbrev H10HilbertGraph (hΩ : IsOpen Ω) :=
  ↥((h10HilbertGraphClosedSubmodule hΩ).toSubmodule)
noncomputable instance (hΩ : IsOpen Ω) :
    SeminormedAddCommGroup (H10HilbertGraph hΩ) := by
  exact inferInstanceAs
    (SeminormedAddCommGroup
      ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))
noncomputable instance (hΩ : IsOpen Ω) :
    NormedAddCommGroup (H10HilbertGraph hΩ) := by
  exact inferInstanceAs
    (NormedAddCommGroup ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))
noncomputable instance (hΩ : IsOpen Ω) :
    NormedSpace ℝ (H10HilbertGraph hΩ) := by
  exact inferInstanceAs
    (NormedSpace ℝ ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))

/-- The continuous scalar-value map from spatial `H¹₀` to spatial `L²`. -/
noncomputable def valueCLM (hΩ : IsOpen Ω) :
    H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  PDE.H1HilbertGraph.valueCLM.comp
    (h10HilbertGraphClosedSubmodule hΩ).toSubmodule.subtypeL
end HypoellipticAleksandrov.Parabolic.Dirichlet

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_a57951cdfb580b1cc97f_TimeScalarEnergy ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Scalar reverse-time energy representatives

This module constructs the scalar no-defect energy representative attached to
a reverse-time Gelfand weak derivative.  It deliberately does not construct a
Hilbert-valued trace or assert a PDE solvability result.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

private axiom abs_sqNorm_valueCLM_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x y : H10HilbertGraph hΩ) :
    |‖valueCLM hΩ x‖ ^ 2 - ‖valueCLM hΩ y‖ ^ 2| ≤
      ‖valueCLM hΩ‖ ^ 2 * ‖x - y‖ ^ 2 +
        2 * ‖valueCLM hΩ‖ ^ 2 * ‖y‖ * ‖x - y‖
private axiom integral_mul_norm_le_sqrt_mul_sqrt
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure ℝ} (f : ℝ → E) (g : ℝ → F)
    (hf : MemLp f (2 : ℝ≥0∞) μ) (hg : MemLp g (2 : ℝ≥0∞) μ) :
    ∫ t, ‖f t‖ * ‖g t‖ ∂μ ≤
      √(∫ t, ‖f t‖ ^ 2 ∂μ) * √(∫ t, ‖g t‖ ^ 2 ∂μ)
private theorem tendsto_integral_abs_valueSq_of_sqNorm
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (μ : Measure ℝ) (u : ℝ → H10HilbertGraph hΩ)
    (uh : ℝ → ℝ → H10HilbertGraph hΩ)
    (hu : MemLp u (2 : ℝ≥0∞) μ)
    (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) (2 : ℝ≥0∞) μ)
    (hU : Tendsto (fun h : ℝ => ∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t,
      |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  let C : ℝ := ‖valueCLM hΩ‖ ^ 2
  have hUsqrt : Tendsto (fun h : ℝ =>
      √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hU.sqrt
  have hfirst : Tendsto (fun h : ℝ =>
      C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hU
  have hsecond : Tendsto (fun h : ℝ =>
      2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ) *
        √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ =>
        2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ))
        (𝓝[>] 0) (𝓝 (2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ)) : Filter ℝ) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hconst.mul hUsqrt
  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => abs_nonneg _
  · filter_upwards [huh] with h huh
    have hdu : MemLp (fun t => uh h t - u t) (2 : ℝ≥0∞) μ := huh.sub hu
    have hLuh : MemLp (fun t => valueCLM hΩ (uh h t)) (2 : ℝ≥0∞) μ :=
      huh.continuousLinearMap_comp (valueCLM hΩ)
    have hLu : MemLp (fun t => valueCLM hΩ (u t)) (2 : ℝ≥0∞) μ :=
      hu.continuousLinearMap_comp (valueCLM hΩ)
    have hleft : Integrable (fun t =>
        |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2|) μ := by
      simpa only [Real.norm_eq_abs, Pi.sub_def] using
        ((hLuh.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).sub
          (hLu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).norm
    have hterm1 : Integrable (fun t =>
        C * ‖uh h t - u t‖ ^ 2) μ :=
      (hdu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
    have hterm2 : Integrable (fun t =>
        2 * C * ‖u t‖ * ‖uh h t - u t‖) μ :=
      by
        apply ((hu.norm).integrable_mul hdu.norm).const_mul (2 * C) |>.congr
        filter_upwards with t
        change 2 * C *
          ((fun x => ‖u x‖) * fun x => ‖uh h x - u x‖) t = _
        simp only [Pi.mul_apply]
        ring
    have hpoint : ∀ t : ℝ,
        |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ≤
          C * ‖uh h t - u t‖ ^ 2 + 2 * C * ‖u t‖ * ‖uh h t - u t‖ := by
      intro t
      simpa only [C] using abs_sqNorm_valueCLM_sub_le hΩ (uh h t) (u t)
    have hmono := integral_mono hleft (hterm1.add hterm2) hpoint
    have hholder := integral_mul_norm_le_sqrt_mul_sqrt
      u (fun t => uh h t - u t) hu hdu
    have hterm2_eq : (∫ t,
        2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ) =
        2 * C *
          (∫ t, ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
      rw [show (fun t : ℝ =>
          2 * C * ‖u t‖ * ‖uh h t - u t‖) =
          fun t => (2 * C) *
            (‖u t‖ * ‖uh h t - u t‖) by
            funext t
            ring, integral_const_mul]
    calc
      (∫ t, |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ) ≤
          ∫ t, C * ‖uh h t - u t‖ ^ 2 +
            2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ := hmono
      _ = C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
          (∫ t, 2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
            rw [integral_add hterm1 hterm2, integral_const_mul]
      _ = C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
          2 * C *
            (∫ t, ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
            rw [hterm2_eq]
      _ ≤ C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
          2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ) *
            √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) := by
            apply add_le_add_right
            simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_left hholder (by positivity : 0 ≤ 2 * C)
  · simpa only [add_zero] using hfirst.add hsecond
end HypoellipticAleksandrov.Parabolic.Dirichlet
