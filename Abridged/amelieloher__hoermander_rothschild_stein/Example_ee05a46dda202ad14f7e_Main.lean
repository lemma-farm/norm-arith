module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.NhdsSet
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.VectorField

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.B.Defs ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace Hormander.B
abbrev Carrier (N : ℕ) := EuclideanSpace ℝ (Fin N)
abbrev TestFunction (N : ℕ) := SchwartzMap (Carrier N) ℂ
abbrev Tempered (N : ℕ) := TemperedDistribution (Carrier N) ℂ
abbrev Operator (N : ℕ) := TestFunction N →ₗ[ℂ] TestFunction N
local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
noncomputable def sobolevSpace {N : ℕ} (s : ℝ) (u : TestFunction N) :
    BesselPotentialSpace (Carrier N) ℂ s 2 :=
  (SchwartzMap.memSobolev (s := s) (p := 2) u).toBesselPotentialSpace
noncomputable def sobolevNorm {N : ℕ} (s : ℝ) (u : TestFunction N) : ℝ :=
  ‖sobolevSpace s u‖
/-- The order predicate on complex-linear operators on Schwartz functions. -/
def HasOrder {N : ℕ} (m : ℝ) (T : Operator N) : Prop :=
  ∀ s : ℝ, ∃ C : NNReal, ∀ u : TestFunction N,
    sobolevNorm s (T u) ≤ (C : ℝ) * sobolevNorm (s + m) u

/-- The bilinear integral pairing used to define transposes on Schwartz functions. -/
def bilinearPairing {N : ℕ} (u v : TestFunction N) : ℂ :=
  ∫ x, u x * v x
/-- The algebraic identity that makes `Tt` the bilinear transpose of `T`. -/
def HasBilinearTranspose {N : ℕ} (T Tt : Operator N) : Prop :=
  ∀ u v : TestFunction N, bilinearPairing (T u) v = bilinearPairing u (Tt v)
/-- A real Schwartz vector field in coordinate form on the Euclidean carrier. -/
abbrev RealSchwartzVectorField (N : ℕ) := Fin N → SchwartzMap (Carrier N) ℝ
/-- The Schwartz multiplier associated to a complex Schwartz coefficient. -/
def multiplierOperator {N : ℕ} (g : SchwartzMap (Carrier N) ℂ) : Operator N :=
  (SchwartzMap.smulLeftCLM ℂ g).toLinearMap
/-- Complexify a real Schwartz coefficient while retaining its Schwartz structure. -/
def complexifyRealSchwartz {N : ℕ} (g : SchwartzMap (Carrier N) ℝ) :
    SchwartzMap (Carrier N) ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM g
/-- Multiplication by a real Schwartz coefficient on complex-valued Schwartz functions. -/
def realMultiplierOperator {N : ℕ} (g : SchwartzMap (Carrier N) ℝ) : Operator N :=
  multiplierOperator (complexifyRealSchwartz g)
/-- A coordinate directional derivative on Schwartz functions. -/
def coordinateDerivative {N : ℕ} (i : Fin N) : Operator N :=
  (LineDeriv.lineDerivOpCLM ℂ (TestFunction N)
    (EuclideanSpace.single i (1 : ℝ))).toLinearMap
/-- The differential operator of a real Schwartz vector field on Schwartz functions. -/
def vectorFieldOperator {N : ℕ} (V : RealSchwartzVectorField N) : Operator N :=
  ∑ i : Fin N, (realMultiplierOperator (V i)).comp (coordinateDerivative i)

/-- Extend an operator to tempered distributions by precomposition with its transpose. -/
def transposeExtension {N : ℕ}
    (Tt : TestFunction N →L[ℂ] TestFunction N) : Tempered N →L[ℂ] Tempered N :=
  PointwiseConvergenceCLM.precomp ℂ Tt

end Hormander.B

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.A.Fourier ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open LineDeriv MeasureTheory Real SchwartzMap
open scoped FourierTransform ComplexInnerProductSpace
namespace Hormander.A
/-- The Euclidean carrier used by the Fourier and Sobolev modules. -/
abbrev Carrier (N : ℕ) := EuclideanSpace ℝ (Fin N)

end Hormander.A

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.A.SobolevScale ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap TemperedDistribution
open scoped BesselPotentialSpace BoundedContinuousFunction ComplexInnerProductSpace FourierTransform
namespace Hormander.A
/-- The project's Sobolev space is Mathlib's bundled Bessel-potential space at p = 2. -/
abbrev SobolevSpace (N : ℕ) (s : ℝ) :=
  BesselPotentialSpace (Carrier N) ℂ s 2

end Hormander.A

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.B.Order ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace Hormander.B
local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

axiom sobolevNorm_nonneg {N : ℕ} (s : ℝ) (u : TestFunction N) :
    0 ≤ sobolevNorm s u

end Hormander.B

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.B.Fractional.DerivativeFacts ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal
namespace Hormander.B
variable {N : ℕ}
/-! Algebra of the commutator convention `[A,B] = A∘B − B∘A`. -/

/-! Coordinate derivatives. -/

/-! Order facts. -/

/-- Multiplication by a Schwartz function has order zero. -/
axiom hasOrder_multiplierOperator_zero (g : TestFunction N) :
    HasOrder 0 (multiplierOperator g)

end Hormander.B

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.A.Mollifier.Defs ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open ContinuousLinearMap MeasureTheory SchwartzMap TemperedDistribution
open scoped Convolution FourierTransform
namespace Hormander.A
/-- A symmetric bump whose support lies in the closed half-radius ball. -/
def jBump (N : ℕ) : ContDiffBump (0 : Carrier N) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
/-- The real compactly supported kernel used for mollification. -/
def J (N : ℕ) : 𝓢(Carrier N, ℝ) := by
  exact ((jBump N).hasCompactSupport_normed (μ := volume)).toSchwartzMap
    (jBump N).contDiff_normed
/-- The complexification of the real mollifier. -/
def Jc (N : ℕ) : 𝓢(Carrier N, ℂ) := by
  let f : Carrier N → ℂ := fun x ↦ (J N x : ℂ)
  have hsupp : HasCompactSupport f := by
    rw [hasCompactSupport_def]
    have hs : Function.support f = Function.support ((jBump N).normed volume) := by
      ext x
      simp [f, J, jBump]
    rw [hs]
    exact (jBump N).hasCompactSupport_normed (μ := volume)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) f := by
    exact Complex.ofRealCLM.contDiff.comp (jBump N).contDiff_normed
  exact hsupp.toSchwartzMap hsm

/-- The rescaled Schwartz mollifier `δ⁻ᴺ J(x / δ)`. -/
def Jδ (N : ℕ) (δ : ℝ) (hδ : 0 < δ) : 𝓢(Carrier N, ℂ) :=
  (δ ^ N : ℝ)⁻¹ •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.smulLeft (Units.mk0 δ⁻¹ (inv_ne_zero (ne_of_gt hδ))))
      (Jc N)

/-- Convolution by the even kernel on Schwartz tests. -/
def SδSchwartz (N : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    𝓢(Carrier N, ℂ) →L[ℂ] 𝓢(Carrier N, ℂ) :=
  SchwartzMap.convolution (lsmul ℂ ℂ) (Jδ N δ hδ)
/-- Reflection of a Schwartz kernel. -/
def reflectedSchwartz {N : ℕ} (K : 𝓢(Carrier N, ℂ)) : 𝓢(Carrier N, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) K
/-- The test-function operator used to define convolution of a tempered distribution. -/
def temperedConvolutionTests {N : ℕ} (K : 𝓢(Carrier N, ℂ)) :
    𝓢(Carrier N, ℂ) →L[ℂ] 𝓢(Carrier N, ℂ) :=
  SchwartzMap.convolution (lsmul ℂ ℂ) (reflectedSchwartz K)
/-- Convolution of a tempered distribution by a Schwartz kernel, defined by transposition. -/
def temperedConvolution {N : ℕ} (T : 𝓢'(Carrier N, ℂ)) (K : 𝓢(Carrier N, ℂ)) :
    𝓢'(Carrier N, ℂ) :=
  PointwiseConvergenceCLM.precomp _ (temperedConvolutionTests K) T

/-- The transpose convolution of a tempered distribution with `Jδ`. -/
def Sδ (N : ℕ) (δ : ℝ) (hδ : 0 < δ) (T : 𝓢'(Carrier N, ℂ)) :
    𝓢'(Carrier N, ℂ) :=
  temperedConvolution T (Jδ N δ hδ)
end Hormander.A

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.B.Mollifier.Symbol ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace Hormander.B
variable {N : ℕ}
/-- The mollifier on Schwartz functions as a linear operator. -/
def mollOp (N : ℕ) (δ : ℝ) (hδ : 0 < δ) : Operator N :=
  (Hormander.A.SδSchwartz N δ hδ).toLinearMap

end Hormander.B

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.B.Mollifier.FirstCommutator ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal
namespace Hormander.B
variable {N : ℕ}
/-- The positive mollifier scales. -/
abbrev PosScale := {δ : ℝ // 0 < δ}

end Hormander.B

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.D.Defs ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
open Filter Topology
namespace Hormander.D
/-- The outer cutoff is one on an open neighborhood of the support of the inner cutoff. -/
def cutoffPrecedes {N : ℕ} (η η' : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
    ContDiff ℝ (⊤ : ℕ∞) η' ∧ HasCompactSupport η' ∧
    ∀ᶠ x in 𝓝ˢ (tsupport η), η' x = 1

end Hormander.D

end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.C.C9Bridges ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open SchwartzMap
open Hormander.B
namespace Hormander.C
/-- Schwartz coordinate fields associated to compactly supported smooth vector fields. -/
def c9SchwartzVectorField {k N : ℕ}
    (X : Fin (k + 1) → Carrier N → Carrier N)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i)) :
    Fin (k + 1) → RealSchwartzVectorField N := fun i j => by
  have hcoordSupport : Function.support (fun x => X i x j) ⊆ tsupport (X i) := by
    intro x hx
    have hnonzero : X i x j ≠ 0 := by simpa using hx
    apply subset_tsupport
    intro hzero
    apply hnonzero
    simp [hzero]
  have hcoordCompact : HasCompactSupport (fun x => X i x j) := (hXc i).mono' hcoordSupport
  have hcoordSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => X i x j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp (hX i)
  exact hcoordCompact.toSchwartzMap hcoordSmooth

/-- The real Schwartz representative of a compactly supported smooth coefficient. -/
def c9SchwartzMultiplier {N : ℕ} (c : Carrier N → ℝ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c) :
    SchwartzMap (Carrier N) ℝ := hcc.toSchwartzMap hc

end Hormander.C
end

end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.C.Energy.Estimate ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate
namespace Hormander.C
open Hormander.B
variable {N : ℕ}

/-- The operator `L = ∑_{j=1}^k X_j² + X_0 + c`. -/
def diffusionOperator {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) : Operator N :=
  (∑ i : Fin k, (vectorFieldOperator (X i.succ)).comp (vectorFieldOperator (X i.succ))) +
    vectorFieldOperator (X 0) + realMultiplierOperator c

end Hormander.C

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.B.Extension.Extension ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate FourierTransform
namespace Hormander.B

/-- The transposed operator as a continuous linear map on `𝓢`, given its continuity. -/
def continuousTranspose {N : ℕ} (Tt : Operator N) (hc : Continuous Tt) :
    TestFunction N →L[ℂ] TestFunction N :=
  { Tt with cont := hc }
/-- The transposition extension `T'` to tempered distributions, `⟨T'u, φ⟩ = ⟨u, T^t φ⟩`. -/
def tempExtension {N : ℕ} (Tt : Operator N) (hc : Continuous Tt) : Tempered N →L[ℂ] Tempered N :=
  transposeExtension (continuousTranspose Tt hc)

end Hormander.B

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.B.Extension.Localized ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate FourierTransform
namespace Hormander.B

/-- Multiplication of a tempered distribution by a real Schwartz cutoff `ζ`. -/
def cutoffDistr {N : ℕ} (ζ : SchwartzMap (Carrier N) ℝ) : Tempered N →L[ℂ] Tempered N :=
  TemperedDistribution.smulLeftCLM ℂ (⇑(complexifyRealSchwartz ζ))

end Hormander.B

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.B.Extension.Continuity ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate FourierTransform
namespace Hormander.B

/-- The operator has a bilinear transpose, and both are continuous on `𝓢`. -/
def HasContinuousTranspose {N : ℕ} (T : Operator N) : Prop :=
  ∃ Tt : Operator N, HasBilinearTranspose T Tt ∧
    Continuous (fun u : TestFunction N => T u) ∧ Continuous (fun u : TestFunction N => Tt u)

end Hormander.B

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.Defs.VectorFieldOp ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open SchwartzMap
namespace Hormander
/-- The first-order operator `Σᵢ Vⁱ ∂ᵢ` of a vector field `V` on `ℝᴺ`, acting on complex tempered
distributions: `∂ᵢ` is Mathlib's distributional directional derivative along the `i`-th unit
vector and `Vⁱ` acts by `TemperedDistribution.smulLeftCLM`. This is the action of `V` on `𝓢'`
for every `V` whose coordinates have temperate growth (in particular for `C_c^∞` fields, the
only case used). -/
def vectorFieldOp {N : ℕ} (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :
    𝓢'(EuclideanSpace ℝ (Fin N), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin N), ℂ) :=
  ∑ i : Fin N,
    (TemperedDistribution.smulLeftCLM ℂ (fun x => ((V x i : ℝ) : ℂ))).comp
      (LineDeriv.lineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)
        (EuclideanSpace.single i (1 : ℝ)))
end Hormander

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.Defs.HormanderOp ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open SchwartzMap
namespace Hormander
/-- The operator `L = Σ_{i=1}^k Xᵢ² + X₀ + c` acting on complex tempered distributions on `ℝᴺ`,
built from `vectorFieldOp` and multiplication by `c`. Meaningful for coefficients with temperate
growth (in particular `C_c^∞` coefficients, the only case used). -/
def hormanderOp {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ) :
    𝓢'(EuclideanSpace ℝ (Fin N), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin N), ℂ) :=
  (∑ i : Fin k, (vectorFieldOp (X i.succ)).comp (vectorFieldOp (X i.succ))) +
    vectorFieldOp (X 0) +
    TemperedDistribution.smulLeftCLM ℂ (fun x => ((c x : ℝ) : ℂ))
end Hormander

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.OneStep.ExtAlgebra ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open MeasureTheory SchwartzMap
@[expose] public section
noncomputable section
namespace Hormander.E
open Hormander.B
/-- An operator on `𝓢` together with a continuous bilinear transpose, so that it extends to
`𝓢'` by transposition. -/
structure ExtOp (N : ℕ) where
  op : Operator N
  tr : Operator N
  isTr : HasBilinearTranspose op tr
  cont : Continuous (fun u : TestFunction N => tr u)
variable {N : ℕ}
/-- The transposition extension to tempered distributions. -/
def ExtOp.ext (T : ExtOp N) : Tempered N →L[ℂ] Tempered N := tempExtension T.tr T.cont

/-- Smart constructor from an operator with continuous transpose. -/
def ExtOp.ofTranspose (T : Operator N) (h : HasContinuousTranspose T) : ExtOp N where
  op := T
  tr := h.choose
  isTr := h.choose_spec.1
  cont := h.choose_spec.2.2

end Hormander.E

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.OneStepFinal.Basic ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.E
open Hormander.B
variable {N : ℕ}
/-! ### Closure of the class of operators with continuous transpose -/

/-- The transposition extension of an operator with continuous transpose (zero otherwise). -/
def Eop (T : Operator N) : Tempered N →L[ℂ] Tempered N := by
  classical
  exact if h : HasContinuousTranspose T then (ExtOp.ofTranspose T h).ext else 0

axiom Eop_test {T : Operator N} (hT : HasContinuousTranspose T) (φ : TestFunction N) :
    Eop T (φ : Tempered N) = ((T φ : TestFunction N) : Tempered N)
/-! ### Bounded distributions -/
/-- `g` is (the distribution of) an element of `H^s` of norm at most `B`. -/
def Bdd (s : ℝ) (g : Tempered N) (B : ℝ) : Prop :=
  ∃ v : Hormander.A.SobolevSpace N s, v.toDistr = g ∧ ‖v‖ ≤ B
axiom Bdd.mono {s : ℝ} {g : Tempered N} {B B' : ℝ} (h : Bdd s g B) (hB : B ≤ B') :
    Bdd s g B'

axiom Bdd.of_test (s : ℝ) (φ : TestFunction N) : Bdd s (φ : Tempered N) (sobolevNorm s φ)
axiom Bdd.test_le {s : ℝ} {φ : TestFunction N} {B : ℝ} (h : Bdd s (φ : Tempered N) B) :
    sobolevNorm s φ ≤ B

/-- Global transfer. -/
axiom Eop_bdd_global {T : Operator N} (hT : HasContinuousTranspose T) {m s r' : ℝ}
    (hr : s + m = r') {C : NNReal}
    (hC : ∀ φ : TestFunction N, sobolevNorm s (T φ) ≤ (C : ℝ) * sobolevNorm r' φ)
    (w : Hormander.A.SobolevSpace N r') :
    Bdd s (Eop T w.toDistr) ((C : ℝ) * ‖w‖)

end Hormander.E

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.OneStepFinal.Operators ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.E
open Hormander.B
variable {N : ℕ}

axiom hct_realMult (ζ : SchwartzMap (Carrier N) ℝ) :
    HasContinuousTranspose (realMultiplierOperator ζ)

axiom hct_diffusion {k : ℕ} (Vs : Fin (k + 1) → RealSchwartzVectorField N)
    (cs : SchwartzMap (Carrier N) ℝ) :
    HasContinuousTranspose (Hormander.C.diffusionOperator Vs cs)

axiom Eop_realMult (ζ : SchwartzMap (Carrier N) ℝ) :
    Eop (realMultiplierOperator ζ) = cutoffDistr ζ
/-- The distributional operator `hormanderOp X c` is the extension of the Schwartz-side
`diffusionOperator` of the realization. -/
axiom Eop_diffusion_eq {k : ℕ} (X : Fin (k + 1) → Carrier N → Carrier N) (c : Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c) :
    Eop (Hormander.C.diffusionOperator (Hormander.C.c9SchwartzVectorField X hX hXc)
      (Hormander.C.c9SchwartzMultiplier c hc hcc)) = Hormander.hormanderOp X c
end Hormander.E

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.OneStepFinal.Realize ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap Metric
open scoped FourierTransform
namespace Hormander.E
open Hormander.B
variable {N : ℕ}

/-- The mollification of a localized distribution is again localized. -/
axiom cutoffDistr_Sδ_fix (τ ψ : SchwartzMap (Carrier N) ℝ) (v : Tempered N)
    (hτ : cutoffDistr τ v = v) (δ : ℝ) (hδ : 0 < δ)
    (hψ : ∀ x ∈ tsupport (τ : Carrier N → ℝ), ∀ y, ‖x - y‖ ≤ δ / 2 → ψ y = 1) :
    cutoffDistr ψ (Hormander.A.Sδ N δ hδ v) = Hormander.A.Sδ N δ hδ v
/-- Existence of a uniform mollification radius. -/
axiom exists_mollifier_radius {τ ψ : Carrier N → ℝ} (h : Hormander.D.cutoffPrecedes τ ψ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ x ∈ tsupport τ, ∀ y, ‖x - y‖ ≤ δ₀ → ψ y = 1
/-- Realization of a mollified localized `H^s` distribution as a Schwartz function. -/
axiom exists_testFunction_Sδ {s : ℝ} (τ ψ : SchwartzMap (Carrier N) ℝ)
    (hψc : HasCompactSupport (ψ : Carrier N → ℝ)) (v : Tempered N)
    (hv : TemperedDistribution.MemSobolev s 2 v) (hτ : cutoffDistr τ v = v)
    (δ : ℝ) (hδ : 0 < δ)
    (hψ : ∀ x ∈ tsupport (τ : Carrier N → ℝ), ∀ y, ‖x - y‖ ≤ δ / 2 → ψ y = 1) :
    ∃ g : TestFunction N, (g : Tempered N) = Hormander.A.Sδ N δ hδ v
end Hormander.E

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.OneStepFinal.EnergyQ ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.E
open Hormander.B
variable {N : ℕ}
axiom tsupport_realMult_subset (θ : SchwartzMap (Carrier N) ℝ) (φ : TestFunction N) :
    tsupport (realMultiplierOperator θ φ : Carrier N → ℂ) ⊆ tsupport (θ : Carrier N → ℝ)
axiom realMult_eq_self_of_tsupport (ρ : SchwartzMap (Carrier N) ℝ) (ψ : TestFunction N)
    (h : ∀ x ∈ tsupport (ψ : Carrier N → ℂ), ρ x = 1) : realMultiplierOperator ρ ψ = ψ

end Hormander.E

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.D.Cutoffs ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
open Filter Topology Set
namespace Hormander.D
variable {N : ℕ}

/-- Nested smooth cutoffs compose: if the middle cutoff is one near the first support and
the outer cutoff is one near the middle support, it is one near the first support. -/
axiom cutoffPrecedes.trans {η₁ η₂ η₃ : EuclideanSpace ℝ (Fin N) → ℝ}
    (h₁₂ : cutoffPrecedes η₁ η₂) (h₂₃ : cutoffPrecedes η₂ η₃) :
    cutoffPrecedes η₁ η₃
end Hormander.D

end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.OneStepFinal.EnergyLimit ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate
namespace Hormander.E
open Hormander.B
variable {N : ℕ}
/-- (BB Lemma 5.21, converse compactness for mollification), as an explicit hypothesis:
a tempered distribution all of whose mollifications at small scales lie in `H^s` with norm at
most `C` lies in `H^s` with norm at most `C`. -/
def MollifierConverse (N : ℕ) : Prop :=
  ∀ (s : ℝ) (T : Tempered N) (C δ₀ : ℝ), 0 < δ₀ →
    (∀ (δ : ℝ) (hδ : 0 < δ), δ < δ₀ →
      ∃ f : Hormander.A.SobolevSpace N s, f.toDistr = Hormander.A.Sδ N δ hδ T ∧ ‖f‖ ≤ C) →
    ∃ f : Hormander.A.SobolevSpace N s, f.toDistr = T ∧ ‖f‖ ≤ C

/-- The plateau property of a cutoff relation, pointwise. -/
axiom plateau_of_precedes {f g : Carrier N → ℝ} (h : Hormander.D.cutoffPrecedes f g) :
    ∀ x ∈ tsupport f, g x = 1
axiom Bdd.of_memSobolev {s : ℝ} {g : Tempered N} (v : Hormander.A.SobolevSpace N s)
    (hv : v.toDistr = g) : TemperedDistribution.MemSobolev s 2 g

end Hormander.E

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.OneStepFinal.LzBound ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.E
open Hormander.B
variable {N : ℕ}
/-- The regularized localization `B_δ = S_δ M_{η₁}`. -/
def bOp (η₁ : SchwartzMap (Carrier N) ℝ) (δ : ℝ) (hδ : 0 < δ) : Operator N :=
  (mollOp N δ hδ).comp (realMultiplierOperator η₁)

/-- `B_δ g ∈ H^s` for `ζ g ∈ H^s`. -/
axiom bdd_bOp (η₁ ζ : SchwartzMap (Carrier N) ℝ)
    (hz : ∀ x ∈ tsupport (η₁ : Carrier N → ℝ), ζ x = 1) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (g : Tempered N) (w : Hormander.A.SobolevSpace N s),
      w.toDistr = cutoffDistr ζ g → Bdd s (Eop (bOp η₁ d.1 d.2) g) (C * ‖w‖)

/-- the finite bound on `‖L z_δ‖_{H^r}` for `z_δ = S_δ(η₁ u)`. -/
axiom Lz_bound {k : ℕ} (Vs : Fin (k + 1) → RealSchwartzVectorField N)
    (cs η₁ θ ρ η₂ : SchwartzMap (Carrier N) ℝ)
    (h₁ : Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ) (θ : Carrier N → ℝ))
    (h₂ : Hormander.D.cutoffPrecedes (θ : Carrier N → ℝ) (ρ : Carrier N → ℝ))
    (h₃ : Hormander.D.cutoffPrecedes (ρ : Carrier N → ℝ) (η₂ : Carrier N → ℝ))
    (hA6 : MollifierConverse N) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : PosScale) (u : Tempered N) (a b : Hormander.A.SobolevSpace N r),
      a.toDistr = cutoffDistr η₂ u →
      b.toDistr = cutoffDistr η₂ (Eop (Hormander.C.diffusionOperator Vs cs) u) →
      Bdd r (Eop (Hormander.C.diffusionOperator Vs cs) (Eop (bOp η₁ d.1 d.2) u))
        (C * (‖a‖ + ‖b‖))
end Hormander.E

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.OneStepFinal.FinalAux ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.E
open Hormander.B
variable {N : ℕ}
axiom testToTempered_injective' {φ ψ : TestFunction N} (h : (φ : Tempered N) = ψ) : φ = ψ

/-- The five-fold chain `η₁ ≺ χ ≺ θ ≺ ρ ≺ η₂` of Schwartz cutoffs. -/
axiom exists_schwartz_chain {η₁ η₂ : SchwartzMap (Carrier N) ℝ}
    (h : Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ χ θ ρ : SchwartzMap (Carrier N) ℝ,
      Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ) (χ : Carrier N → ℝ) ∧
      Hormander.D.cutoffPrecedes (χ : Carrier N → ℝ) (θ : Carrier N → ℝ) ∧
      Hormander.D.cutoffPrecedes (θ : Carrier N → ℝ) (ρ : Carrier N → ℝ) ∧
      Hormander.D.cutoffPrecedes (ρ : Carrier N → ℝ) (η₂ : Carrier N → ℝ)
/-- The diffusion operator is local. -/
axiom diffusion_apply_eq_zero {k : ℕ} (Vs : Fin (k + 1) → RealSchwartzVectorField N)
    (cs : SchwartzMap (Carrier N) ℝ) (g : TestFunction N) (x : Carrier N)
    (hx : x ∉ tsupport (g : Carrier N → ℂ)) :
    Hormander.C.diffusionOperator Vs cs g x = 0
end Hormander.E

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.CutoffChains ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
open Set
namespace Hormander.E
variable {N : ℕ}
/-- A nested cutoff pair has ordered topological supports. -/
axiom cutoffPrecedes_tsupport_subset
    {η η' : EuclideanSpace ℝ (Fin N) → ℝ}
    (hη : Hormander.D.cutoffPrecedes η η') : tsupport η ⊆ tsupport η'
end Hormander.E

end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.Interface.LieWord ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Hormander.Interface
/-- An iterated Lie word in the drift and squared vector-field generators. -/
inductive LieWord (k : ℕ) where
  | generator : Fin (k + 1) → LieWord k
  | bracket : LieWord k → LieWord k → LieWord k
end Hormander.Interface

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.Defs.LieWordEval ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace Hormander
open Hormander.Interface
/-- Evaluation of a Lie word on vector fields over an arbitrary real normed space `E`: the same
recursion as `Hormander.Interface.LieWord.eval`, with `Fin N → ℝ` replaced by `E`. -/
def lieWordEval {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Fin (k + 1) → E → E) : LieWord k → E → E
  | .generator i => X i
  | .bracket p q => VectorField.lieBracket ℝ (lieWordEval X p) (lieWordEval X q)
end Hormander

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.Defs.LieWordLength ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
namespace Hormander
open Hormander.Interface
/-- The ordinary length of a Lie word: its number of generator leaves (the drift `X 0`
counts once, like every other generator). -/
def lieWordLength {k : ℕ} : LieWord k → ℕ
  | .generator _ => 1
  | .bracket p q => lieWordLength p + lieWordLength q
end Hormander

end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.OneStepFinal.Final ====
public section
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.E
open Hormander.B
/-- The localized gain statement `Hormander.D.localized_gain`, as a
hypothesis ranging over all of its binders. -/
def D1Hypothesis : Prop :=
  ∀ {k N : ℕ}
    (X : Fin (k + 1) → Hormander.B.Carrier N → Hormander.B.Carrier N)
    (c : Hormander.B.Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcc : HasCompactSupport c)
    {K U : Set (Hormander.B.Carrier N)}
    (_hK : IsCompact K) (_hU : IsOpen U) (_hKU : K ⊆ U)
    (s : ℕ) (_hs : 1 ≤ s)
    (w : Fin N → Hormander.Interface.LieWord k)
    (_hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (_hw : ∀ x ∈ U,
      LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x))
    (η₁ η₂ : SchwartzMap (Hormander.B.Carrier N) ℝ)
    (_hη : Hormander.D.cutoffPrecedes (η₁ : Hormander.B.Carrier N → ℝ)
      (η₂ : Hormander.B.Carrier N → ℝ))
    (_hη₂K : tsupport (η₂ : Hormander.B.Carrier N → ℝ) ⊆ K)
    (σ : ℝ),
    ∃ C : ℝ, ∀ u : Hormander.B.TestFunction N,
      Hormander.B.sobolevNorm (σ + (2 : ℝ) / 4 ^ s)
        (Hormander.B.realMultiplierOperator η₁ u) ≤
        C * (Hormander.B.sobolevNorm σ
          (Hormander.B.realMultiplierOperator η₂
            (Hormander.C.diffusionOperator
              (Hormander.C.c9SchwartzVectorField X hX hXc)
              (Hormander.C.c9SchwartzMultiplier c hc hcc) u)) +
          Hormander.B.sobolevNorm σ
            (Hormander.B.realMultiplierOperator η₂ u))
end Hormander.E

end
end
end

-- ==== Examples.amelieloher__hoermander_rothschild_stein.Examples.Example_ee05a46dda202ad14f7e_Main ====
-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.E
open Hormander.B
variable {N : ℕ}
/-- Cutoffs absorb: `ψ (τ u) = τ u` if `ψ = 1` on the support of `τ`. -/
axiom cutoffDistr_absorb (τ ψ : SchwartzMap (Carrier N) ℝ)
    (h : ∀ x ∈ tsupport (τ : Carrier N → ℝ), ψ x = 1) (u : Tempered N) :
    cutoffDistr ψ (cutoffDistr τ u) = cutoffDistr τ u
axiom cutoffDistr_comm (τ ψ : SchwartzMap (Carrier N) ℝ) (u : Tempered N) :
    cutoffDistr ψ (cutoffDistr τ u) = cutoffDistr τ (cutoffDistr ψ u)
axiom Eop_bOp (η₁ : SchwartzMap (Carrier N) ℝ) (δ : ℝ) (hδ : 0 < δ) (u : Tempered N) :
    Eop (bOp η₁ δ hδ) u = Hormander.A.Sδ N δ hδ (cutoffDistr η₁ u)
/-- The one-step regularization estimate follows from the localized gain estimate and the
mollifier converse. -/
theorem one_step_regularization_of_D1 {k N : ℕ}
    (X : Fin (k + 1) → Hormander.B.Carrier N → Hormander.B.Carrier N)
    (c : Hormander.B.Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcc : HasCompactSupport c)
    {K U : Set (Hormander.B.Carrier N)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s : ℕ) (hs : 1 ≤ s)
    (w : Fin N → Hormander.Interface.LieWord k)
    (hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (hw : ∀ x ∈ U,
      LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x))
    (η₁ η₂ : SchwartzMap (Hormander.B.Carrier N) ℝ)
    (hη : Hormander.D.cutoffPrecedes (η₁ : Hormander.B.Carrier N → ℝ)
      (η₂ : Hormander.B.Carrier N → ℝ))
    (hη₂K : tsupport (η₂ : Hormander.B.Carrier N → ℝ) ⊆ K)
    (r : ℝ) (hA6 : MollifierConverse N) (hD1 : D1Hypothesis) :
    ∃ C : ℝ, ∀ (u : 𝓢'(Hormander.B.Carrier N, ℂ))
      (a b : Hormander.A.SobolevSpace N r),
      a.toDistr = Hormander.B.cutoffDistr η₂ u →
      b.toDistr = Hormander.B.cutoffDistr η₂ (Hormander.hormanderOp X c u) →
      ∃ v : Hormander.A.SobolevSpace N (r + (2 : ℝ) / 4 ^ s),
        v.toDistr = Hormander.B.cutoffDistr η₁ u ∧ ‖v‖ ≤ C * (‖b‖ + ‖a‖) := by
  obtain ⟨χ, θ, ρ, hχ1, hχ2, h₂, h₃⟩ := exists_schwartz_chain hη
  have h₁ : Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ) (θ : Carrier N → ℝ) :=
    Hormander.D.cutoffPrecedes.trans hχ1 hχ2
  have hρK : tsupport (ρ : Carrier N → ℝ) ⊆ K :=
    (cutoffPrecedes_tsupport_subset h₃).trans hη₂K
  have hη₁η : ∀ x ∈ tsupport (η₁ : Carrier N → ℝ), η₂ x = 1 :=
    plateau_of_precedes hη
  obtain ⟨CD, hCD⟩ := hD1 X c hX hXc hc hcc hK hU hKU s hs w hws hw θ ρ h₂ hρK r
  obtain ⟨CL, hCL0, hCL⟩ := Lz_bound (Hormander.C.c9SchwartzVectorField X hX hXc)
    (Hormander.C.c9SchwartzMultiplier c hc hcc) η₁ θ ρ η₂ h₁ h₂ h₃ hA6 r
  obtain ⟨C0, hC00, hC0⟩ := bdd_bOp η₁ η₂ hη₁η r
  obtain ⟨δ₀, hδ₀, hδ₀p⟩ := exists_mollifier_radius hχ2
  set CD' : ℝ := max CD 0 with hCD'
  have hCD'0 : 0 ≤ CD' := le_max_right _ _
  refine ⟨CD' * (CL + C0), fun u a b ha hb => ?_⟩
  set M := ‖b‖ + ‖a‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hb' : b.toDistr = cutoffDistr η₂ (Eop (Hormander.C.diffusionOperator
      (Hormander.C.c9SchwartzVectorField X hX hXc)
      (Hormander.C.c9SchwartzMultiplier c hc hcc)) u) := by
    rw [hb, Eop_diffusion_eq X c hX hXc hc hcc]
  -- the localization `η₁ u` lies in `H^r`
  have hmem : TemperedDistribution.MemSobolev r 2 (cutoffDistr η₁ u) := by
    have e : cutoffDistr η₁ u = cutoffDistr η₁ a.toDistr := by
      rw [ha, cutoffDistr_comm, cutoffDistr_absorb η₁ η₂ hη₁η]
    have hM' : HasOrder 0 (realMultiplierOperator η₁) :=
      hasOrder_multiplierOperator_zero (complexifyRealSchwartz η₁)
    obtain ⟨C', hC'⟩ := hM' r
    obtain ⟨v, hv, -⟩ := Eop_bdd_global (hct_realMult η₁) (m := 0) (s := r) (r' := r) (by simp)
      (C := C') (fun φ => by simpa using hC' φ) a
    rw [e]
    exact Bdd.of_memSobolev v (by rw [hv, Eop_realMult])
  have hτ : cutoffDistr χ (cutoffDistr η₁ u) = cutoffDistr η₁ u :=
    cutoffDistr_absorb η₁ χ (plateau_of_precedes hχ1) u
  refine hA6 (r + (2 : ℝ) / 4 ^ s) (cutoffDistr η₁ u) (CD' * (CL + C0) * M) δ₀ hδ₀
    (fun δ hδ hδlt => ?_)
  have hψ : ∀ x ∈ tsupport (χ : Carrier N → ℝ), ∀ y, ‖x - y‖ ≤ δ / 2 → θ y = 1 :=
    fun x hx y hy => hδ₀p x hx y (hy.trans (by linarith))
  obtain ⟨g, hg⟩ := exists_testFunction_Sδ χ θ hχ2.2.2.2.1 (cutoffDistr η₁ u) hmem hτ δ hδ hψ
  have hθfix := cutoffDistr_Sδ_fix χ θ (cutoffDistr η₁ u) hτ δ hδ hψ
  have hgB : (g : Tempered N) = Eop (bOp η₁ δ hδ) u := by rw [hg, Eop_bOp]
  have hθg : realMultiplierOperator θ g = g := by
    apply testToTempered_injective'
    rw [← Eop_test (hct_realMult θ), Eop_realMult, hg, hθfix]
  have hθρ := plateau_of_precedes h₂
  have hρg : realMultiplierOperator ρ g = g := by
    apply realMult_eq_self_of_tsupport
    intro x hx
    apply hθρ
    have := tsupport_realMult_subset θ g
    rw [hθg] at this
    exact this hx
  have hρLg : realMultiplierOperator ρ (Hormander.C.diffusionOperator
      (Hormander.C.c9SchwartzVectorField X hX hXc)
      (Hormander.C.c9SchwartzMultiplier c hc hcc) g) =
      Hormander.C.diffusionOperator (Hormander.C.c9SchwartzVectorField X hX hXc)
      (Hormander.C.c9SchwartzMultiplier c hc hcc) g := by
    apply realMult_eq_self_of_tsupport
    intro x hx
    apply hθρ
    have hsub : tsupport (Hormander.C.diffusionOperator (Hormander.C.c9SchwartzVectorField X hX hXc)
        (Hormander.C.c9SchwartzMultiplier c hc hcc) g : Carrier N → ℂ) ⊆
        tsupport (g : Carrier N → ℂ) := by
      apply closure_minimal _ (isClosed_tsupport _)
      intro y hy
      by_contra hyg
      exact hy (diffusion_apply_eq_zero _ _ g y hyg)
    have := tsupport_realMult_subset θ g
    rw [hθg] at this
    exact this (hsub hx)
  -- bounds
  have hBL := hCL ⟨δ, hδ⟩ u a b ha hb'
  have hBB := hC0 ⟨δ, hδ⟩ u a ha
  have hnL : sobolevNorm r (Hormander.C.diffusionOperator
      (Hormander.C.c9SchwartzVectorField X hX hXc)
      (Hormander.C.c9SchwartzMultiplier c hc hcc) g) ≤ CL * M := by
    have h1 : Bdd r ((Hormander.C.diffusionOperator (Hormander.C.c9SchwartzVectorField X hX hXc)
        (Hormander.C.c9SchwartzMultiplier c hc hcc) g : TestFunction N) : Tempered N)
        (CL * (‖a‖ + ‖b‖)) := by
      rw [← Eop_test (hct_diffusion _ _), hgB]
      exact hBL
    have := h1.test_le
    rwa [add_comm ‖a‖ ‖b‖] at this
  have hng : sobolevNorm r g ≤ C0 * ‖a‖ := by
    have h1 : Bdd r (g : Tempered N) (C0 * ‖a‖) := by rw [hgB]; exact hBB
    exact h1.test_le
  have hD := hCD g
  rw [hθg, hρg, hρLg] at hD
  have hD' : sobolevNorm (r + (2 : ℝ) / 4 ^ s) g ≤ CD' * (CL * M + C0 * M) := by
    have hle : CD * (sobolevNorm r (Hormander.C.diffusionOperator
        (Hormander.C.c9SchwartzVectorField X hX hXc)
        (Hormander.C.c9SchwartzMultiplier c hc hcc) g) + sobolevNorm r g) ≤
        CD' * (CL * M + C0 * M) := by
      have hsum0 : 0 ≤ sobolevNorm r (Hormander.C.diffusionOperator
        (Hormander.C.c9SchwartzVectorField X hX hXc)
        (Hormander.C.c9SchwartzMultiplier c hc hcc) g) + sobolevNorm r g :=
        add_nonneg (sobolevNorm_nonneg _ _) (sobolevNorm_nonneg _ _)
      calc _ ≤ CD' * (sobolevNorm r (Hormander.C.diffusionOperator
          (Hormander.C.c9SchwartzVectorField X hX hXc)
          (Hormander.C.c9SchwartzMultiplier c hc hcc) g) + sobolevNorm r g) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hsum0
        _ ≤ CD' * (CL * M + C0 * M) := by
            apply mul_le_mul_of_nonneg_left _ hCD'0
            have : C0 * ‖a‖ ≤ C0 * M := by gcongr; linarith [norm_nonneg b]
            linarith
    exact hD.trans hle
  have hfin : Bdd (r + (2 : ℝ) / 4 ^ s) (g : Tempered N) (CD' * (CL + C0) * M) :=
    (Bdd.of_test _ g).mono (by nlinarith)
  rw [hg] at hfin
  exact hfin
end Hormander.E
