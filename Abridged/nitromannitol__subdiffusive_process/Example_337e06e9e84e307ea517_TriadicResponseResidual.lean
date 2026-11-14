module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.SpecialFunctions.Exp

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.WeakGradient ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# The actual weak-gradient graph

Spatial coordinates use the usual finite product, with its sup norm. Gradient
energy will use the sum of squared coordinate L2 norms, not that sup norm.
The graph below imposes the distributional derivative identity against every
smooth function compactly supported in the open domain. It does not assume
an abstract space has the properties of a Sobolev space.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
namespace SubdiffusiveProcess
noncomputable section
abbrev SpatialCoordinates (d : ℕ) := Fin d → ℝ
abbrev DomainL2 {d : ℕ} (Ω : Opens (SpatialCoordinates d)) :=
  Lp ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))
abbrev SobolevData {d : ℕ} (Ω : Opens (SpatialCoordinates d)) :=
  DomainL2 Ω × (Fin d → DomainL2 Ω)
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- A smooth compactly supported test, as an actual scalar L2 equivalence class. -/
noncomputable def testL2 (φ : 𝓓(Ω, ℝ)) : DomainL2 Ω :=
  (φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ
/-- The coordinate derivative of a test is also an actual L2 function. -/
noncomputable def testPartialL2 (φ : 𝓓(Ω, ℝ)) (i : Fin d) : DomainL2 Ω :=
  ((φ.contDiff.continuous_fderiv_apply (by simp)).comp
    (continuous_id.prodMk continuous_const) |>.memLp_of_hasCompactSupport
      (φ.hasCompactSupport.fderiv_apply ℝ (Pi.single i 1))).toLp
    (fun x => fderiv ℝ φ x (Pi.single i 1))
/-- No pointwise representative is selected outside its almost-everywhere identity. -/
axiom testL2_coeFn (φ : 𝓓(Ω, ℝ)) :
    (testL2 φ : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] φ
/-- The L2 derivative is the classical coordinate derivative almost everywhere. -/
axiom testPartialL2_coeFn (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    (testPartialL2 φ i : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      (fun x => fderiv ℝ φ x (Pi.single i 1))
/-- One distributional integration-by-parts constraint, as a bounded linear functional. -/
noncomputable def weakGradientTest (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    SobolevData Ω →L[ℝ] ℝ :=
  ((innerSL ℝ (testL2 φ)).comp
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _))) +
  ((innerSL ℝ (testPartialL2 φ i)).comp (ContinuousLinearMap.fst ℝ _ _))
/-- The graph of weak first derivatives on the open domain. -/
noncomputable def weakSobolevGraph (Ω : Opens (SpatialCoordinates d)) :
    Submodule ℝ (SobolevData Ω) :=
  ⨅ (φ : 𝓓(Ω, ℝ)) (i : Fin d), LinearMap.ker (weakGradientTest φ i).toLinearMap

end
end SubdiffusiveProcess

end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Geometry.Cube ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Actual open coordinate cubes

`SpatialCoordinates d` carries the maximum norm, so its open ball of radius
`r / 2` is precisely the axis-aligned cube of side `r`. The energy still uses
the Euclidean coordinate pairing. Keeping these conventions separate avoids
replacing the unit slopes of the response defect by maximum-norm unit slopes.
-/
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}
/-- The open coordinate cube of positive side length `r` centered at `z`. -/
def centeredCube (z : SpatialCoordinates d) (r : ℝ) (_hr : 0 < r) :
    Opens (SpatialCoordinates d) := ⟨Metric.ball z (r / 2), Metric.isOpen_ball⟩

/-- Cubes provide the bounded domains needed by actual affine Sobolev data. -/
axiom centeredCube_isBounded (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Bornology.IsBounded (centeredCube z r hr : Set (SpatialCoordinates d))

/-- The normalization denominator is strictly positive, including dimension zero. -/
axiom centeredCube_volume_pos (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Geometry.OddGrid ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Centered odd subdivisions of an actual cube

For `2*m+1` children in each coordinate, the middle child is centered on
the original midplane. Triadic grids are specializations of this literal
geometry. Labels are coordinate tuples, not abstract nodes of a tree.
-/
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}
/-- Coordinate labels in the odd subdivision with `2*m+1` pieces per side. -/
abbrev OddGridIndex (d m : ℕ) := Fin d → Fin (2 * m + 1)
/-- The actual center of a cell, with the middle coordinate label equal to `m`. -/
def oddGridCenter (z : SpatialCoordinates d) (r : ℝ) (m : ℕ)
    (k : OddGridIndex d m) : SpatialCoordinates d :=
  fun i => z i + ((k i).val - (m : ℝ)) * (r / (2 * (m : ℝ) + 1))
/-- The actual open child cube in a centered odd subdivision. -/
def oddGridCell (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (m : ℕ)
    (k : OddGridIndex d m) : Opens (SpatialCoordinates d) :=
  centeredCube (oddGridCenter z r m k) (r / (2 * (m : ℝ) + 1))
    (div_pos hr (by positivity))

set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.oddGridCell_isFiniteMeasure : ∀ {d : ℕ} (z : SubdiffusiveProcess.SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (m : ℕ)
  (k : SubdiffusiveProcess.OddGridIndex d m),
  MeasureTheory.IsFiniteMeasure
    (MeasureTheory.MeasureSpace.volume.restrict
      (↑(SubdiffusiveProcess.oddGridCell z r hr m k) :
        Set (SubdiffusiveProcess.SpatialCoordinates d)))
attribute [instance] _root_.SubdiffusiveProcess.oddGridCell_isFiniteMeasure
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Geometry.OddGridPartition ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# The centered odd grid is an actual Lebesgue partition

Containment and disjointness, together with the exact sum of cell volumes,
prove coverage up to Lebesgue null sets. No partition axiom or floor-function
selection is needed. This concerns Lebesgue volume, not limiting energy or
speed measures.
-/
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}
/-- Volume is additive on every finite subfamily of these actual disjoint cells. -/
axiom oddGrid_subfamily_volume_real (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (S : Finset (OddGridIndex d m)) :
    volume.real (⋃ k ∈ S, (oddGridCell z r hr m k : Set (SpatialCoordinates d))) =
      ∑ k ∈ S, volume.real (oddGridCell z r hr m k : Set (SpatialCoordinates d))
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Geometry.OddGridResidual ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# The unresolved volume on a centered odd grid

Unresolved labels are precisely those whose actual open cells meet at least
one selected coordinate midplane. Count the middle-coordinate fibers and
use their actual cell volumes. No independence, coefficient estimate, or
assumed geometric remainder enters this argument.
-/
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}
/-- Labels whose `i`th coordinate is the middle child. -/
def oddGridPlaneCells (m : ℕ) (i : Fin d) : Finset (OddGridIndex d m) :=
  Finset.univ.filter (fun k => (k i).val = m)
/-- Cells unresolved by the selected coordinate midplanes. -/
def oddGridUnresolved (m : ℕ) (I : Finset (Fin d)) : Finset (OddGridIndex d m) :=
  I.biUnion (oddGridPlaneCells m)
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Geometry.TriadicResidual ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Vanishing geometric remainder on the actual triadic grid

The odd grid with middle index `3^J / 2` has exactly `3^J` intervals per
coordinate. Its actual unresolved volume fraction is at most `d / 3^J`
and tends to zero. This limit is geometric and deterministic; it is taken
before any cutoff-uniform moment estimate in the reflection argument.
-/
open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}
/-- The middle label in a coordinate subdivision of depth `J`. -/
def triadicHalf (J : ℕ) : ℕ := 3 ^ J / 2
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.KilledGraph ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# The killed Sobolev graph

The zero-boundary space is the closure of the classical function/gradient
pairs of smooth functions compactly supported in the domain. Integration by
parts proves that this closure consists of genuine weak gradients. No trace
or density theorem about a proposed abstract space is assumed.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- Classical function and coordinate derivatives of a compactly supported smooth function. -/
def smoothSobolevData (φ : 𝓓(Ω, ℝ)) : SobolevData Ω :=
  (testL2 φ, testPartialL2 φ)
/-- The actual smooth-gradient graph is linear. -/
def smoothSobolevDataLinear : 𝓓(Ω, ℝ) →ₗ[ℝ] SobolevData Ω where
  toFun := smoothSobolevData
  map_add' φ ψ := by
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [testL2_coeFn (φ + ψ), testL2_coeFn φ, testL2_coeFn ψ,
        Lp.coeFn_add (testL2 φ) (testL2 ψ)] with x ha hb hc hd
      change (testL2 (φ + ψ)) x = (testL2 φ + testL2 ψ) x
      rw [ha, hd]
      change φ x + ψ x = (testL2 φ) x + (testL2 ψ) x
      rw [hb, hc]
    · funext i
      apply Lp.ext
      filter_upwards [testPartialL2_coeFn (φ + ψ) i, testPartialL2_coeFn φ i,
        testPartialL2_coeFn ψ i, Lp.coeFn_add (testPartialL2 φ i) (testPartialL2 ψ i)]
        with x ha hb hc hd
      change (testPartialL2 (φ + ψ) i) x = (testPartialL2 φ i + testPartialL2 ψ i) x
      rw [ha, hd]
      simp only [Pi.add_apply, hb, hc]
      change fderiv ℝ ((φ : SpatialCoordinates d → ℝ) + (ψ : SpatialCoordinates d → ℝ)) x (Pi.single i 1) = _
      rw [fderiv_add (φ.contDiff.differentiable (by simp) x)
        (ψ.contDiff.differentiable (by simp) x)]
      rfl
  map_smul' c φ := by
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [testL2_coeFn (c • φ), testL2_coeFn φ,
        Lp.coeFn_smul c (testL2 φ)] with x ha hb hc
      change (testL2 (c • φ)) x = (c • testL2 φ) x
      simp [ha, hb, hc]
    · funext i
      apply Lp.ext
      filter_upwards [testPartialL2_coeFn (c • φ) i, testPartialL2_coeFn φ i,
        Lp.coeFn_smul c (testPartialL2 φ i)] with x ha hb hc
      change (testPartialL2 (c • φ) i) x = (c • testPartialL2 φ i) x
      rw [ha, hc]
      simp only [Pi.smul_apply, hb]
      change fderiv ℝ (c • (φ : SpatialCoordinates d → ℝ)) x (Pi.single i 1) = _
      rw [fderiv_const_smul (φ.contDiff.differentiable (by simp) x)]
      rfl

/-- The zero-boundary Sobolev graph is the closure of actual compactly supported smooth data. -/
def killedSobolevGraph (Ω : Opens (SpatialCoordinates d)) : Submodule ℝ (SobolevData Ω) :=
  (LinearMap.range (smoothSobolevDataLinear (Ω := Ω))).topologicalClosure
/-- The killed space is closed, hence complete in its graph norm. -/
axiom isClosed_killedSobolevGraph :
    IsClosed (killedSobolevGraph Ω : Set (SobolevData Ω))
/-- Every element of the killed completion has genuine weak first derivatives. -/
axiom killedSobolevGraph_le_weakSobolevGraph : killedSobolevGraph Ω ≤ weakSobolevGraph Ω
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.GradientRange ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Closed gradient ranges and volume loads

Only the finite tuple of scalar L2 spaces receives a Hilbert norm. Spatial
coordinates retain their ordinary product norm; no vector-valued Lp coercion
through a Euclidean-space wrapper occurs. The Poincare estimate below is an
explicit foundational input on a concrete closed subspace of the weak graph.
It is not a model convergence or regularity assumption.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- Coordinatewise square-integrable gradients, with the sum-of-squares Hilbert norm. -/
abbrev HilbertGradient (Ω : Opens (SpatialCoordinates d)) :=
  PiLp 2 (fun _ : Fin d => DomainL2 Ω)
/-- The actual coordinate gradient projection from function/gradient data. -/
def sobolevGradient : SobolevData Ω →L[ℝ] HilbertGradient Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => DomainL2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.snd ℝ _ _)
def subspaceGradient (V : Submodule ℝ (SobolevData Ω)) : V →L[ℝ] HilbertGradient Ω :=
  sobolevGradient.comp V.subtypeL

/-- L2 volume pairing on actual function/gradient data. -/
def sobolevVolumeLoad (f : DomainL2 Ω) : SobolevData Ω →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (ContinuousLinearMap.fst ℝ _ _)
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.MeanZero ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Mean-zero Sobolev data and the affine Neumann load

The domain has finite Lebesgue volume. Mean zero means its actual volume
integral vanishes. The affine Neumann load is the sum of the coordinate
volume integrals of the weak gradient; identifying its boundary-flux formula
is a separate trace/divergence theorem.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
/-- A constant scalar function as an actual domain L2 equivalence class. -/
def domainConstantL2 (c : ℝ) : DomainL2 Ω :=
  (memLp_const (μ := volume.restrict (Ω : Set (SpatialCoordinates d))) (p := 2) c).toLp
    (fun _ => c)

/-- The actual mean-zero H1 graph; the zero integral uses Lebesgue measure. -/
def meanZeroSobolevGraph (Ω : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))] :
    Submodule ℝ (SobolevData Ω) :=
  weakSobolevGraph Ω ⊓ LinearMap.ker (sobolevVolumeLoad (domainConstantL2 1)).toLinearMap
axiom isClosed_meanZeroSobolevGraph :
    IsClosed (meanZeroSobolevGraph Ω : Set (SobolevData Ω))
/-- The affine Neumann load on an actual gradient vector. -/
def affineNeumannLoad (p : Fin d → ℝ) : HilbertGradient Ω →L[ℝ] ℝ :=
  ∑ i : Fin d, (innerSL ℝ (domainConstantL2 (p i))).comp (PiLp.proj 2 _ i)

end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.AffineData ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Affine functions in the concrete Sobolev graph

The boundary slope in the finite-volume responses of Section 3.2 is an
actual affine function on the domain. Its weak gradient is proved to be the
constant vector of slopes. Boundedness supplies its L2 membership; integration
by parts uses the compact support of the test, not of the affine function.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- The literal coordinate pairing with a prescribed affine slope. -/
def affineSlope (p : Fin d → ℝ) : SpatialCoordinates d →L[ℝ] ℝ :=
  ∑ i : Fin d, p i • ContinuousLinearMap.proj i

variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
/-- Bounded domains make every affine function square integrable. -/
axiom affine_memLp (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) :
    MemLp (fun x => affineSlope p x + c) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d)))
/-- An affine function as its actual L2 equivalence class. -/
def affineL2 (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) : DomainL2 Ω :=
  (affine_memLp hΩ p c).toLp (fun x => affineSlope p x + c)

/-- The affine function paired with its constant coordinate gradients. -/
def affineSobolevData (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) : SobolevData Ω :=
  (affineL2 hΩ p c, fun i => domainConstantL2 (p i))
/-- The specified constant gradients really are the distributional derivatives. -/
axiom affineSobolevData_mem (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) : affineSobolevData hΩ p c ∈ weakSobolevGraph Ω
/-- Affine boundary data as an element of the proved weak Sobolev graph. -/
def affineSobolev (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (c : ℝ) : weakSobolevGraph Ω :=
  ⟨affineSobolevData hΩ p c, affineSobolevData_mem hΩ p c⟩
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Variational.WeightedL2 ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Weighted integral forms on vector fields

The bilinear form is the actual integral of a bounded scalar weight times
the pointwise inner product. With base measure A dx and vectors equal to
Sobolev gradients this is the finite-cutoff energy. The identification of
the admissible Sobolev gradient spaces is a separate obligation.
-/
open MeasureTheory InnerProductSpace Filter
open scoped ENNReal
namespace SubdiffusiveProcess
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The actual integral form on square-integrable vector fields with a bounded scalar weight. -/
noncomputable def weightedL2Form (a : Lp ℝ ∞ μ) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ →L[ℝ] ℝ :=
  (innerSL ℝ).comp ((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holderL μ ∞ 2 2 a)

end SubdiffusiveProcess

end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.WeightedGradient ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# The finite-cutoff coefficient form on actual gradients

The energy is the sum of the coordinate weighted L2 pairings. Thus it is
exactly the scalar coefficient times the Euclidean dot product of weak
gradients, with no factor 1/2. Positive bounded coefficients and Poincare
on a concrete closed variation space give the actual volume-source equation.
-/
open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- Sum of scalar coordinate energies, on the Hilbert space of gradients. -/
def weightedGradientForm (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    HilbertGradient Ω →L[ℝ] HilbertGradient Ω →L[ℝ] ℝ :=
  ∑ i : Fin d, (weightedL2Form (E := ℝ) a).bilinearComp (PiLp.proj 2 _ i) (PiLp.proj 2 _ i)

end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.ResponseSpace ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Concrete spaces and coefficients for finite responses

The space is a closed subspace of the actual distributional H1 graph,
with ordinary Poincare stated explicitly. The coefficient is an actual L∞
class bounded away from zero. No response or limiting theorem is a field.
-/
open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- A concrete Sobolev variation space on which ordinary Poincare holds. -/
structure ResponseSpace (Ω : Opens (SpatialCoordinates d)) where
  space : Submodule ℝ (SobolevData Ω)
  le_weak : space ≤ weakSobolevGraph Ω
  closed : IsClosed (space : Set (SobolevData Ω))
  poincare : ∃ K : ℝ≥0, ∀ z : space,
    ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient space z‖
/-- Killed variations use the previously constructed H1_0 completion. -/
def killedResponseSpace (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
    ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖) :
    ResponseSpace Ω :=
  ⟨killedSobolevGraph Ω, killedSobolevGraph_le_weakSobolevGraph,
    isClosed_killedSobolevGraph, hP⟩
/-- Neumann variations use the actual mean-zero weak-gradient graph. -/
def meanZeroResponseSpace [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖) :
    ResponseSpace Ω :=
  ⟨meanZeroSobolevGraph Ω, inf_le_left, isClosed_meanZeroSobolevGraph, hP⟩
/-- Actual bounded scalar coefficients with a uniform positive lower bound. -/
def PositiveCoefficient (Ω : Opens (SpatialCoordinates d)) :=
  {a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) //
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a x}
/-- The bilinear energy on the concrete Sobolev variation space. -/
def responseForm (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) :
    S.space →L[ℝ] S.space →L[ℝ] ℝ :=
  (weightedGradientForm a.val).bilinearComp (subspaceGradient S.space) (subspaceGradient S.space)
axiom existsUnique_responseForm_solution (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) : ∃! u : S.space, ∀ v, responseForm S a u v = L v
/-- The unique weak source solution; no fallback value is used. -/
def responseSolution (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) :
    S.space := Classical.choose (existsUnique_responseForm_solution S a L)

def inverseResponse (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) : ℝ :=
  responseForm S a (responseSolution S a L) (responseSolution S a L)

end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.DirichletResponse ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Canonical boundary responses

Boundary data are actual elements of the weak H1 graph. Admissible functions
differ by an element of the concrete variation space; for the killed space
this is the usual H1/H1_0 boundary class. The minimizer is constructed from
the source solver with load -E(b, ·), and the minimum is proved attained.
-/
open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
/-- The actual coefficient form on full function/gradient data. -/
def sobolevCoefficientForm (a : PositiveCoefficient Ω) :
    SobolevData Ω →L[ℝ] SobolevData Ω →L[ℝ] ℝ :=
  (weightedGradientForm a.val).bilinearComp sobolevGradient sobolevGradient

/-- The load that corrects a given H1 extension to a harmonic one. -/
def boundaryCorrectionLoad (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) : S.space →L[ℝ] ℝ :=
  -((sobolevCoefficientForm a b.val).comp S.space.subtypeL)
/-- The actual harmonic extension in the given affine Sobolev class. -/
def dirichletMinimizer (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) : weakSobolevGraph Ω :=
  ⟨b.val + (responseSolution S a (boundaryCorrectionLoad S a b) : SobolevData Ω),
    (weakSobolevGraph Ω).add_mem b.property (S.le_weak (responseSolution S a _).property)⟩

/-- The scalar boundary response is the actual energy of its constructed extension. -/
def dirichletResponse (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) : ℝ :=
  sobolevCoefficientForm a (dirichletMinimizer S a b).val (dirichletMinimizer S a b).val

end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.AffineResponses ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Actual affine finite-volume responses

These are the unnormalized primal and inverse-Neumann scalar responses used
in Section 3.2 and the original-grid reflection argument. Their competitors
are the concrete killed and mean-zero Sobolev spaces. Only ordinary Poincare
and finite-cutoff ellipticity enter their construction. Matrix normalization
and finite-partition subadditivity are separate obligations.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- The affine Dirichlet minimum, with the prescribed slope and killed variations. -/
def affineDirichletResponse (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) : ℝ :=
  dirichletResponse (killedResponseSpace hP) a (affineSobolev hΩ p 0)

/-- The inverse affine Neumann response, on the actual mean-zero Sobolev space. -/
def affineInverseNeumannResponse
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) : ℝ :=
  inverseResponse (meanZeroResponseSpace hP) a
    ((affineNeumannLoad p).comp (subspaceGradient (meanZeroSobolevGraph Ω)))
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.DiagonalDefect ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# The concrete diagonal response defect

The equal-slope defect used in Theorem 19 is the sum of the actual affine
Dirichlet and inverse-Neumann responses, divided by twice the domain volume,
minus the squared slope. Nonnegativity follows by using the mean-subtracted
Dirichlet minimizer in the Neumann problem. The upper bound is independent
of the domain volume, as required to remove unresolved subcubes at a fixed
cutoff. No matrix representation or subadditivity is assumed here.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
def affineDiagonalDefect
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (_hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) : ℝ :=
  (affineDirichletResponse hΩ hD a p + affineInverseNeumannResponse hN a p) /
    (2 * volume.real (Ω : Set (SpatialCoordinates d))) - ∑ i : Fin d, (p i)^2
axiom affineDiagonalDefect_le_of_unit_slope
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) {p : Fin d → ℝ} (hp : ∑ i : Fin d, (p i)^2 = 1)
    {c M : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a.val x)
    (hM : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ M) :
    affineDiagonalDefect hΩ hvol hD hN a p ≤ (M + c⁻¹) / 2 - 1
end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_337e06e9e84e307ea517_TriadicResponseResidual ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Removing unresolved affine-response contributions at fixed ellipticity

This joins the actual triadic geometry to the actual Sobolev responses.
Ordinary Poincare on each cell constructs the responses. A common positive
coefficient lower bound and finite upper bound suffice for the unresolved
weighted sum to vanish. No cutoff-uniform estimate or partition-response
inequality is assumed. In the reflection application these bounds are fixed
before the geometric depth tends to infinity. Unit slopes may vary with
both depth and cell, as they do under the coordinate reflections.
-/
open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
variable
  (hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
  (hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
  (a : ∀ J (k : OddGridIndex d (triadicHalf J)),
    PositiveCoefficient (oddGridCell z r hr (triadicHalf J) k))
/-- The literal volume-weighted sum of actual defects on unresolved triadic cells. -/
def triadicResponseResidual (I : Finset (Fin d))
    (p : ∀ J, OddGridIndex d (triadicHalf J) → Fin d → ℝ) (J : ℕ) : ℝ :=
  ∑ k ∈ oddGridUnresolved (triadicHalf J) I,
    (volume.real ((oddGridCell z r hr (triadicHalf J) k) : Set (SpatialCoordinates d)) /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) *
    affineDiagonalDefect (Ω := (oddGridCell z r hr (triadicHalf J) k)) (centeredCube_isBounded _ _)
      (centeredCube_volume_pos _ _) (hD J k) (hN J k) (a J k) (p J k)
/-- Common coefficient bounds multiply only the actual unresolved volume fraction. -/
theorem triadicResponseResidual_le_volume_fraction
    (I : Finset (Fin d)) {p : ∀ J, OddGridIndex d (triadicHalf J) → Fin d → ℝ}
    (hp : ∀ J k, ∑ i : Fin d, (p J k i)^2 = 1)
    {c M : ℝ} (hc : 0 < c)
    (ha : ∀ J k, ∀ᵐ x ∂volume.restrict
      (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)), c ≤ (a J k).val x)
    (hM : ∀ J k, ∀ᵐ x ∂volume.restrict
      (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)), (a J k).val x ≤ M)
    (J : ℕ) :
    triadicResponseResidual z hr hD hN a I p J ≤ max ((M + c⁻¹) / 2 - 1) 0 *
      (volume.real (⋃ k ∈ oddGridUnresolved (triadicHalf J) I,
        ((oddGridCell z r hr (triadicHalf J) k) : Set (SpatialCoordinates d))) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  let C := max ((M + c⁻¹) / 2 - 1) 0
  calc
    _ ≤ ∑ k ∈ oddGridUnresolved (triadicHalf J) I,
        (volume.real ((oddGridCell z r hr (triadicHalf J) k) : Set (SpatialCoordinates d)) /
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * C := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _
        (div_nonneg measureReal_nonneg (centeredCube_volume_pos z hr).le)
      exact (affineDiagonalDefect_le_of_unit_slope _ _ _ _ _ (hp J k) hc (ha J k) (hM J k)).trans
        (le_max_left _ _)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_div, ← oddGrid_subfamily_volume_real]
      exact mul_comm _ _
end SubdiffusiveProcess
