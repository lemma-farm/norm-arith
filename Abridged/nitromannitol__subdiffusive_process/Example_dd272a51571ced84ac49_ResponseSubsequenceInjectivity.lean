module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Normed.Operator.Bilinear

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v4df14347943b.SubdiffusiveProcess.Sobolev.WeakGradient ====
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

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v4df14347943b.SubdiffusiveProcess.Sobolev.GradientRange ====
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

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v4df14347943b.SubdiffusiveProcess.Variational.WeightedL2 ====
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

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v4df14347943b.SubdiffusiveProcess.Sobolev.WeightedGradient ====
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

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v4df14347943b.SubdiffusiveProcess.Sobolev.ResponseSpace ====
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
def PositiveCoefficient (Ω : Opens (SpatialCoordinates d)) :=
  {a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) //
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a x}
/-- The bilinear energy on the concrete Sobolev variation space. -/
def responseForm (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) :
    S.space →L[ℝ] S.space →L[ℝ] ℝ :=
  (weightedGradientForm a.val).bilinearComp (subspaceGradient S.space) (subspaceGradient S.space)

set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.existsUnique_responseForm_solution : ∀ {d : ℕ} {Ω : TopologicalSpace.Opens (SubdiffusiveProcess.SpatialCoordinates d)}
  (S : SubdiffusiveProcess.ResponseSpace Ω) (a : SubdiffusiveProcess.PositiveCoefficient Ω)
  (L : ↥S.space →L[ℝ] ℝ),
  ∃! u : ↥S.space,
    ∀ (v : ↥S.space),
      ((SubdiffusiveProcess.responseForm S a : ↥S.space → ↥S.space →L[ℝ] ℝ) u : ↥S.space → ℝ) v =
        (L : ↥S.space → ℝ) v
/-- The unique weak source solution; no fallback value is used. -/
def responseSolution (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) :
    S.space := Classical.choose (existsUnique_responseForm_solution S a L)

def inverseResponse (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) : ℝ :=
  responseForm S a (responseSolution S a L) (responseSolution S a L)

end SubdiffusiveProcess

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_dd272a51571ced84ac49_ResponseSubsequenceInjectivity ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-! Injectivity of an inverse limit from approximants along further subsequences.
The subsequence may depend on the datum and accuracy. Construction and bounded
energy of those approximants remain explicit hypotheses. -/
open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology
namespace SubdiffusiveProcess
set_option linter.unusedVariables false in
/-- Arbitrarily accurate bounded-energy approximants along further subsequences make an inverse limit injective. -/
theorem injective_limit_of_volumeResponse_subsequence_approximations
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : ℕ → PositiveCoefficient Ω)
    (G : DomainL2 Ω →L[ℝ] DomainL2 Ω) (D : Set (DomainL2 Ω))
    (hD : Dense D)
    (hresponse : ∀ f : DomainL2 Ω,
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (𝓝 (inner ℝ f (G f))))
    (happrox : ∀ φ ∈ D, ∀ ε : ℝ, 0 < ε →
      ∃ seq : ℕ → ℕ, StrictMono seq ∧ ∃ w : ℕ → S.space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm S (a (seq n)) (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε)) 
    (h_SubdiffusiveProcess_responseForm_nonneg : ∀ {d : ℕ} {Ω : TopologicalSpace.Opens (SubdiffusiveProcess.SpatialCoordinates d)}
      (S : SubdiffusiveProcess.ResponseSpace Ω) (a : SubdiffusiveProcess.PositiveCoefficient Ω)
      (u : ↥S.space),
      0 ≤ ((SubdiffusiveProcess.responseForm S a : ↥S.space → ↥S.space →L[ℝ] ℝ) u : ↥S.space → ℝ) u)
    (h_SubdiffusiveProcess_sq_load_le_inverseResponse_mul_responseForm : ∀ {d : ℕ} {Ω : TopologicalSpace.Opens (SubdiffusiveProcess.SpatialCoordinates d)}
      (S : SubdiffusiveProcess.ResponseSpace Ω) (a : SubdiffusiveProcess.PositiveCoefficient Ω)
      (L : ↥S.space →L[ℝ] ℝ) (w : ↥S.space),
      (L : ↥S.space → ℝ) w ^ 2 ≤
        SubdiffusiveProcess.inverseResponse S a L *
          ((SubdiffusiveProcess.responseForm S a : ↥S.space → ↥S.space →L[ℝ] ℝ) w : ↥S.space → ℝ) w)
    (h_SubdiffusiveProcess_inverseResponse_nonneg : ∀ {d : ℕ} {Ω : TopologicalSpace.Opens (SubdiffusiveProcess.SpatialCoordinates d)}
      (S : SubdiffusiveProcess.ResponseSpace Ω) (a : SubdiffusiveProcess.PositiveCoefficient Ω)
      (L : ↥S.space →L[ℝ] ℝ), 0 ≤ SubdiffusiveProcess.inverseResponse S a L)
    :
    Function.Injective G := by
  intro f g hfg
  let x : DomainL2 Ω := f - g
  have hGx : G x = 0 := by
    simp only [x, map_sub, hfg, sub_self]
  have hresponse_zero : Tendsto (fun n => inverseResponse S (a n)
      ((sobolevVolumeLoad x).comp S.space.subtypeL)) atTop (𝓝 0) := by
    simpa only [hGx, inner_zero_right] using hresponse x
  have hxD : ∀ φ ∈ D, inner ℝ x φ = 0 := by
    intro φ hφ
    by_contra hpair_ne
    have hpair_pos : 0 < |inner ℝ x φ| := abs_pos.mpr hpair_ne
    let ε : ℝ := |inner ℝ x φ| / (2 * (‖x‖ + 1))
    have hε : 0 < ε := by
      dsimp only [ε]
      positivity
    obtain ⟨seq, hseq, w, C, henergy, hclose⟩ := happrox φ hφ ε hε
    have hC : 0 ≤ C := by
      exact (h_SubdiffusiveProcess_responseForm_nonneg S (a (seq 0)) (w 0)).trans (henergy 0)
    have hsquare : ∀ n : ℕ,
        (((sobolevVolumeLoad x).comp S.space.subtypeL) (w n)) ^ 2 ≤
          inverseResponse S (a (seq n)) ((sobolevVolumeLoad x).comp S.space.subtypeL) * C := by
      intro n
      exact (h_SubdiffusiveProcess_sq_load_le_inverseResponse_mul_responseForm S (a (seq n))
        ((sobolevVolumeLoad x).comp S.space.subtypeL) (w n)).trans
          (mul_le_mul_of_nonneg_left (henergy n) (h_SubdiffusiveProcess_inverseResponse_nonneg S (a (seq n)) _))
    have hsqrt : Tendsto (fun n => Real.sqrt
        (inverseResponse S (a (seq n)) ((sobolevVolumeLoad x).comp S.space.subtypeL) * C))
        atTop (𝓝 0) := by
      have hmul := (hresponse_zero.comp hseq.tendsto_atTop).mul_const C
      have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hmul
      simpa only [Function.comp_def, zero_mul, Real.sqrt_zero] using hs
    have hload_abs : Tendsto (fun n =>
        |((sobolevVolumeLoad x).comp S.space.subtypeL) (w n)|) atTop (𝓝 0) := by
      apply squeeze_zero'
      · exact Eventually.of_forall fun n => abs_nonneg _
      · exact Eventually.of_forall fun n => Real.abs_le_sqrt (hsquare n)
      · exact hsqrt
    have hpair_bound : |inner ℝ x φ| ≤ ‖x‖ * ε := by
      have ht : Tendsto (fun n =>
          |((sobolevVolumeLoad x).comp S.space.subtypeL) (w n)| + ‖x‖ * ε)
          atTop (𝓝 (‖x‖ * ε)) := by
        simpa only [zero_add] using hload_abs.add_const (‖x‖ * ε)
      apply ge_of_tendsto ht
      exact Eventually.of_forall fun n => by
        have hinner_close : |inner ℝ x (φ - (w n).val.1)| ≤ ‖x‖ * ε := by
          calc
            |inner ℝ x (φ - (w n).val.1)| ≤ ‖x‖ * ‖φ - (w n).val.1‖ := by
              simpa only [Real.norm_eq_abs] using
                (norm_inner_le_norm (𝕜 := ℝ) x (φ - (w n).val.1))
            _ ≤ ‖x‖ * ε := mul_le_mul_of_nonneg_left (by
              simpa only [norm_sub_rev] using hclose n) (norm_nonneg x)
        calc
          |inner ℝ x φ| = |inner ℝ x (w n).val.1 + inner ℝ x (φ - (w n).val.1)| := by
            rw [inner_sub_right]
            ring_nf
          _ ≤ |inner ℝ x (w n).val.1| + |inner ℝ x (φ - (w n).val.1)| :=
            abs_add_le _ _
          _ ≤ |((sobolevVolumeLoad x).comp S.space.subtypeL) (w n)| + ‖x‖ * ε := by
            rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
            exact add_le_add (le_refl _) hinner_close
    dsimp only [ε] at hpair_bound
    have hxnorm : 0 ≤ ‖x‖ := norm_nonneg x
    have hdenom : 0 < 2 * (‖x‖ + 1) := by positivity
    have hfactor : ‖x‖ / (2 * (‖x‖ + 1)) < 1 := by
      rw [div_lt_one hdenom]
      linarith only [hxnorm]
    have hrearrange : ‖x‖ * (|inner ℝ x φ| / (2 * (‖x‖ + 1))) =
        |inner ℝ x φ| * (‖x‖ / (2 * (‖x‖ + 1))) := by ring
    rw [hrearrange] at hpair_bound
    nlinarith only [hpair_bound, hpair_pos, hfactor]
  have hxzero : x = 0 := by
    have heq : (fun φ : DomainL2 Ω => inner ℝ x φ) = fun _ => 0 := by
      apply Continuous.ext_on hD
      · exact continuous_const.inner continuous_id
      · exact continuous_const
      · intro φ hφ
        exact hxD φ hφ
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact congrFun heq x
  simpa only [x, sub_eq_zero] using hxzero
end SubdiffusiveProcess
