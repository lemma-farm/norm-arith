module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Pi

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.vb7c9d381e330.UnitDistance.EnergyWindow ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-!
# Removing the overlap density on the common energy window

`X` and `Y` are the two endpoint energies on the overlap space. Its ordinary
measure includes positions and displacements; the probability density is
`exp (-(X + Y)) / Z`. Zero-profile points are omitted from that space.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace UnitDistance
noncomputable def overlapLaw {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) (Z : ℝ) : Measure Ω :=
  m.withDensity (fun ω => ENNReal.ofReal (Real.exp (-(X ω + Y ω)) / Z))

end UnitDistance

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Examples.Example_7a89ba6663ebbc3cac0c_TensorProfiles ====
@[expose] public section
set_option backward.privateInPublic true
/-!
# Tensor overlap laws

These identities connect sums of endpoint energies with products of their
actual overlap measures. Independence across blocks is proved from the
product measure, and need not be supplied as an additional hypothesis.
The base measure of each block may already be restricted to profile support.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace UnitDistance
section ProductDensity
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}
  [∀ i, MeasurableSpace (Ω i)]

def tensorEnergy (E : (i : ι) → Ω i → ℝ) (x : (i : ι) → Ω i) : ℝ :=
  ∑ i, E i (x i)

end ProductDensity
section ProductMoments
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}
  [∀ i, MeasurableSpace (Ω i)]


set_option linter.unusedVariables false in
/-- The product overlap law has the summed endpoint means and a variance
bound linear in the number of blocks, derived from the individual laws. -/
theorem tensor_overlap_moments (m : (i : ι) → Measure (Ω i)) [∀ i, SigmaFinite (m i)]
    (X Y : (i : ι) → Ω i → ℝ) (Z mean : ι → ℝ) (C : ℝ)
    (hZ : ∀ i, 0 < Z i)
    (hI : ∀ i, Integrable (fun x => Real.exp (-(X i x + Y i x))) (m i))
    (hnorm : ∀ i, ∫ x, Real.exp (-(X i x + Y i x)) ∂m i = Z i)
    (hX : ∀ i, MemLp (X i) 2 (overlapLaw (m i) (X i) (Y i) (Z i)))
    (hY : ∀ i, MemLp (Y i) 2 (overlapLaw (m i) (X i) (Y i) (Z i)))
    (hmeanX : ∀ i, ∫ x, X i x ∂overlapLaw (m i) (X i) (Y i) (Z i) = mean i)
    (hmeanY : ∀ i, ∫ x, Y i x ∂overlapLaw (m i) (X i) (Y i) (Z i) = mean i)
    (hvX : ∀ i, variance (X i) (overlapLaw (m i) (X i) (Y i) (Z i)) ≤ C)
    (hvY : ∀ i, variance (Y i) (overlapLaw (m i) (X i) (Y i) (Z i)) ≤ C) 
    (h_UnitDistance_tensorEnergy_memLp : ∀ {ι : Type u_1} [inst : Fintype ι] {Ω : ι → Type u_2} [inst_1 : (i : ι) → MeasurableSpace (Ω i)]
      (μ : (i : ι) → MeasureTheory.Measure (Ω i)) [∀ (i : ι), MeasureTheory.IsProbabilityMeasure (μ i)]
      (X : (i : ι) → Ω i → ℝ),
      (∀ (i : ι), MeasureTheory.MemLp (X i) 2 (μ i)) →
        MeasureTheory.MemLp (UnitDistance.tensorEnergy X) 2 (MeasureTheory.Measure.pi μ))
    (h_UnitDistance_tensor_overlapLaw : ∀ {ι : Type u_1} [inst : Fintype ι] {Ω : ι → Type u_2} [inst_1 : (i : ι) → MeasurableSpace (Ω i)]
      (m : (i : ι) → MeasureTheory.Measure (Ω i)) [∀ (i : ι), MeasureTheory.SigmaFinite (m i)]
      (X Y : (i : ι) → Ω i → ℝ) (Z : ι → ℝ),
      (∀ (i : ι), 0 < Z i) →
        (∀ (i : ι), MeasureTheory.Integrable (fun (x : Ω i) ↦ Real.exp (-(X i x + Y i x))) (m i)) →
          UnitDistance.overlapLaw (MeasureTheory.Measure.pi m) (UnitDistance.tensorEnergy X)
              (UnitDistance.tensorEnergy Y) (∏ i : ι, Z i) =
            MeasureTheory.Measure.pi fun (i : ι) ↦ UnitDistance.overlapLaw (m i) (X i) (Y i) (Z i))
    (h_UnitDistance_tensorEnergy_variance : ∀ {ι : Type u_1} [inst : Fintype ι] {Ω : ι → Type u_2} [inst_1 : (i : ι) → MeasurableSpace (Ω i)]
      (μ : (i : ι) → MeasureTheory.Measure (Ω i)) [∀ (i : ι), MeasureTheory.IsProbabilityMeasure (μ i)]
      (X : (i : ι) → Ω i → ℝ),
      (∀ (i : ι), MeasureTheory.MemLp (X i) 2 (μ i)) →
        ProbabilityTheory.variance (UnitDistance.tensorEnergy X) (MeasureTheory.Measure.pi μ) =
          ∑ i : ι, ProbabilityTheory.variance (X i) (μ i))
    (h_UnitDistance_tensorEnergy_integral : ∀ {ι : Type u_1} [inst : Fintype ι] {Ω : ι → Type u_2} [inst_1 : (i : ι) → MeasurableSpace (Ω i)]
      (μ : (i : ι) → MeasureTheory.Measure (Ω i)) [∀ (i : ι), MeasureTheory.IsProbabilityMeasure (μ i)]
      (X : (i : ι) → Ω i → ℝ),
      (∀ (i : ι), MeasureTheory.Integrable (X i) (μ i)) →
        ∫ (x : (i : ι) → Ω i), UnitDistance.tensorEnergy X x ∂MeasureTheory.Measure.pi μ =
          ∑ i : ι, ∫ (x : Ω i), X i x ∂μ i)
    (h_UnitDistance_overlapLaw_probability : ∀ {Ω : Type u_2} [inst : MeasurableSpace Ω] (m : MeasureTheory.Measure Ω) (X Y : Ω → ℝ) {Z : ℝ},
      0 < Z →
        MeasureTheory.Integrable (fun (ω : Ω) ↦ Real.exp (-(X ω + Y ω))) m →
          ∫ (ω : Ω), Real.exp (-(X ω + Y ω)) ∂m = Z →
            MeasureTheory.IsProbabilityMeasure (UnitDistance.overlapLaw m X Y Z))
    :
    let μ := overlapLaw (Measure.pi m) (tensorEnergy X) (tensorEnergy Y) (∏ i, Z i)
    MemLp (tensorEnergy X) 2 μ ∧ MemLp (tensorEnergy Y) 2 μ ∧
      (∫ x, tensorEnergy X x ∂μ) = ∑ i, mean i ∧
      (∫ x, tensorEnergy Y x ∂μ) = ∑ i, mean i ∧
      variance (tensorEnergy X) μ ≤ Fintype.card ι * C ∧
      variance (tensorEnergy Y) μ ≤ Fintype.card ι * C := by
  let μ := fun i => overlapLaw (m i) (X i) (Y i) (Z i)
  letI (i : ι) : IsProbabilityMeasure (μ i) := h_UnitDistance_overlapLaw_probability (m i) (X i) (Y i)
    (hZ i) (hI i) (hnorm i)
  dsimp only
  rw [h_UnitDistance_tensor_overlapLaw m X Y Z hZ hI]
  refine ⟨h_UnitDistance_tensorEnergy_memLp μ X hX, h_UnitDistance_tensorEnergy_memLp μ Y hY, ?_, ?_, ?_, ?_⟩
  · rw [h_UnitDistance_tensorEnergy_integral μ X (fun i => (hX i).integrable (by norm_num))]
    exact Finset.sum_congr rfl (fun i _ => hmeanX i)
  · rw [h_UnitDistance_tensorEnergy_integral μ Y (fun i => (hY i).integrable (by norm_num))]
    exact Finset.sum_congr rfl (fun i _ => hmeanY i)
  · rw [h_UnitDistance_tensorEnergy_variance μ X hX]
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hvX i)
  · rw [h_UnitDistance_tensorEnergy_variance μ Y hY]
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hvY i)
end ProductMoments
end UnitDistance
