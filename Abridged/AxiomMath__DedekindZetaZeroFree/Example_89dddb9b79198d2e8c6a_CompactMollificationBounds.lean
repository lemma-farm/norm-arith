module

public import Mathlib

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.vf9c440f97c5d.DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy ====
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace DedekindZetaZeroFree.KPContLocalNorm
open MeasureTheory Filter Topology TopologicalSpace
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
structure LocalBall (n : ℕ) where
  dimension_pos : 0 < n
  center : Space n
  radius : ℝ
  radius_pos : 0 < radius
def LocalBall.carrier {n : ℕ} (B : LocalBall n) : Set (Space n) :=
  Metric.ball B.center B.radius

abbrev BallL2 {n : ℕ} (B : LocalBall n) :=
  Lp ℂ 2 (volume.restrict B.carrier)

end DedekindZetaZeroFree.KPContLocalNorm
end

end
end

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.vf9c440f97c5d.DedekindZetaZeroFree.Analysis.Sobolev.Approximation.CompactInteriorH1Density ====
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates
open MeasureTheory KPContLocalNorm  Filter Topology
namespace CompactApproximation
open scoped Convolution Pointwise
def compactZeroExtension {n : ℕ} {B : LocalBall n} (K : Set (Space n))
    (f : BallL2 B) : Space n → ℂ := K.indicator (fun x => f x)

def shrinkingBump {n : ℕ} (δ : ℝ) (hδ : 0 < δ) (m : ℕ) :
    ContDiffBump (0 : Space n) :=
  ⟨(δ / (m + 1 : ℝ)) / 2, δ / (m + 1 : ℝ),
    half_pos (div_pos hδ (by positivity)),
    half_lt_self (div_pos hδ (by positivity))⟩

def translateL2 {n : ℕ} (f : Lp ℂ 2 (volume : Measure (Space n))) (t : Space n) :
    Lp ℂ 2 (volume : Measure (Space n)) :=
  Lp.compMeasurePreserving (fun x => x - t) (measurePreserving_sub_right volume t) f
 

 
 

 

end CompactApproximation
open scoped Convolution

end DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates
end

end
end

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Examples.Example_89dddb9b79198d2e8c6a_CompactMollificationBounds ====
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1500000
namespace DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior
open MeasureTheory KPContLocalNorm
open scoped Convolution
set_option linter.unusedVariables false in
theorem norm_averaged_translateL2_le {n : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Space n))) (φ : ContDiffBump (0 : Space n)) 
    (h_DedekindZetaZeroFree_KPContLocalEnergy_SobolevEnergyEstimates_CompactApproximation_translateL2_norm : ∀ {n : ℕ} (f : ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.MeasureSpace.volume))
      (t : DedekindZetaZeroFree.KPContLocalNorm.Space n),
      ‖DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 f
            t‖ =
        ‖f‖)
    :
    ‖∫ t, φ.normed volume t • KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 f t‖ ≤ ‖f‖ := by
  calc
    _ ≤ ∫ t, ‖φ.normed volume t • KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 f t‖ := norm_integral_le_integral_norm _
    _ = ∫ t, φ.normed volume t * ‖f‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t), h_DedekindZetaZeroFree_KPContLocalEnergy_SobolevEnergyEstimates_CompactApproximation_translateL2_norm]
    _ = ‖f‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]
end DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior
end
