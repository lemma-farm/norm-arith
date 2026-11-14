module

public import Mathlib

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.vb788de2423fc.DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy ====
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

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.vb788de2423fc.DedekindZetaZeroFree.Analysis.Sobolev.Approximation.CompactInteriorH1Density ====
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

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Examples.Example_faa369ba8988963a9f58_CompactMollificationBounds ====
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1500000
namespace DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior
open MeasureTheory KPContLocalNorm
open scoped Convolution

set_option linter.unusedVariables false in
theorem convolution_integral_norm_sq_le {n : ℕ}
    (g : Space n → ℂ) (hg : MemLp g 2 volume) (hg1 : Integrable g volume)
    (φ : ContDiffBump (0 : Space n)) 
    (h_DedekindZetaZeroFree_KPLocalCubeSobolevJets_Interior_norm_averaged_translateL2_le : ∀ {n : ℕ} (f : ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.MeasureSpace.volume)) (φ : ContDiffBump 0),
      ‖∫ (t : DedekindZetaZeroFree.KPContLocalNorm.Space n),
            φ.normed MeasureTheory.MeasureSpace.volume t •
              DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2
                f t‖ ≤
        ‖f‖)
    (h_DedekindZetaZeroFree_KPContLocalEnergy_SobolevEnergyEstimates_CompactApproximation_averaged_translateL2_ae : ∀ {n : ℕ} (g : DedekindZetaZeroFree.KPContLocalNorm.Space n → ℂ)
      (hg : MeasureTheory.MemLp g 2 MeasureTheory.MeasureSpace.volume),
      MeasureTheory.Integrable g MeasureTheory.MeasureSpace.volume →
        ∀ (φ : ContDiffBump 0),
          (↑(↑(∫ (t : DedekindZetaZeroFree.KPContLocalNorm.Space n),
                      φ.normed MeasureTheory.MeasureSpace.volume t •
                        DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2
                          (MeasureTheory.MemLp.toLp g hg) t) :
                  DedekindZetaZeroFree.KPContLocalNorm.Space n →ₘ[MeasureTheory.MeasureSpace.volume]
                    ℂ) :
              DedekindZetaZeroFree.KPContLocalNorm.Space n → ℂ) =ᵐ[MeasureTheory.MeasureSpace.volume]
            MeasureTheory.convolution (φ.normed MeasureTheory.MeasureSpace.volume) g
              (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.MeasureSpace.volume)
    :
    (∫ x, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ^ 2) ≤
      ‖hg.toLp g‖ ^ 2 := by
  let a : Lp ℂ 2 (volume : Measure (Space n)) :=
    ∫ t, φ.normed volume t • KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.translateL2 (hg.toLp g) t
  have hae := h_DedekindZetaZeroFree_KPContLocalEnergy_SobolevEnergyEstimates_CompactApproximation_averaged_translateL2_ae g hg hg1 φ
  have heq : (∫ x, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ^ 2) = ‖a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  rw [heq]
  exact pow_le_pow_left₀ (norm_nonneg a) (h_DedekindZetaZeroFree_KPLocalCubeSobolevJets_Interior_norm_averaged_translateL2_le _ φ) 2
end DedekindZetaZeroFree.KPLocalCubeSobolevJets.Interior
end
