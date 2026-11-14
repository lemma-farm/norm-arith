module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Data.Int.Interval

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v9e23ca2b4f17.FalconerThetaGauge.ScalarEnergyBinning ====
public section
set_option autoImplicit false
/-!
# Literal scalar bins in Lemma 7.3

The bins are the manuscript's half-open intervals `[jh,(j+1)h)`, indexed by
all integers. Their partition and the measure decomposition are exact,
including endpoint atoms.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal
namespace FalconerThetaGauge
/-- The actual half-open integer bin of width `h`. -/
def scalarBin (h : ℝ) (j : ℤ) : Set ℝ := Ico ((j : ℝ) * h) ((j + 1 : ℝ) * h)

def scalarBinMass (η : Measure ℝ) (h : ℝ) (j : ℤ) : ℝ≥0∞ := η (scalarBin h j)
/-- The squared bin mass in the binning proof. -/
def scalarBinSquareMass (η : Measure ℝ) (h : ℝ) : ℝ≥0∞ :=
  ∑' j : ℤ, scalarBinMass η h j ^ (2 : ℕ)
/-- The exact small-diagonal pair mass used by Lemma 7.3. -/
def scalarCollisionMass (η ζ : Measure ℝ) (h u : ℝ) : ℝ≥0∞ :=
  η.prod ζ {p : ℝ × ℝ | |p.1 - p.2 - u| ≤ h}

/-- The diagonal rectangles are disjoint and each lies in the true width-`h` collision set. -/
axiom scalarBinSquareMass_le_collision (η : Measure ℝ) [SFinite η]
    {h : ℝ} (hh : 0 < h) : scalarBinSquareMass η h ≤ scalarCollisionMass η η h 0

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v9e23ca2b4f17.FalconerThetaGauge.ScalarEnergyBinningShift ====
public section
set_option autoImplicit false
/-!
# Shift and dilation bounds in Lemma 7.3

The shifted pair sets are actual unions of half-open bin rectangles. Their
mass is an exact discrete correlation, so countable Cauchy--Schwarz proves
the manuscript's constants `4` and `2L+1` without discarding endpoint atoms.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal
namespace FalconerThetaGauge
/-- The exact pairs whose integer bin indices differ by `m`. -/
def scalarBinShiftPairs (h : ℝ) (m : ℤ) : Set (ℝ × ℝ) :=
  ⋃ j : ℤ, scalarBin h j ×ˢ scalarBin h (j - m)
axiom measurableSet_scalarBinShiftPairs (h : ℝ) (m : ℤ) :
    MeasurableSet (scalarBinShiftPairs h m)

/-- A shifted cross-bin correlation is bounded by the two true bin-square masses. -/
axiom measure_scalarBinShiftPairs_le (η ζ : Measure ℝ) [SFinite ζ]
    {h : ℝ} (hh : 0 < h) (m : ℤ) :
    η.prod ζ (scalarBinShiftPairs h m) ≤
      scalarBinSquareMass η h ^ (1 / 2 : ℝ) * scalarBinSquareMass ζ h ^ (1 / 2 : ℝ)
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Examples.Example_0d293a5a98b436452118_ScalarEnergyBinningKernel ====
set_option autoImplicit false
/-!
# The decaying cross-kernel bound in Lemma 7.3(iii)

The positive integer tail is bounded by a finite telescoping calculation.
Countable bin correlations then control the actual two-measure integral.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal
namespace FalconerThetaGauge
/-- The literal polynomially decaying scalar kernel in Lemma 7.3(iii). -/
def scalarBinningKernel (h : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + |p.1 - p.2| / h) ^ (-2 : ℝ))
def scalarBinningShiftWeight (m : ℤ) : ℝ≥0∞ :=
  if m = 0 then 1 else ENNReal.ofReal ((m.natAbs : ℝ) ^ (-2 : ℝ))

/-- The shift weights sum to at most five, which is stronger than the source's ten. -/
axiom tsum_scalarBinningShiftWeight_le_five :
    (∑' m : ℤ, scalarBinningShiftWeight m) ≤ 5

/-- A weighted countable cover by the actual bin-shift rectangles. -/
axiom scalarBinningKernel_le_tsum_indicators {h : ℝ} (hh : 0 < h) (p : ℝ × ℝ) :
    scalarBinningKernel h p ≤ ∑' m : ℤ,
      (scalarBinShiftPairs h m).indicator (fun _ ↦ scalarBinningShiftWeight m) p
/-- Lemma 7.3(iii), with the actual double integral and the source constant ten. -/
theorem lintegral_scalarBinningKernel_le_ten (η ζ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ζ] {h : ℝ} (hh : 0 < h) :
    (∫⁻ p, scalarBinningKernel h p ∂η.prod ζ) ≤
      10 * (scalarCollisionMass η η h 0 * scalarCollisionMass ζ ζ h 0) ^ (1 / 2 : ℝ) := by
  calc
    _ ≤ ∫⁻ p, ∑' m : ℤ, (scalarBinShiftPairs h m).indicator
        (fun _ ↦ scalarBinningShiftWeight m) p ∂η.prod ζ :=
      lintegral_mono (scalarBinningKernel_le_tsum_indicators hh)
    _ = ∑' m : ℤ, scalarBinningShiftWeight m * η.prod ζ (scalarBinShiftPairs h m) := by
      rw [lintegral_tsum (fun m ↦ (measurable_const.indicator
        (measurableSet_scalarBinShiftPairs h m)).aemeasurable)]
      apply tsum_congr
      intro m
      rw [lintegral_indicator (measurableSet_scalarBinShiftPairs h m), setLIntegral_const]
    _ ≤ ∑' m : ℤ, scalarBinningShiftWeight m *
        (scalarBinSquareMass η h ^ (1 / 2 : ℝ) * scalarBinSquareMass ζ h ^ (1 / 2 : ℝ)) :=
      ENNReal.tsum_le_tsum fun m ↦ mul_le_mul' le_rfl (measure_scalarBinShiftPairs_le η ζ hh m)
    _ = (∑' m : ℤ, scalarBinningShiftWeight m) *
        (scalarBinSquareMass η h ^ (1 / 2 : ℝ) * scalarBinSquareMass ζ h ^ (1 / 2 : ℝ)) :=
      ENNReal.tsum_mul_right
    _ ≤ 10 * (scalarCollisionMass η η h 0 ^ (1 / 2 : ℝ) *
        scalarCollisionMass ζ ζ h 0 ^ (1 / 2 : ℝ)) := by
      apply mul_le_mul'
      · exact tsum_scalarBinningShiftWeight_le_five.trans (by norm_num)
      · exact mul_le_mul' (ENNReal.rpow_le_rpow (scalarBinSquareMass_le_collision η hh)
          (by norm_num))
          (ENNReal.rpow_le_rpow (scalarBinSquareMass_le_collision ζ hh)
            (by norm_num))
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
end FalconerThetaGauge
