module
public import Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.vb788de2423fc.DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates.Raw
open MeasureTheory
open KPContLocalNorm
def zeroIndex (n k : ℕ) : MultiIndex n k := ⟨fun _ => 0, by simp⟩
def firstIndex {n : ℕ} (i : Fin n) : MultiIndex n 1 :=
  ⟨fun j => if j = i then 1 else 0, by
    simp only [apply_ite Fin.val, Fin.val_one, Fin.val_zero]
    simp⟩
def value {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k) : BallL2 B :=
  u.derivatives (zeroIndex n k)
end DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates.Raw
end
