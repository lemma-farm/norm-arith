module
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.GaussSum.RamifiedTracePhase
public import Mathlib
set_option autoImplicit false
@[expose] public section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace ShortDraftLatticeCount
def q (x : ℤ × ℤ) : ℤ := x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2
end ShortDraftLatticeCount
namespace ActualEisensteinCubic
open ShortDraftCusp
end ActualEisensteinCubic
namespace ShortDraftCusp
variable {R : Type*} [CommRing R]
end ShortDraftCusp
namespace ShortDraftLatticeCount
open ActualEisensteinCoordinates
theorem coords_eval (a b : ℤ) :
    coords (eval a b) = (a, b) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext h.1 h.2
theorem qO_mul (x y : O) :
    q (coords (x * y)) = q (coords x) * q (coords y) := by
  have hxy : x * y = eval
      ((coords x).1 * (coords y).1 - (coords x).2 * (coords y).2)
      ((coords x).1 * (coords y).2 + (coords x).2 * (coords y).1 -
        (coords x).2 * (coords y).2) := by
    calc
      x * y = eval (coords x).1 (coords x).2 *
          eval (coords y).1 (coords y).2 := by rw [eval_coords, eval_coords]
      _ = _ := eval_mul _ _ _ _
  rw [hxy, coords_eval]
  exact ShortDraft.eisenstein_norm_mul (coords x) (coords y)
theorem qO_nonneg (x : O) : 0 ≤ q (coords x) := by
  exact ShortDraft.eisenstein_norm_nonneg (coords x)
def qNat (x : O) : ℕ := (q (coords x)).toNat
theorem qNat_mul (x y : O) : qNat (x * y) = qNat x * qNat y := by
  unfold qNat
  rw [qO_mul]
  exact Int.toNat_mul (qO_nonneg x) (qO_nonneg y)
end ShortDraftLatticeCount
namespace AnalyticBridge
end AnalyticBridge
namespace ShortDraftLatticeCount
open ActualEisensteinCoordinates
end ShortDraftLatticeCount
namespace IdealGaussCRT
open AddChar MulChar
end IdealGaussCRT
namespace ActualEisensteinCubic
section
open ShortDraftLatticeCount
end
open AddChar MulChar
end ActualEisensteinCubic
end
end OAI
