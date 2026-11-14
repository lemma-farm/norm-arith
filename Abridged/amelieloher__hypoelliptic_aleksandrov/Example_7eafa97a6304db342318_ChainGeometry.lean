module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Set.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.DenselyOrdered

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0d16f1532774.PDEFoundation.Ambient.Basic ====
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

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0d16f1532774.PDEFoundation.Ambient.EuclideanNorm ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Explicit Euclidean norm on native vectors

`PDE.Vec d = Fin d → ℝ` inherits the finite-product supremum norm. This
module supplies the distinct Euclidean dot product, squared norm, and norm
needed by energy estimates.
-/
@[expose] public section
open scoped BigOperators
namespace PDE
/-- The Euclidean dot product on native project vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i
/-- The square of the Euclidean norm on native project vectors. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0d16f1532774.PDEFoundation.Geometry.EuclideanBall.Basic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Round balls on native vectors

Round balls are defined through the explicit Euclidean squared distance, not
the inherited finite-product metric. The squared-radius convention agrees
with the established homogenization API. Consequently, norm-membership and
radius-monotonicity lemmas state the required radius sign assumptions.
-/
@[expose] public section
open scoped Pointwise
namespace PDE
/-- Euclidean squared distance on native vectors. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)
/-- The explicit round Euclidean open ball. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0d16f1532774.HypoellipticAleksandrov.Parabolic.Geometry ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Parabolic time--velocity geometry

This module fixes the explicit Euclidean time--velocity cylinders and their
forward parabolic boundary. The terminal open-ball face is deliberately not a
boundary component.
-/
@[expose] public section
namespace HypoellipticAleksandrov.Parabolic
/-- Time--velocity points in dimension `d`. -/
abbrev TimeVelocity (d : ℕ) := ℝ × PDE.Vec d
end HypoellipticAleksandrov.Parabolic

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0d16f1532774.HypoellipticAleksandrov.Parabolic.HarnackGeometry ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coordinate geometry for the parabolic Harnack argument

The Krylov--Safonov boxes in this file use coordinate cubes.  In particular,
they are not the metric balls inherited by `PDE.Vec d`.
-/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace HypoellipticAleksandrov.Parabolic
noncomputable section
/-- The open coordinate cube of radius `r` about `v₀`. -/
def velocityCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) : Set (PDE.Vec d) :=
  {v | ∀ i : Fin d, |v i - v₀ i| < r}
/-- The closed coordinate cube of radius `r` about `v₀`. -/
def velocityClosedCube {d : ℕ} (v₀ : PDE.Vec d) (r : ℝ) : Set (PDE.Vec d) :=
  {v | ∀ i : Fin d, |v i - v₀ i| ≤ r}
def parabolicClosedBox {d : ℕ} (vartheta r t₀ : ℝ) (v₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Icc t₀ (t₀ + vartheta * r ^ 2) ×ˢ velocityClosedCube v₀ r

end
end HypoellipticAleksandrov.Parabolic

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_7eafa97a6304db342318_ChainGeometry ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Equal-time Harnack links inside the open unit cylinder -/
@[expose] public section
namespace HypoellipticAleksandrov.Parabolic
open Set


set_option linter.unusedVariables false in
/-- A fixed number of links reaches every upper point without crossing the terminal time. -/
theorem unitCylinder_harnack_link_geometry
    (d : ℕ) (hd : 1 ≤ d) (P P' : TimeVelocity d)
    (hP : P ∈ Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
      PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ))
    (hP' : P' ∈ Ioo (3 / 4 : ℝ) 1 ×ˢ
      PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ)) 
    (h_HypoellipticAleksandrov_Parabolic_vecNormSq_sub_le_natCast_mul_sq_of_mem_velocityClosedCube : ∀ {d : ℕ} {v v0 : PDE.Vec d} {r : ℝ},
      v ∈ HypoellipticAleksandrov.Parabolic.velocityClosedCube v0 r →
        PDE.vecNormSq (v - v0) ≤ (↑d : ℝ) * r ^ 2)
    (h_HypoellipticAleksandrov_Parabolic_normSq_lt_quarter_of_mem_halfBall : ∀ {d : ℕ} {w : PDE.Vec d}, w ∈ PDE.euclideanBall 0 (1 / 2) → PDE.vecNormSq w < 1 / 4)
    (h_PDE_convex_euclideanBall : ∀ {d : ℕ} (x₀ : PDE.Vec d) (R : ℝ), Convex ℝ (PDE.euclideanBall x₀ R))
    (h_HypoellipticAleksandrov_Parabolic_coordinate_lt_half_of_mem_halfBall : ∀ {d : ℕ} {w : PDE.Vec d}, w ∈ PDE.euclideanBall 0 (1 / 2) → ∀ (i : Fin d), |w i| < 1 / 2)
    (h_PDE_vecNormSq_add_le : ∀ {d : ℕ} (x y : PDE.Vec d), PDE.vecNormSq (x + y) ≤ 2 * (PDE.vecNormSq x + PDE.vecNormSq y))
    (h_HypoellipticAleksandrov_Parabolic_mem_parabolicClosedBox_iff : ∀ {d : ℕ} {vartheta r t₀ t : ℝ} {v₀ v : PDE.Vec d},
      (t, v) ∈ HypoellipticAleksandrov.Parabolic.parabolicClosedBox vartheta r t₀ v₀ ↔
        t₀ ≤ t ∧
          t ≤ t₀ + vartheta * r ^ 2 ∧ v ∈ HypoellipticAleksandrov.Parabolic.velocityClosedCube v₀ r)
    :
    let m : ℕ := 256 * d
    let dt : ℝ := (P'.1 - P.1) / (m : ℝ)
    let r : ℝ := Real.sqrt dt
    let t : ℕ → ℝ := fun k => P.1 + (k : ℝ) * dt
    let v : ℕ → PDE.Vec d := fun k =>
      P.2 + ((k : ℝ) / (m : ℝ)) • (P'.2 - P.2)
    0 < m ∧ 0 < r ∧ (t 0, v 0) = P ∧ (t m, v m) = P' ∧
    (∀ k < m, t (k + 1) = t k + r ^ 2) ∧
    (∀ k < m, parabolicClosedBox 2 r (t k - r ^ 2) (v k) ⊆
      Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec d) 1) ∧
    (∀ k < m, v (k + 1) ∈ velocityCube (v k) (r / 2)) := by
  let m : ℕ := 256 * d
  let dt : ℝ := (P'.1 - P.1) / (m : ℝ)
  let r : ℝ := Real.sqrt dt
  let t : ℕ → ℝ := fun k => P.1 + (k : ℝ) * dt
  let v : ℕ → PDE.Vec d := fun k =>
    P.2 + ((k : ℝ) / (m : ℝ)) • (P'.2 - P.2)
  change 0 < m ∧ 0 < r ∧ (t 0, v 0) = P ∧ (t m, v m) = P' ∧ _
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hm : 256 ≤ m := by dsimp [m]; omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 256) hm
  have hmreal : (256 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmd : (m : ℝ) = 256 * (d : ℝ) := by simp [m]
  have hgap0 : 1 / 4 < P'.1 - P.1 := by linarith [hP.1.2, hP'.1.1]
  have hgap1 : P'.1 - P.1 < 1 := by linarith [hP.1.1, hP'.1.2]
  have hdt : 0 < dt := div_pos (by linarith) hmpos
  have hmul : (m : ℝ) * dt = P'.1 - P.1 := by
    dsimp [dt]
    field_simp
  have hrsq : r ^ 2 = dt := Real.sq_sqrt hdt.le
  have hr : 0 < r := Real.sqrt_pos.mpr hdt
  have hdtSmall : dt < 1 / 256 := by nlinarith
  have hdSmall : (d : ℝ) * dt < 1 / 256 := by rw [hmd] at hmul; nlinarith
  have htstep : ∀ k : ℕ, t (k + 1) = t k + r ^ 2 := by
    intro k
    simp only [t, Nat.cast_add, Nat.cast_one, hrsq]
    ring
  have hvstep : ∀ k : ℕ, v (k + 1) - v k = (1 / (m : ℝ)) • (P'.2 - P.2) := by
    intro k
    ext i
    simp only [v, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    ring
  have hcenter : ∀ k ≤ m,
      v k ∈ PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ) := by
    intro k hk
    have hkreal : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
    have ha : 0 ≤ (k : ℝ) / (m : ℝ) := div_nonneg (Nat.cast_nonneg _) hmpos.le
    have hb : (k : ℝ) / (m : ℝ) ≤ 1 := (div_le_one₀ hmpos).mpr hkreal
    have hconv := (h_PDE_convex_euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ))
      hP.2 hP'.2 (by linarith : 0 ≤ 1 - (k : ℝ) / (m : ℝ)) ha
      (by ring : (1 - (k : ℝ) / (m : ℝ)) + (k : ℝ) / (m : ℝ) = 1)
    convert hconv using 1
    ext i
    simp only [v, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hrecip : 1 / (m : ℝ) < r / 2 := by
    have hsquare : ((m : ℝ) * r) ^ 2 = (m : ℝ) * (P'.1 - P.1) := by
      calc
        ((m : ℝ) * r) ^ 2 = (m : ℝ) * ((m : ℝ) * dt) := by rw [mul_pow, hrsq]; ring
        _ = _ := by rw [hmul]
    have hlarge : 2 < (m : ℝ) * r := by
      have hpos := mul_pos hmpos hr
      have hprod := mul_lt_mul_of_pos_left hgap0 hmpos
      nlinarith
    apply (div_lt_iff₀ hmpos).mpr
    nlinarith
  refine ⟨by omega, hr, ?_, ?_, fun k _ => htstep k, ?_, ?_⟩
  · simp [t, v]
  · apply Prod.ext
    · dsimp [t]
      linarith
    · simp [v, div_self hmpos.ne', one_smul]
  · intro k hk w hw
    rcases w with ⟨s, w⟩
    rw [h_HypoellipticAleksandrov_Parabolic_mem_parabolicClosedBox_iff] at hw
    have hkreal : (k : ℝ) ≤ (m : ℝ) - 1 := by
      have hs : ((k + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
      push_cast at hs
      linarith
    have htk0 : P.1 ≤ t k := by
      dsimp [t]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hdt.le)
    have htk1 : t k + dt ≤ P'.1 := by
      have hle := mul_le_mul_of_nonneg_right hkreal hdt.le
      dsimp [t]
      nlinarith
    have hnorm := h_HypoellipticAleksandrov_Parabolic_normSq_lt_quarter_of_mem_halfBall (hcenter k (Nat.le_of_lt hk))
    have hdisp := h_HypoellipticAleksandrov_Parabolic_vecNormSq_sub_le_natCast_mul_sq_of_mem_velocityClosedCube hw.2.2
    rw [hrsq] at hdisp
    have hsum := h_PDE_vecNormSq_add_le (v k) (w - v k)
    rw [add_sub_cancel] at hsum
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hrsq] at hw
      linarith [hP.1.1, hw.1]
    · rw [hrsq] at hw
      linarith [hP'.1.2, hw.2.1]
    · change PDE.euclideanSqDist w 0 < 1 ^ 2
      simpa [PDE.euclideanSqDist] using (show PDE.vecNormSq w < 1 by nlinarith)
  · intro k _ i
    have hcoord0 := h_HypoellipticAleksandrov_Parabolic_coordinate_lt_half_of_mem_halfBall hP.2 i
    have hcoord1 := h_HypoellipticAleksandrov_Parabolic_coordinate_lt_half_of_mem_halfBall hP'.2 i
    have hcoord : |P'.2 i - P.2 i| < 1 := by
      have hab := abs_sub_le (P'.2 i) 0 (P.2 i)
      simp only [sub_zero, zero_sub, abs_neg] at hab
      linarith
    have hstepi := congrFun (hvstep k) i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hstepi
    rw [hstepi, abs_mul, abs_of_pos (one_div_pos.mpr hmpos)]
    calc
      (1 / (m : ℝ)) * |P'.2 i - P.2 i| < (1 / (m : ℝ)) * 1 :=
        mul_lt_mul_of_pos_left hcoord (one_div_pos.mpr hmpos)
      _ = 1 / (m : ℝ) := mul_one _
      _ < r / 2 := hrecip
end HypoellipticAleksandrov.Parabolic
