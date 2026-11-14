module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.TietzeExtension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Topology.Metrizable.Urysohn

-- ==== Examples.adbrw__HS_proof.Dependencies.vbf80bd479a67.HSFormal.PadicSubgroups ====
public section
@[expose] public section
/-!
# Closed additive subgroups of the p-adic integers

Integer density makes a closed additive subgroup of `ℤ_[p]` stable under every
`ℤ_[p]`-scalar. It is therefore an ideal, and the discrete valuation ring
classification identifies each nonzero such subgroup with `p^n ℤ_[p]`.

The action-kernel results below are conditional on a nontrivial kernel. They do
not establish that a p-adic action on a manifold has a nontrivial kernel.
-/
namespace HSFormal
open Topology
/-- The additive subgroup `p^n ℤ_[p]`. -/
noncomputable def padicPowerSubgroup (p : ℕ) [Fact p.Prime] (n : ℕ) : AddSubgroup ℤ_[p] :=
  (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]).toAddSubgroup
section ClosedSubgroups
variable {p : ℕ} [Fact p.Prime]

end ClosedSubgroups
section ActionKernel
variable {p : ℕ} [Fact p.Prime] {X : Type*} [AddAction ℤ_[p] X]
variable [TopologicalSpace X] [T2Space X] [ContinuousVAdd ℤ_[p] X]
end ActionKernel
end HSFormal

end
end

-- ==== Examples.adbrw__HS_proof.Dependencies.vbf80bd479a67.HSFormal.SpherePinch ====
public section
@[expose] public section
/-!
# The oriented pinch and the round target sphere (Section 7, L492–524)

The target sphere `Sⁿ` of Section 7 is the one-point compactification `OnePoint ℝⁿ` of
coordinate space.

* `HSFormal.pinch ρ`: the oriented pinch `s_ρ : ℝⁿ → Sⁿ`, `v ↦ v / (ρ - ‖v‖)` on `B(0,ρ)` and `∞`
  outside (L492). It is continuous, and a homeomorphism of `B(0,ρ)` onto `Sⁿ ∖ {∞}`
  (`HSFormal.pinchBallHomeomorph`).
* `HSFormal.pinchMap`: its extension `Sⁿ → Sⁿ` by `∞ ↦ ∞`, and `HSFormal.pinchHomotopy`, an
  explicit homotopy rel `∞` from the identity of `Sⁿ` to it (so the pinch has degree one).
* `HSFormal.roundSphere`: stereographic identification of `Sⁿ` with the unit sphere of `ℝⁿ⁺¹`;
  `HSFormal.roundDist` is the induced round (chordal) metric, for which `s_ρ(0)` and `∞` are
  antipodal at distance `2` (L519).
* `HSFormal.SphereSelfMapSurjective`: the classical non-contractibility of spheres, isolated as an
  explicit hypothesis (degree theory is not available in mathlib).
-/
noncomputable section
open Set Filter Metric Module OnePoint
open Topology
open scoped unitInterval
namespace HSFormal
section DivOrInfty
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- `a / d` in the one-point compactification, and `∞` when `d ≤ 0`. -/
def divOrInfty (d : ℝ) (a : E) : OnePoint E :=
  if 0 < d then ((d⁻¹ • a : E) : OnePoint E) else ∞

end DivOrInfty
section Extension
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
end Extension
section Pinch
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The oriented pinch `s_ρ` (L492): `v ↦ v / (ρ - ‖v‖)` on `B(0,ρ)`, and `∞` outside. -/
def pinch (ρ : ℝ) (v : E) : OnePoint E := divOrInfty (ρ - ‖v‖) v

variable [ProperSpace E]
end Pinch
section RoundSphere
/-- The north pole of the unit sphere in `ℝⁿ⁺¹`. -/
def northPole (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
set_option linter.unusedVariables false in
axiom _root_.HSFormal.norm_northPole : ∀ (n : ℕ), ‖HSFormal.northPole n‖ = 1
/-- A linear identification of `ℝⁿ` with the equatorial hyperplane. -/
def hyperplaneEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] (ℝ ∙ northPole n)ᗮ :=
  haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by
    rw [Submodule.finrank_orthogonal_span_singleton (n := n) (by
      intro h; have := norm_northPole n; rw [h, norm_zero] at this; exact zero_ne_one this)]
    simp)).some
/-- The stereographic identification of `Sⁿ = OnePoint ℝⁿ` with the round unit sphere of `ℝⁿ⁺¹`;
`∞` goes to the north pole and `0` to the south pole. -/
def roundSphere (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  (hyperplaneEquiv n).toHomeomorph.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere (norm_northPole n))
def roundDist {n : ℕ} (z z' : OnePoint (EuclideanSpace ℝ (Fin n))) : ℝ :=
  dist (roundSphere n z) (roundSphere n z')
end RoundSphere
end HSFormal

end
end
end

-- ==== Examples.adbrw__HS_proof.Dependencies.vbf80bd479a67.HSFormal.CharacterDetector ====
public section
@[expose] public section
/-!
# Character averages and continuous orbit detectors

The measure below is the actual normalized Haar measure on a compact group. Averaging
with a circle character gives a continuous equivariant complex-valued function. A
character trivial on a point stabilizer descends to the compact orbit; Tietze extension
then supplies an averaging input whose average equals one at that point.

These are topological prerequisites for the detector in Section 7 of `fullHS_final.md`.
They do not assume the proposed controlled realization or assert a Hilbert–Smith theorem.
-/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Topology
namespace HSFormal
section NormalizedHaar
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
/-- Haar measure normalized on the whole compact group, rather than on an unspecified
positive compact neighborhood. -/
def normalizedCompactHaar : Measure G :=
  Measure.haarMeasure (⊤ : PositiveCompacts G)

end NormalizedHaar
section Average
variable {G X : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MetricSpace X] [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X]
end Average
section OrbitExtension
variable {G X : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace G] [CompactSpace G] [MetricSpace X] [ContinuousSMul G X]
end OrbitExtension
section PointDetector
variable {G X : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MetricSpace X] [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X]
end PointDetector
end HSFormal

end
end
end

-- ==== Examples.adbrw__HS_proof.Dependencies.vbf80bd479a67.HSFormal.ChartData ====
public section
@[expose] public section
/-!
# Section 7: the chart, the subgroup `H`, the averaged coordinate and the sphere map

Fixed data of Section 7 of `fullHS_final.md` (L456–517) for an effective jointly continuous
`ℤ_[p]`-action on a manifold without boundary; the package is completed in `HSFormal.FixedData`.

* `HSFormal.PadicTail`: `H_j` as a compact multiplicative group, with normalized Haar measure.
* `HSFormal.padicChar`: the quotient character `χ : H_j → H_j/H_{j+1} ≅ C_p ⊆ S¹` (L517).
* `HSFormal.ChartData`: the free point `x₀`, a chart `φ` with `φ x₀ = 0`, `B(0,4) ⊆ φ(U)`, and
  `H = H_j` with displacement `≤ D < 1/64` on `φ⁻¹ B̄(0,2)` (7.1). Derived: `Ω = H · φ⁻¹ B(0,2)`
  (L468), the Haar average `F₀` (7.2) with (7.3), and the carrier `Z⁺ = F₀⁻¹ B̄(0,ρ₊)` (7.4).
* `HSFormal.exists_equivariant_sphere_map`: the equivariant map `ρ̃ : Z⁺ → T = S^{2m-1}` (7.7).
  It is obtained from the repo's character detector (`exists_finite_character_detector`), with
  the stabilizer hypothesis supplied by `padicStabilizer_le_nextPower_of_not_fixed`, instead of the
  paper's partition of unity on the free `C_p`-space `Z⁺/H'`. Both give a continuous map
  `Z⁺ → S^{2m-1} ⊆ ℂ^m` with `ρ̃(hx) = χ(h) ρ̃(x)`; here `ρ̃` is even defined and continuous on an
  open neighbourhood of `Z⁺`, and equivariant on all of `M`.
-/
noncomputable section
open Set Filter Metric MeasureTheory OnePoint Topology
open scoped unitInterval
namespace HSFormal
/-! ### The tail `H_j` as a compact multiplicative group, and the quotient character -/
/-- The tail `H_j = p^j ℤ_[p]`, written multiplicatively (for Haar averages and characters). -/
def PadicTail (p : ℕ) [Fact p.Prime] (j : ℕ) : Type :=
  Multiplicative (padicPowerSubgroup p j)
namespace PadicTail
variable {p : ℕ} [Fact p.Prime] {j : ℕ}
instance : CommGroup (PadicTail p j) := inferInstanceAs (CommGroup (Multiplicative _))
instance : TopologicalSpace (PadicTail p j) :=
  inferInstanceAs (TopologicalSpace (Multiplicative _))
set_option linter.unusedVariables false in
axiom _root_.HSFormal.PadicTail.instIsTopologicalGroup : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {j : ℕ}, IsTopologicalGroup (HSFormal.PadicTail p j)
attribute [instance] _root_.HSFormal.PadicTail.instIsTopologicalGroup
set_option linter.unusedVariables false in
axiom _root_.HSFormal.PadicTail.instCompactSpace : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {j : ℕ}, CompactSpace (HSFormal.PadicTail p j)
attribute [instance] _root_.HSFormal.PadicTail.instCompactSpace

instance : MeasurableSpace (PadicTail p j) := borel _
set_option linter.unusedVariables false in
axiom _root_.HSFormal.PadicTail.instBorelSpace : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {j : ℕ}, BorelSpace (HSFormal.PadicTail p j)
attribute [instance] _root_.HSFormal.PadicTail.instBorelSpace
/-- The underlying p-adic integer. -/
def val (g : PadicTail p j) : ℤ_[p] :=
  ((Multiplicative.toAdd g : padicPowerSubgroup p j) : ℤ_[p])

instance {X : Type*} [AddAction ℤ_[p] X] : MulAction (PadicTail p j) X where
  smul g x := g.val +ᵥ x
  one_smul := zero_vadd ℤ_[p]
  mul_smul g h x := add_vadd g.val h.val x

end PadicTail
section Character
variable {p : ℕ} [Fact p.Prime] {j : ℕ}
set_option linter.unusedVariables false in
axiom _root_.HSFormal.instNeZeroNatHPowOfFactPrime_examples : ∀ (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ), NeZero (p ^ k)
attribute [instance] _root_.HSFormal.instNeZeroNatHPowOfFactPrime_examples
/-- The character `ℤ_[p] → ℤ/p^{j+1} → S¹`. On `H_j` it is the quotient character
`χ : H_j → H_j/H_{j+1} ≅ C_p ⊆ S¹` of (7.7), see `padicChar_eq_one_iff` and
`padicChar_pow_eq_one`. -/
def padicChar (p : ℕ) [Fact p.Prime] (j : ℕ) : AddChar ℤ_[p] Circle :=
  ZMod.toCircle.compAddMonoidHom (PadicInt.toZModPow (j + 1)).toAddMonoidHom
end Character
/-! ### Charts and uniform chart displacement -/
section Chart
variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M]
end Chart
/-! ### The chart, the subgroup `H` and the averaged coordinate (7.1)–(7.3) -/
/-- The data `(x₀, φ, H = H_j, D)` of L458–466. -/
structure ChartData (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type*) [TopologicalSpace M]
    [AddAction ℤ_[p] M] where
  /-- A free point (L458). -/
  x₀ : M
  stabilizer_x₀ : AddAction.stabilizer ℤ_[p] x₀ = ⊥
  /-- A chart centred at `x₀` whose image contains `B(0,4)` (L460). -/
  φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  x₀_mem_source : x₀ ∈ φ.source
  φ_x₀ : φ x₀ = 0
  ball_subset_target : ball 0 4 ⊆ φ.target
  /-- `H = H_j` and the displacement bound `D` of (7.1). -/
  j : ℕ
  D : ℝ
  D_nonneg : 0 ≤ D
  D_lt : D < 1 / 64
  vadd_mem_source : ∀ h ∈ padicPowerSubgroup p j, ∀ x ∈ φ.source, ‖φ x‖ ≤ 2 →
    h +ᵥ x ∈ φ.source
  displacement_le : ∀ h ∈ padicPowerSubgroup p j, ∀ x ∈ φ.source, ‖φ x‖ ≤ 2 →
    ‖φ (h +ᵥ x) - φ x‖ ≤ D
namespace ChartData
variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (c : ChartData p n M)
/-- `H = H_j = p^j ℤ_[p]`. -/
abbrev H : AddSubgroup ℤ_[p] := padicPowerSubgroup p c.j
abbrev fixH : Set M := AddAction.fixedPoints (padicPowerSubgroup p c.j) M
/-- `Ω = H · φ⁻¹ B(0,2)` (L468). -/
def Ω : Set M := {x | ∃ h ∈ c.H, h +ᵥ x ∈ c.φ.source ∧ ‖c.φ (h +ᵥ x)‖ < 2}
/-- The averaged coordinate `F₀(x) = ∫_H φ(hx) dμ(h)` for normalized Haar measure (7.2). -/
def F₀ (x : M) : EuclideanSpace ℝ (Fin n) :=
  ∫ g, c.φ (g • x) ∂normalizedCompactHaar (PadicTail p c.j)
def carrier (ρplus : ℝ) : Set M := c.Ω ∩ c.F₀ ⁻¹' closedBall 0 ρplus

end ChartData
/-! ### The equivariant sphere map (7.7) -/
section SphereMap
variable {p : ℕ} [Fact p.Prime] {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
end SphereMap
end HSFormal

end
end
end

-- ==== Examples.adbrw__HS_proof.Examples.Example_55ba1bb953ec74f0d2c2_FixedData ====
@[expose] public section
/-!
# Section 7: the fixed geometric data from a hypothetical effective action

`HSFormal.FixedData` packages the fixed data of Section 7 of `fullHS_final.md` (L456–539) in the
paper's choice order `(x₀, chart, H) ≺ (ρ₊, ρ, f, Z⁺, T, ρ̃, r, R, t, u) ≺ K_i`:

* the fields are the free choices, with their defining properties;
* `Ω`, `F₀`, `Z⁺`, `f`, `fhat`, `Z₀`, `Z` are derived definitions, given by the paper's formulas;
* the properties (7.1)–(7.9) are theorems below;
* `HSFormal.exists_fixedData`: the data exist for every effective jointly continuous
  `ℤ_[p]`-action on a connected manifold without boundary, given Montgomery's theorem
  `HSFormal.PointwisePeriodicIsPeriodic`.

Degree one (L500) is proved in its homotopy form: the compactified map `fhat` is homotopic rel `∞`
to the identity of `Sⁿ = OnePoint ℝⁿ`, through the homotopy (7.6) and the scaling homotopy of the
pinch. The only further consequence drawn here, `Z⁺ ≠ ∅`, uses the non-contractibility of spheres,
isolated as the explicit hypothesis `HSFormal.SphereSelfMapSurjective`.
-/
noncomputable section
open Set Filter Metric MeasureTheory OnePoint Topology
open scoped unitInterval
namespace HSFormal
/-- The fixed data of Section 7 for an action of `ℤ_[p]` on `M` with charts in `ℝⁿ`. -/
structure FixedData (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type*) [TopologicalSpace M]
    [AddAction ℤ_[p] M] extends ChartData p n M where
  /-- `ρ₊ < 1/4` such that `B̄(0,ρ₊)` misses `Fix(H)` (L483). -/
  ρplus : ℝ
  ρplus_pos : 0 < ρplus
  ρplus_lt : ρplus < 1 / 4
  notMem_fixH : ∀ x ∈ φ.source, ‖φ x‖ ≤ ρplus → x ∉ toChartData.fixH
  /-- The pinch radius `0 < ρ < ρ₊` (L492). -/
  ρ : ℝ
  ρ_pos : 0 < ρ
  ρ_lt : ρ < ρplus
  /-- The equivariant map `ρ̃ : Z⁺ → T = S^{2m-1} ⊆ ℂ^m` of (7.7), continuous with values in `T`
  on an open neighbourhood of `Z⁺`. -/
  m : ℕ
  ρtilde : M → EuclideanSpace ℂ (Fin m)
  ρtilde_spec : ∃ U, IsOpen U ∧ toChartData.carrier ρplus ⊆ U ∧ ContinuousOn ρtilde U ∧
    ∀ x ∈ U, ‖ρtilde x‖ = 1
  ρtilde_vadd : ∀ h ∈ padicPowerSubgroup p j, ∀ x,
    ρtilde (h +ᵥ x) = (padicChar p j h : ℂ) • ρtilde x
  /-- The radii `0 < r < R < t < u < d(y, ∞)` of (7.8), for the round metric, `y = s_ρ(0)`. -/
  r : ℝ
  R : ℝ
  t : ℝ
  u : ℝ
  r_pos : 0 < r
  r_lt_R : r < R
  R_lt_t : R < t
  t_lt_u : t < u
  u_lt : u < roundDist (pinch ρ (0 : EuclideanSpace ℝ (Fin n))) ∞
namespace FixedData
variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (d : FixedData p n M)

def chartHomotopyFun (q : I × EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n)) :=
  if ‖q.2‖ < 2 then
    pinch d.ρ ((1 - (q.1 : ℝ)) • d.F₀ (d.φ.symm q.2) + (q.1 : ℝ) • q.2)
  else ∞
section Action
variable [ContinuousVAdd ℤ_[p] M]
set_option linter.unusedVariables false in
axiom _root_.HSFormal.FixedData.norm_F₀_symm_sub_le.{w_u_1} : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {n : ℕ} {M : Type w_u_1} [inst_1 : TopologicalSpace M]
  [inst_2 : AddAction ℤ_[p] M] (d : HSFormal.FixedData p n M) [ContinuousVAdd ℤ_[p] M]
  {v : EuclideanSpace ℝ (Fin n)},
  ‖v‖ < 2 → ‖d.F₀ ((↑d.φ.symm : EuclideanSpace ℝ (Fin n) → M) v) - v‖ ≤ 2 * d.D
set_option linter.unusedVariables false in
/-- (7.6) is `∞` outside the fixed compact set `B̄(0, ρ + 2D)`, uniformly in `t` (L507). -/
theorem chartHomotopyFun_eq_infty {q : I × EuclideanSpace ℝ (Fin n)}
    (hq : d.ρ + 2 * d.D < ‖q.2‖) 
    (h_HSFormal_pinch_of_le : ∀ {E : Type} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {ρ : ℝ} {v : E},
      ρ ≤ ‖v‖ → HSFormal.pinch ρ v = OnePoint.infty)
    : d.chartHomotopyFun q = ∞ := by
  obtain ⟨t, v⟩ := q
  simp only at hq
  unfold chartHomotopyFun
  split_ifs with h2
  · apply h_HSFormal_pinch_of_le
    set F := d.F₀ (d.φ.symm v)
    have hFv := d.norm_F₀_symm_sub_le h2
    have ht0 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.2 t.2.2
    have hw : v = ((1 - (t : ℝ)) • F + (t : ℝ) • v) - (1 - (t : ℝ)) • (F - v) := by
      simp only [smul_sub, sub_smul, one_smul]
      abel
    have h := norm_sub_le ((1 - (t : ℝ)) • F + (t : ℝ) • v) ((1 - (t : ℝ)) • (F - v))
    rw [← hw, norm_smul, Real.norm_of_nonneg ht0] at h
    nlinarith [mul_nonneg t.2.1 (norm_nonneg (F - v))]
  · rfl
section Homotopy
end Homotopy
end Action
end FixedData
section Existence
end Existence
end HSFormal
