/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Mathlib
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismTransport
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueRoots
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueQuotient
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerLift
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerDecomposition
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
Develops quotients of valuation-ring units by higher principal units and compares their first
layer with residue-field units.
-/
namespace LocalFieldTheory
open ValuationTheory
noncomputable section
open scoped BigOperators
universe u v
namespace DiscreteValuationField
namespace CompleteDVF
variable {K : Type u} [Field K]
namespace higherPrincipalUnitGroup
open ValuationTheory.DiscreteValuationField.DVF
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
def quotientUnitHom (n : ℕ) :
    F.valuationSubringˣ →*
      (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ :=
  Units.map (Ideal.Quotient.mk (F.maximalIdeal ^ n))
theorem quotientUnitHom_ker_eq (n : ℕ) :
    (higherPrincipalUnitGroup.quotientUnitHom F n).ker =
      higherPrincipalUnitGroup F n := by
  ext u
  rw [MonoidHom.mem_ker, higherPrincipalUnitGroup.mem_iff]
  constructor
  · intro hu
    have hval := congrArg
      (fun z : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ =>
        (z : F.valuationSubring ⧸ F.maximalIdeal ^ n)) hu
    change
      Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
        1 at hval
    have hmk :
        Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
          Ideal.Quotient.mk (F.maximalIdeal ^ n)
            (1 : F.valuationSubring) := by
      simpa using hval
    exact
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n) (u : F.valuationSubring)
        (1 : F.valuationSubring)).1 hmk
  · intro hu
    apply Units.ext
    change
      Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
        1
    simpa using
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n) (u : F.valuationSubring)
        (1 : F.valuationSubring)).2 hu
/-- First-isomorphism form of unit reduction modulo `m^n`: `O^*/U^n` is the
range of the unit group of `O/m^n`. -/
noncomputable def unitsModHigherPrincipalUnitGroupEquivRange (n : ℕ) :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n ≃*
      (higherPrincipalUnitGroup.quotientUnitHom F n).range :=
  (QuotientGroup.quotientMulEquivOfEq
    (higherPrincipalUnitGroup.quotientUnitHom_ker_eq F n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (higherPrincipalUnitGroup.quotientUnitHom F n))
theorem maximalIdeal_fg :
    F.maximalIdeal.FG := by
  rcases F.exists_uniformizer with ⟨pi, hpi⟩
  refine ⟨{pi}, ?_⟩
  simpa using (F.maximalIdeal_eq_span_uniformizer hpi).symm
/-- If the residue field is finite, then every quotient by a power of the
maximal ideal is finite. -/
theorem finite_quotient_maximalIdeal_pow_of_finite_residue
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n) := by
  have : Finite (F.valuationSubring ⧸ F.maximalIdeal) := by
    change Finite F.residueField
    infer_instance
  exact Ideal.finite_quotient_pow
    (I := F.maximalIdeal) (higherPrincipalUnitGroup.maximalIdeal_fg F) n
/-- Finite-residue complete DVFs have finite unit quotients `O^*/U^n`. -/
theorem finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) := by
  have : Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n) :=
    higherPrincipalUnitGroup.finite_quotient_maximalIdeal_pow_of_finite_residue
      F n
  exact
    Finite.of_equiv
      ((higherPrincipalUnitGroup.quotientUnitHom F n).range)
      (higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupEquivRange F n).symm
/-- The type in `Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n)` is finite. -/
noncomputable instance quotientMaximalIdealPowFinite
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n) :=
  higherPrincipalUnitGroup.finite_quotient_maximalIdeal_pow_of_finite_residue F n
/-- The type in `Finite (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n)` is finite. -/
noncomputable instance unitsModHigherPrincipalUnitGroupFinite
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) :=
  higherPrincipalUnitGroup.finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
    F n
theorem finite_principalUnitSubquotient_of_finite_residue
    [Finite F.residueField] (m n : ℕ) :
    Finite (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m)) := by
  let : Finite
      (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) := by
    exact
      higherPrincipalUnitGroup.finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
        F n
  let f : higherPrincipalUnitGroup F m →*
      F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n :=
    (QuotientGroup.mk' (higherPrincipalUnitGroup F n)).comp
      (higherPrincipalUnitGroup F m).subtype
  have hker : f.ker =
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk' (higherPrincipalUnitGroup F n)
        (x : F.valuationSubringˣ) = 1 ↔
      (x : F.valuationSubringˣ) ∈ higherPrincipalUnitGroup F n
    exact QuotientGroup.eq_one_iff
      (N := higherPrincipalUnitGroup F n) (x : F.valuationSubringˣ)
  let e : (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m)) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  exact Finite.of_equiv f.range e.symm
/--
The type in `Finite (higherPrincipalUnitGroup F m ⧸ (higherPrincipalUnitGroup F n).subgroupOf
(higherPrincipalUnitGroup F m))` is finite.
-/
noncomputable instance principalUnitSubquotientFinite
    [Finite F.residueField] (m n : ℕ) :
    Finite (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m)) :=
  higherPrincipalUnitGroup.finite_principalUnitSubquotient_of_finite_residue
    F m n
/-- The concrete principal-unit filtration as the abstract filtration API. -/
def toPrincipalUnitFiltration :
    AntitoneSubgroupFiltration F.valuationSubringˣ where
  subgroup := higherPrincipalUnitGroup F
  antitone := fun h => higherPrincipalUnitGroup.antitone F h
noncomputable instance toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite
    [Finite F.residueField] (m n : ℕ) :
    Finite
      ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotient
        m n) := by
  let U := higherPrincipalUnitGroup.toPrincipalUnitFiltration F
  exact Finite.of_equiv
    (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m))
    (U.principalUnitSubquotientConcreteEquiv m n).symm.toEquiv
/-! ### Successive principal-unit quotients -/
/-- The adjacent quotient `U^n/U^(n+1)` for the concrete complete-DVF
principal-unit filtration. -/
def principalUnitSuccQuot (n : ℕ) : Type u :=
  higherPrincipalUnitGroup F n ⧸
    (higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)
/--
Equips the target with its canonical `CommGroup` structure, namely `CommGroup
(higherPrincipalUnitGroup.principalUnitSuccQuot F n)`.
-/
instance principalUnitSuccQuotCommGroup (n : ℕ) :
    CommGroup (higherPrincipalUnitGroup.principalUnitSuccQuot F n) := by
  change CommGroup
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  infer_instance
/-- Explicit access to the concrete quotient used to implement
`principalUnitSuccQuot`. -/
def principalUnitSuccQuotConcreteEquiv (n : ℕ) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n ≃*
      (higherPrincipalUnitGroup F n ⧸
        (higherPrincipalUnitGroup F (n + 1)).subgroupOf
          (higherPrincipalUnitGroup F n)) := by
  change
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) ≃*
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  exact MulEquiv.refl _
noncomputable instance principalUnitSuccQuotFinite
    [Finite F.residueField] (n : ℕ) :
    Finite (higherPrincipalUnitGroup.principalUnitSuccQuot F n) :=
  Finite.of_equiv
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
    (higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n).symm.toEquiv
end higherPrincipalUnitGroup
end CompleteDVF
end DiscreteValuationField
end
end LocalFieldTheory
