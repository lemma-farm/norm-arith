module

public import Mathlib.Probability.Process.Filtration
public import Mathlib.Topology.CompactOpen
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Basic.Denumerable
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Fin.Basic
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Composition.KernelLemmas
public import Mathlib.Data.Finset.Sort
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Data.Finset.Sum
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Tactic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v7648cd52bcfa.SubdiffusiveProcess.DirichletForm.Basic ====
public section
/-
# Closed symmetric forms and Dirichlet forms on `L²`

This file is the base of a self-contained, reusable Dirichlet-form library.  It
imports only Mathlib, uses no carrier of the ambient project, and is written so
that the directory `SubdiffusiveProcess/DirichletForm/` can be lifted into a
standalone Lake package without changes.
-/
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
# Closed symmetric forms and Dirichlet forms

Let `m` be a measure on a measurable space `X`.  A **closed form** on `L²(X, m)`
is a densely defined, symmetric, nonnegative bilinear form `E` whose domain
`D(E)` is a submodule of `L²(X, m)` complete for the energy norm
`E₁(u) = E(u, u) + ‖u‖²`.  A **Dirichlet form** is a closed form on which the
unit contraction `t ↦ (t ⊓ 1) ⊔ 0` operates.

## Main definitions

* `SubdiffusiveProcess.DirichletForm.ClosedForm m`: a densely defined, symmetric, nonnegative,
  closed bilinear form on `L²(X, m)`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.energyInner`, `SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq`:
  the energy inner product `E₁(u, v) = E(u, v) + ⟪u, v⟫` and `E₁(u) = E₁(u, u)`.
* `SubdiffusiveProcess.DirichletForm.IsNormalContraction`: `T : ℝ → ℝ` with `T 0 = 0` and
  `|T s - T t| ≤ |s - t|`.
* `SubdiffusiveProcess.DirichletForm.unitTruncation`: the unit contraction `t ↦ (t ⊓ 1) ⊔ 0`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.OperatesOn`: `T` operates on `E`, i.e. `T ∘ u` stays
  in `D(E)` and does not increase the energy.
* `SubdiffusiveProcess.DirichletForm`: a closed form on which `unitTruncation` operates.
* `SubdiffusiveProcess.DirichletForm.HasNormalContractions`: the Fukushima–Oshima–Takeda statement
  that *every* normal contraction operates on a Dirichlet form.

## Implementation notes

The bilinear form is carried as a total function `Lp ℝ 2 m → Lp ℝ 2 m → ℝ`; every
axiom is restricted to the domain, so the values off the domain carry no
information.  This keeps statements free of subtype coercions and matches the
way a form defined by a dual (resolvent) expression is met in practice.

## References

* M. Fukushima, Y. Oshima, M. Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, 2nd edition, de Gruyter, 2011.
-/
open MeasureTheory Filter Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]
namespace SubdiffusiveProcess.DirichletForm
/-- The unit contraction `t ↦ (t ⊓ 1) ⊔ 0` of the real line. -/
def unitTruncation (t : ℝ) : ℝ := max (min t 1) 0
structure ClosedForm (m : Measure X) where
  /-- The form domain `D(E)`, a linear subspace of `L²(X, m)`. -/
  domain : Submodule ℝ (Lp ℝ 2 m)
  /-- The bilinear form `E(u, v)`.  Values outside `domain` carry no
  information: every axiom below is restricted to `domain`. -/
  form : Lp ℝ 2 m → Lp ℝ 2 m → ℝ
  /-- `D(E)` is dense in `L²(X, m)`. -/
  denseDomain : Dense (domain : Set (Lp ℝ 2 m))
  /-- `E(u, v) = E(v, u)`. -/
  form_symm : ∀ u ∈ domain, ∀ v ∈ domain, form u v = form v u
  /-- `E` is additive in its first argument. -/
  form_add_left : ∀ u ∈ domain, ∀ v ∈ domain, ∀ w ∈ domain,
    form (u + v) w = form u w + form v w
  /-- `E` is homogeneous in its first argument. -/
  form_smul_left : ∀ c : ℝ, ∀ u ∈ domain, ∀ v ∈ domain, form (c • u) v = c * form u v
  /-- `E(u, u) ≥ 0`. -/
  form_nonneg : ∀ u ∈ domain, 0 ≤ form u u
  /-- `E` is closed: `D(E)` is complete for the energy norm
  `E₁(u) = E(u, u) + ‖u‖²`. -/
  complete : ∀ u : ℕ → Lp ℝ 2 m, (∀ n, u n ∈ domain) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      form (u p - u q) (u p - u q) + ‖u p - u q‖ ^ 2 < ε) →
    ∃ w ∈ domain, Tendsto
      (fun n => form (u n - w) (u n - w) + ‖u n - w‖ ^ 2) atTop (𝓝 0)
namespace ClosedForm
variable {m : Measure X} (E : ClosedForm m)

def energyInner (u v : Lp ℝ 2 m) : ℝ := E.form u v + inner ℝ u v
/-- The squared energy norm `E₁(u) = E(u, u) + ‖u‖²`. -/
def energyNormSq (u : Lp ℝ 2 m) : ℝ := E.form u u + ‖u‖ ^ 2

end ClosedForm
end SubdiffusiveProcess.DirichletForm
/-- A **Dirichlet form** on `L²(X, m)`: a closed symmetric nonnegative form on
which the unit contraction `t ↦ (t ⊓ 1) ⊔ 0` operates.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroDirichletForm`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
structure SubdiffusiveProcess.DirichletForm (m : Measure X) extends _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m where
  /-- The Markov property: the unit contraction operates on `E`. -/
  markov : ∀ u ∈ domain, ∀ v : Lp ℝ 2 m,
    (⇑v =ᵐ[m] fun x => _root_.SubdiffusiveProcess.DirichletForm.unitTruncation (u x)) →
    v ∈ domain ∧ form v v ≤ form u u
namespace SubdiffusiveProcess.DirichletForm
variable {m : Measure X}

end SubdiffusiveProcess.DirichletForm

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v7648cd52bcfa.SubdiffusiveProcess.DirichletForm.Regular ====
public section
/-
# Cores, regularity and strong locality
-/
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
# Cores, regularity and strong locality

A **core** of a closed form `E` on `L²(X, m)` is a set of elements of
`D(E) ∩ C_c(X)` which is dense in `D(E)` for the energy norm and dense in
`C_c(X)` for the uniform norm; `E` is **regular** if it has one.  `E` is
**strongly local** if `E(u, v) = 0` whenever `u, v ∈ D(E)` vanish outside
compact sets and `u` is constant on an open set outside which `v` vanishes.

## Main definitions

* `SubdiffusiveProcess.DirichletForm.HasCoreRep m U u`: `u` has a continuous representative whose
  (compact) support lies in `U`.
* `SubdiffusiveProcess.DirichletForm.ClosedForm.MemCoreOn E U`, `SubdiffusiveProcess.DirichletForm.ClosedForm.MemCore E`:
  the cores `D(E) ∩ C_c(U)` and `D(E) ∩ C_c(X)`.
* `SubdiffusiveProcess.DirichletForm.IsCore`, `SubdiffusiveProcess.DirichletForm.IsRegular`.
* `SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore`, `SubdiffusiveProcess.DirichletForm.IsStronglyLocal`.

## References

* Fukushima–Oshima–Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  §1.1 (regularity) and §3.2 (strong locality).
-/
open MeasureTheory Filter Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
namespace SubdiffusiveProcess.DirichletForm
/-- `u ∈ L²(X, m)` has a continuous representative with compact support contained
in `U`. -/
def HasCoreRep (m : Measure X) (U : Set X) (u : Lp ℝ 2 m) : Prop :=
  ∃ f : X → ℝ, Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ U ∧ ⇑u =ᵐ[m] f

namespace ClosedForm
/-- The core `D(E) ∩ C_c(U)`: elements of the domain with a continuous
representative compactly supported inside `U`. -/
def MemCoreOn (E : ClosedForm m) (U : Set X) (u : Lp ℝ 2 m) : Prop :=
  u ∈ E.domain ∧ HasCoreRep m U u

variable {E : ClosedForm m}

end ClosedForm
/-- `C` is a **core** of `E` relative to the open state space `U`: a set of
elements of `D(E) ∩ C_c(U)` which is dense in `D(E)` for the energy norm and
dense in `C_c(U)` for the uniform norm.

The state space `U` is not cosmetic.  Fukushima–Oshima–Takeda's regularity is
density in `C_c(X)` where `X` is the space the form lives on; for a form on
`L²(U, m|_U)` inside a bigger ambient `X` — which is how every concrete instance
arises — core functions vanish outside `U`, so no core function is uniformly
close to an `f ∈ C_c(X)` whose support meets `X \ U`.  Quantifying `denseUniform`
over all of `C_c(X)` therefore makes the structure **unsatisfiable**, and with it
`IsRegular`, and with it the antecedent of `HasEnergyMeasure`.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroIsCoreOn`. The witness establishes NON-VACUITY
only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
structure IsCoreOn (E : ClosedForm m) (U : Set X) (C : Set (Lp ℝ 2 m)) : Prop where
  /-- Every element of `C` lies in `D(E) ∩ C_c(U)`. -/
  memCoreOn : ∀ u ∈ C, E.MemCoreOn U u
  /-- `C` is dense in `D(E)` for the energy norm. -/
  denseEnergy : ∀ u ∈ E.domain, ∀ ε : ℝ, 0 < ε → ∃ w ∈ C, E.energyNormSq (u - w) < ε
  /-- `C` is dense in `C_c(U)` for the uniform norm. -/
  denseUniform : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
    ∀ ε : ℝ, 0 < ε →
    ∃ w ∈ C, ∃ g : X → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ⇑w =ᵐ[m] g ∧ ∀ x : X, |g x - f x| < ε

end SubdiffusiveProcess.DirichletForm

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.v7648cd52bcfa.SubdiffusiveProcess.DirichletForm.FOTProduct ====
public section
/-
# Lipschitz calculus and products on a Dirichlet form (Fukushima–Oshima–Takeda 1.4.1, 1.4.2)
-/
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
# Lipschitz calculus and products on a Dirichlet form

A `SubdiffusiveProcess.DirichletForm` only assumes that the unit contraction `t ↦ (t ∧ 1) ∨ 0` operates.  This file
derives from that single Markov clause and closedness the calculus of Fukushima–Oshima–Takeda
§1.4, with no regularity, locality or resolvent input:

* `SubdiffusiveProcess.DirichletForm.lipschitz_comp_mem`: if `G` is `L`-Lipschitz with `G 0 = 0` and `u ∈ D(E)`,
  then `G ∘ u ∈ D(E)` and `E(G ∘ u) ≤ L² E(u)` (Theorem 1.4.1 for `L = 1`;
  `SubdiffusiveProcess.DirichletForm.hasNormalContractions`).
* `SubdiffusiveProcess.DirichletForm.exists_mul_mem`: products of bounded elements of `D(E)` lie in `D(E)`
  (Theorem 1.4.2(ii)).
* `SubdiffusiveProcess.DirichletForm.exists_memCoreOn_mul_comp`, `SubdiffusiveProcess.DirichletForm.mul_comp_mem`,
  `SubdiffusiveProcess.DirichletForm.mul_mem`, `SubdiffusiveProcess.DirichletForm.comp_mem`, `SubdiffusiveProcess.DirichletForm.mul_mem_of_bounded`: the
  core `D(E) ∩ C_c` is stable under products and `C¹` functions (Theorem 1.4.2), in the exact
  shapes of the four closure clauses of `SubdiffusiveProcess.DirichletForm.IsCoreAlgebra`.

## Method

1. *Cross energies.*  If the ramp at level `h` returns `f` from `f + t g` for all `t > 0`,
   then `E(f, g) ≥ 0` (`form_nonneg_of_ramp_eq`).  Hence the slices of `u` over the cells
   `[i h, (i + 1) h]`, the reflected slices and the tail beyond `N h` have pairwise
   nonnegative cross energies.
2. *Piecewise-linear functions.*  A combination of these slices with coefficients of size at
   most `L` has energy at most `L² E(u)` (`sliceSum_mem_and_form_le`).
3. *Lower semicontinuity.*  A closed form is lower semicontinuous along `L²`-convergent
   sequences of bounded energy (`ClosedForm.mem_domain_of_tendsto_of_form_le`): the
   minimal-energy points of the convex hulls of the tails form an energy-Cauchy sequence by
   the parallelogram identity.
4. *Limit.*  The interpolants of `G` on finer and longer grids converge to `G ∘ u` in `L²` by
   dominated convergence (`tendsto_Lp_of_tendsto_comp`).
5. *Products* follow by polarization with a clamped square; *`C¹` functions* of bounded
   elements by clamping to the range, where they are Lipschitz.

## References

* M. Fukushima, Y. Oshima, M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  2nd edition, de Gruyter, 2011, Theorems 1.4.1 and 1.4.2.
-/
open MeasureTheory Filter Topology Set
open scoped NNReal
noncomputable section
variable {X : Type*} [MeasurableSpace X] {m : Measure X}
namespace SubdiffusiveProcess.DirichletForm
/-! ### Ramps -/

/-! ### Nonnegative cross energies -/

/-! ### Lower semicontinuity of a closed form -/
namespace ClosedForm
variable (E : ClosedForm m)

end ClosedForm
/-! ### Slices of the real line -/

section SliceReal
variable {h : ℝ} {i : ℕ} {s : ℝ}

end SliceReal
/-! ### Slices in `L²` -/

/-! ### Signs of the cross energies of slices -/
section Cross
variable (E : _root_.SubdiffusiveProcess.DirichletForm m) {u : Lp ℝ 2 m} (hu : u ∈ E.domain) {h : ℝ} (hh : 0 ≤ h)
include hu hh

end Cross
/-! ### Finite sums with nonnegative cross energies -/
namespace ClosedForm
variable (E : ClosedForm m)

end ClosedForm
/-! ### Energy of a weighted sum of slices -/

/-! ### Piecewise-linear interpolation -/
section Interp
variable {Γ : ℝ → ℝ} {L : ℝ≥0} {h : ℝ}

end Interp
/-! ### Convergence in `L²` of compositions -/

/-! ### Lipschitz calculus (Fukushima–Oshima–Takeda, Theorem 1.4.1) -/
set_option linter.unusedVariables false in
axiom _root_.SubdiffusiveProcess.DirichletForm.lipschitz_comp_mem.{w_u_1} : ∀ {X : Type w_u_1} [inst : MeasurableSpace X] {m : MeasureTheory.Measure X}
  (E : SubdiffusiveProcess.DirichletForm m) {G : ℝ → ℝ} {L : NNReal},
  LipschitzWith L G →
    G 0 = 0 →
      ∀ {u : ↥(MeasureTheory.Lp ℝ 2 m)},
        u ∈ E.domain →
          ∀ {w : ↥(MeasureTheory.Lp ℝ 2 m)},
            ((↑(↑w : X →ₘ[m] ℝ) : X → ℝ) =ᵐ[m] fun (x : X) ↦ G ((↑(↑u : X →ₘ[m] ℝ) : X → ℝ) x)) →
              w ∈ E.domain ∧ E.form w w ≤ (↑L : ℝ) ^ 2 * E.form u u
section Core
variable [TopologicalSpace X]
end Core
end SubdiffusiveProcess.DirichletForm

end
end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_5a92210bc32b1602b11a_CoreDensity ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
/-- Soft thresholding a uniform core approximation controls its support. -/
theorem exists_localCore_uniform {d : ℕ} {m : Measure (Fin d → ℝ)}
    (E : _root_.SubdiffusiveProcess.DirichletForm m) (V : Set (Fin d → ℝ))
    (C : Set (Lp ℝ 2 m)) (hC : _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm V C)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfV : tsupport f ⊆ V) (U : Set (Fin d → ℝ)) (hfU : tsupport f ⊆ U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : Lp ℝ 2 m, E.toClosedForm.MemCoreOn U u ∧
      ∃ g : (Fin d → ℝ) → ℝ, Continuous g ∧ HasCompactSupport g ∧
        tsupport g ⊆ tsupport f ∧ ⇑u =ᵐ[m] g ∧ ∀ x, |g x - f x| < ε := by
  obtain ⟨w, hwC, g, hg, hgK, _, hwg, herr⟩ :=
    hC.denseUniform f hf hfc hfV (ε / 4) (by positivity)
  let Γ : ℝ → ℝ := fun t => max (t - ε / 2) 0 + min (t + ε / 2) 0
  have hΓ : LipschitzWith 2 Γ := by
    have hp : LipschitzWith 1 (fun t : ℝ => max (t - ε / 2) 0) := by
      simpa using (LipschitzWith.id.sub (LipschitzWith.const (ε / 2))).max
        (LipschitzWith.const 0)
    have hn : LipschitzWith 1 (fun t : ℝ => min (t + ε / 2) 0) := by
      simpa using (LipschitzWith.id.add (LipschitzWith.const (ε / 2))).min
        (LipschitzWith.const 0)
    convert hp.add hn using 1 ; norm_num
  have hΓzero : ∀ t, |t| ≤ ε / 2 → Γ t = 0 := by
    intro t ht
    obtain ⟨hl, hr⟩ := abs_le.1 ht
    dsimp [Γ]
    rw [max_eq_right (by linarith), min_eq_right (by linarith)]
    exact add_zero 0
  have hΓ0 : Γ 0 = 0 := hΓzero 0 (by simp only [abs_zero]; positivity)
  have hΓerr : ∀ t, |Γ t - t| ≤ ε / 2 := by
    intro t
    dsimp [Γ]
    simp only [max_def, min_def]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  let z : Lp ℝ 2 m := hΓ.compLp hΓ0 w
  have hzw : ⇑z =ᵐ[m] fun x => Γ (w x) := LipschitzWith.coeFn_compLp hΓ hΓ0 w
  have hzE : z ∈ E.domain :=
    (_root_.SubdiffusiveProcess.DirichletForm.lipschitz_comp_mem E hΓ hΓ0 (hC.memCoreOn w hwC).1 hzw).1
  have hzg : ⇑z =ᵐ[m] Γ ∘ g := hzw.trans (hwg.fun_comp Γ)
  have hsupport : Function.support (Γ ∘ g) ⊆ tsupport f := by
    intro x hx
    by_contra hnot
    have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hnot
    have hsmall := herr x
    rw [hfx, sub_zero] at hsmall
    have hle : |g x| ≤ ε / 2 := by linarith
    exact hx (hΓzero _ hle)
  have hts : tsupport (Γ ∘ g) ⊆ tsupport f := closure_minimal hsupport isClosed_closure
  have hcompact : HasCompactSupport (Γ ∘ g) :=
    IsCompact.of_isClosed_subset hfc isClosed_closure hts
  have hcont : Continuous (Γ ∘ g) := hΓ.continuous.comp hg
  refine ⟨z, ⟨hzE, Γ ∘ g, hcont, hcompact, hts.trans hfU, hzg⟩,
    Γ ∘ g, hcont, hcompact, hts, hzg, ?_⟩
  intro x
  have hb := abs_add_le (Γ (g x) - g x) (g x - f x)
  have he := hΓerr (g x)
  have ha := herr x
  simp only [Function.comp_apply]
  have hs : Γ (g x) - f x = (Γ (g x) - g x) + (g x - f x) := by ring
  rw [hs]
  linarith
end SubdiffusiveProcess.PartProcess
