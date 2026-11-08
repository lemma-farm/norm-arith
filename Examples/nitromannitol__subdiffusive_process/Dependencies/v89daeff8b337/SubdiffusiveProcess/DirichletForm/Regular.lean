/-
# Cores, regularity and strong locality
-/
module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v89daeff8b337.SubdiffusiveProcess.DirichletForm.Energy
public import Mathlib.Topology.Algebra.Support
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
theorem HasCoreRep.add {U : Set X} {u v : Lp ℝ 2 m} (hu : HasCoreRep m U u)
    (hv : HasCoreRep m U v) : HasCoreRep m U (u + v) := by
  obtain ⟨f, hf, hcf, hsf, haf⟩ := hu
  obtain ⟨g, hg, hcg, hsg, hag⟩ := hv
  refine ⟨f + g, hf.add hg, hcf.add hcg, ?_, ?_⟩
  · have h1 : tsupport (f + g) ⊆ tsupport f ∪ tsupport g := by
      refine (closure_mono (Function.support_add f g)).trans ?_
      exact closure_union.le
    exact h1.trans (Set.union_subset hsf hsg)
  · exact (Lp.coeFn_add u v).trans (haf.add hag)
namespace ClosedForm
/-- The core `D(E) ∩ C_c(U)`: elements of the domain with a continuous
representative compactly supported inside `U`. -/
def MemCoreOn (E : ClosedForm m) (U : Set X) (u : Lp ℝ 2 m) : Prop :=
  u ∈ E.domain ∧ HasCoreRep m U u
/-- The core `D(E) ∩ C_c(X)`. -/
def MemCore (E : ClosedForm m) (u : Lp ℝ 2 m) : Prop := E.MemCoreOn Set.univ u
variable {E : ClosedForm m}
theorem MemCoreOn.mem_domain {U : Set X} {u : Lp ℝ 2 m} (hu : E.MemCoreOn U u) :
    u ∈ E.domain := hu.1
theorem MemCore.mem_domain {u : Lp ℝ 2 m} (hu : E.MemCore u) : u ∈ E.domain := hu.1
theorem MemCoreOn.add {U : Set X} {u v : Lp ℝ 2 m} (hu : E.MemCoreOn U u)
    (hv : E.MemCoreOn U v) : E.MemCoreOn U (u + v) :=
  ⟨E.domain.add_mem hu.1 hv.1, hu.2.add hv.2⟩
end ClosedForm
end SubdiffusiveProcess.DirichletForm
