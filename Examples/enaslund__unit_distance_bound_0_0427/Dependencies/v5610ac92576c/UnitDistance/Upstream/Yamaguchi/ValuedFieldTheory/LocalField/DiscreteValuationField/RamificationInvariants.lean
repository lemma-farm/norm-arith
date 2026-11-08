/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
# Canonical ramification invariants

The ramification index and residue degree are the ideal-theoretic invariants of
the chosen valuation rings.  Every theorem below is stated directly in the
ambient valued-extension context; there are no compatibility aliases or
extension-marker arguments.
-/
noncomputable section
universe u v w x
namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace ValuedExtension
variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]
variable [FiniteDimensional K L]
end ValuedExtension
end LocalFieldTheory.DiscreteValuationField
end
