/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
/-!
# Ramification ideals in finite complete-DVF extensions

This file records the ideal-theoretic source behind the local-field structure theory.
The base maximal ideal maps to the `e`-th power of the target maximal ideal, where
`e` is the canonical ramification index.  Every statement is expressed directly
in the ambient valued-extension context; no extension marker is involved.
-/
noncomputable section
universe u v w x
namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace ValuedExtension
open ValuationTheory.DiscreteValuationField.ValuedExtension
variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]
end ValuedExtension
end LocalFieldTheory.DiscreteValuationField
end
