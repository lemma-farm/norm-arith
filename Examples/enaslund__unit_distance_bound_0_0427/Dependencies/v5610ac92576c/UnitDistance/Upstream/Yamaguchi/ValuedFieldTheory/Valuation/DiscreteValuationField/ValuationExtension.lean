/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/
module
public import Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v5610ac92576c.UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
public import Mathlib
@[expose] public section
set_option backward.privateInPublic true
set_option autoImplicit false
namespace ValuationTheory
/-!
# Valuation extensions

Mathlib's uniqueness criterion for valuations is expressed through
`Valuation.IsEquiv`: two valuations on the same field are equivalent exactly
when they have the same valuation subring.  The results here use the ambient
valued-extension property directly; no marker object is introduced.
-/
noncomputable section
universe u v w x y
namespace DiscreteValuationField
namespace ValuedExtension
variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
section EquivalentBase
variable {Gamma₁ Gamma₂ GammaL : Type*}
variable [LinearOrderedCommGroupWithZero Gamma₁]
variable [LinearOrderedCommGroupWithZero Gamma₂]
variable [LinearOrderedCommGroupWithZero GammaL]
end EquivalentBase
section ComapAlongCompatibleEmbedding
variable {M : Type y} [Field M] [Algebra K M]
variable {GammaK GammaM : Type*}
variable [LinearOrderedCommGroupWithZero GammaK]
variable [LinearOrderedCommGroupWithZero GammaM]
end ComapAlongCompatibleEmbedding
section LocalValuationSubringMap
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
end LocalValuationSubringMap
section Pullback
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]
end Pullback
section Comparison
variable (target : CompleteDVF.{w, x} L)
end Comparison
end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
