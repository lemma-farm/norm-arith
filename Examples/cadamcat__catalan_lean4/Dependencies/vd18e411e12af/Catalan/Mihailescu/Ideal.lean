module
public import Examples.cadamcat__catalan_lean4.Dependencies.vd18e411e12af.Catalan.Cyclotomic.Elements
public import Examples.cadamcat__catalan_lean4.Dependencies.vd18e411e12af.Catalan.Cyclotomic.UnitPowers
/-! The Mihăilescu ideal and its augmentation subgroup, without height assumptions. -/
/-!
# `Catalan.Mihailescu.Ideal`

Part of the Catalan formalization.
-/
@[expose] public section
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan
section BaseElement
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
end BaseElement
section MihIdeal
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime] (x : ℤ)
end MihIdeal
section Embedding
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
local instance mihIdealFintypeG : Fintype (G p K) := Fintype.ofFinite _
end Embedding
end Catalan
