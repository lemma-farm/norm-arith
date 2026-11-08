module
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.Mellin.ExponentialSmoothing
public import Mathlib
set_option autoImplicit false
@[expose] public section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ShortDraftMellin
end ShortDraftMellin
namespace FiniteRingSieve
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _
end FiniteRingSieve
namespace FiniteFieldSieve
variable {F : Type*} [Field F] [Fintype F]
end FiniteFieldSieve
namespace ProductResidueSieve
variable {R S : Type*} [CommRing R] [CommRing S]
end ProductResidueSieve
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff
namespace FourierBridge
end FourierBridge
end OAI
