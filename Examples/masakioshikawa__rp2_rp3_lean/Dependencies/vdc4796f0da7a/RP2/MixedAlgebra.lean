module
public import Mathlib
public section
/-!
# Fourth-order polarization and finite-family algebra

Adapted from OpenAI's ClassicalON RotationWork, MixedWard, ComplexWard, and
FamilyAlgebra at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Copyright OpenAI; Apache-2.0. All statements here are generic commutative-ring
identities; no spin-model hypotheses enter them.
-/
namespace RP2.Quadratic
universe uA uE uI uJ uK uL uV
noncomputable section
open scoped BigOperators ComplexConjugate
namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]
end MixedAlgebra
namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]
end MixedAlgebra
namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]
end MixedAlgebra
namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]
end MixedAlgebra
structure ComplexFourForm (A : Type uA) [AddCommMonoid A] [Module ℂ A] where
  toFun : A → A → A → A → ℂ
  add_first : ∀ u u' v w z, toFun (u+u') v w z = toFun u v w z + toFun u' v w z
  add_second : ∀ u v v' w z, toFun u (v+v') w z = toFun u v w z + toFun u v' w z
  add_third : ∀ u v w w' z, toFun u v (w+w') z = toFun u v w z + toFun u v w' z
  add_fourth : ∀ u v w z z', toFun u v w (z+z') = toFun u v w z + toFun u v w z'
  smul_first : ∀ r u v w z, toFun (r • u) v w z = r * toFun u v w z
  smul_second : ∀ r u v w z, toFun u (r • v) w z = r * toFun u v w z
  smul_third : ∀ r u v w z, toFun u v (r • w) z = r * toFun u v w z
  smul_fourth : ∀ r u v w z, toFun u v w (r • z) = r * toFun u v w z
@[expose] instance {A : Type uA} [AddCommMonoid A] [Module ℂ A] :
    CoeFun (ComplexFourForm A) (fun _ => A → A → A → A → ℂ) := ⟨ComplexFourForm.toFun⟩
namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} {L : Type uL} [Fintype E] [CommRing K] [CommRing L]
end MixedAlgebra
namespace MixedAlgebra
variable {I : Type uI} {J : Type uJ} {E : Type uE} {K : Type uK} [Fintype I] [Fintype J] [Fintype E] [CommRing K]
end MixedAlgebra
end
end RP2.Quadratic
