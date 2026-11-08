module
public import Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.v7541bf954a90.DedekindZetaZeroFree.Arithmetic.RayClasses.Character
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.LargeSieve
open scoped NumberField Classical
theorem finite_ideals_absNorm_le (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ X}.Finite := by
  rcases lt_or_ge X 0 with hX | hX
  · refine Set.finite_empty.subset ?_
    rintro I hI
    exact absurd (le_trans (Nat.cast_nonneg (Ideal.absNorm I)) hI) (not_le.mpr hX)
  · refine (Ideal.finite_setOfPred_absNorm_le ⌊X⌋₊).subset ?_
    rintro I hI
    exact (Nat.le_floor_iff hX).mpr hI
noncomputable def boundedNormIdeals (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    Finset (Ideal (𝓞 F)) :=
  (finite_ideals_absNorm_le F X).toFinset
end DedekindZetaZeroFree.LargeSieve
