module
public import Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.v7541bf954a90.DedekindZetaZeroFree.Arithmetic.Ideals.BoundedNormFinsets
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.LargeSieve.Sieve
open scoped NumberField Classical
noncomputable def idealAdmissibleFinset (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (X : ℝ) : Finset (Ideal (𝓞 F)) :=
  (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).filter (fun I => Squarefree I ∧ I ⊔ c = ⊤)
noncomputable def paperShell (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (T : ℝ) : Finset (Ideal (𝓞 F)) :=
  (idealAdmissibleFinset F c (2 * T)).filter (fun I => T < (Ideal.absNorm I : ℝ))
end DedekindZetaZeroFree.LargeSieve.Sieve
