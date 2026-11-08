module
public import Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.v7541bf954a90.DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleIdealRanges
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.LargeSieve.Sieve
open scoped NumberField Classical
noncomputable def idealDyadicBlock (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) : ℕ → Finset (Ideal (𝓞 F))
  | 0 => {⊤}
  | k + 1 => paperShell F c ((2 : ℝ) ^ k)
def dyadicScale : ℕ → ℝ
  | 0 => 1
  | k + 1 => (2 : ℝ) ^ k
end DedekindZetaZeroFree.LargeSieve.Sieve
