module
public import Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.v33a87da00ae6.DedekindZetaZeroFree.HarmonicAnalysis.Mellin.PositiveLineInversion
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped NumberField Classical ContDiff
namespace DedekindZetaZeroFree.LargeSieve.Vendor
def originMellinH (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  Complex.Gammaℂ s * originMellinQ h s
end DedekindZetaZeroFree.LargeSieve.Vendor
end
