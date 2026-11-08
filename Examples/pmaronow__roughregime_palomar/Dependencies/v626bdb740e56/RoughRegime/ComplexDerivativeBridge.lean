module
public import Mathlib
public import Examples.pmaronow__roughregime_palomar.Dependencies.v626bdb740e56.RoughRegime.Cauchy
public import Examples.pmaronow__roughregime_palomar.Dependencies.v626bdb740e56.RoughRegime.PolynomialDerivatives
@[expose] public section
/-! Real derivatives of a real polynomial obey the complex Cauchy bound of Lemma 5(c). -/
noncomputable section
namespace RoughRegime.ComplexDerivativeBridge
def complexify {p : ℕ} (F : MvPolynomial (Fin p) ℝ) : MvPolynomial (Fin p) ℂ :=
  MvPolynomial.map Complex.ofRealHom F
end RoughRegime.ComplexDerivativeBridge
