module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sym
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Data.Int.Interval
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Fourier.FourierTransform

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.StudentComplexBernstein ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-!
# Exact complex perturbation of a bicubic Bernstein polynomial

Finite mixed differences of the original coefficient table give the exact
Taylor expansion. The Bernstein partition of unity is reused from Mathlib.
This supplies the algebraic and norm-control foundation for the published
polynomial Student profile's zero-free complex tube.
-/
open scoped BigOperators
namespace UnitDistance.BernsteinTube
variable {R : Type*} [CommRing R]
/-- Evaluation of the ordinary Bernstein basis polynomial. -/
noncomputable def basis (n i : ℕ) (t : R) : R :=
  (n.choose i : R)*t^i*(1-t)^(n-i)

/-- The actual bicubic polynomial represented by a coefficient array.
Only indices from zero through three occur. -/
noncomputable def patch (B : ℕ → ℕ → R) (t u : R) : R :=
  ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4, B i j*basis 3 i t*basis 3 j u
/-- Ordinary forward mixed differences; these are independently defined
from the coefficient table, not from the desired perturbation bound. -/
noncomputable def difference (B : ℕ → ℕ → R) (r s i j : ℕ) : R :=
  ∑ k ∈ Finset.range (r+1), ∑ l ∈ Finset.range (s+1),
    (-1:R)^(r-k+s-l)*(r.choose k : R)*(s.choose l : R)*B (i+k) (j+l)

end UnitDistance.BernsteinTube

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.StudentComplexTubeCertificate ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-!
# The exact Bernstein tube certificate of the published witness

The finite mixed differences, their maxima and the tube loss are defined
directly from the original rational coefficient array. The strict bound is
verified by kernel rational arithmetic, not by floating-point computation.
-/
open scoped BigOperators
namespace UnitDistance.Witness

def fourierTubeWidth : ℚ := 1/1000
def fourierTubeOmega : ℚ :=
  (fourierTubeWidth+fourierTubeWidth^2)/(1-fourierTubeWidth^2)

end UnitDistance.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.StudentComplexDenominator ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-!
# Complex Student denominators in the Euclidean tube

The denominator is the actual holomorphic quadratic `1+sum(z_i^2)`.
Its real part and norm are controlled after an imaginary Euclidean shift,
with the exact scale factor used by the manuscript.
-/
open scoped BigOperators RealInnerProductSpace
namespace UnitDistance.BernsteinTube
variable {ι : Type*} [Fintype ι]
noncomputable def studentDenominator (z : ι → ℂ) : ℂ := 1+∑ i, z i^2
noncomputable def complexShift (x y : EuclideanSpace ℝ ι) (i : ι) : ℂ :=
  (x i : ℂ)+Complex.I*(y i : ℂ)

end UnitDistance.BernsteinTube

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.StudentComplexExtension ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-!
# A genuine holomorphic extension of the polynomial Student weight

The extension uses the principal complex powers of independently defined
quadratic denominators and the actual Bernstein polynomial. Its branch
conditions are proved on the prescribed geometric tube.
-/
open scoped BigOperators
namespace UnitDistance.Witness
abbrev StudentRealPlane := EuclideanSpace ℝ (Fin 2)
abbrev StudentComplexPlane := Fin 2 → ℂ

noncomputable def pairComplexShift (x y : StudentRealPlane × StudentRealPlane) :
    StudentComplexPlane × StudentComplexPlane :=
  (BernsteinTube.complexShift x.1 y.1, BernsteinTube.complexShift x.2 y.2)

end UnitDistance.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.StudentComplexRealRestriction ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-! The complex extension restricts to the exact published real p-th power. -/
open scoped BigOperators
namespace UnitDistance.Witness
noncomputable def complexToStudentRealPlane (z : ℂ) : StudentRealPlane :=
  WithLp.toLp 2 ![z.re, z.im]

end UnitDistance.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.StudentFourierPhase ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-! Exact Fourier phase factors for justified horizontal contour shifts. -/
open MeasureTheory Filter Set
open scoped Topology
namespace UnitDistance.FourierContour
/-- The Fourier kernel with the exact `exp(-2*pi*i*xi*z)` convention. -/
noncomputable def fourierKernel (ξ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-((2*Real.pi*ξ:ℝ):ℂ)*Complex.I*z)

end UnitDistance.FourierContour

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.StudentFourierCoordinates ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-! Ordinary four real coordinates for the actual Student Fourier integral. -/
open MeasureTheory
namespace UnitDistance.Witness
/-- Real coordinates in the order `Re z₁, Im z₁, Re z₂, Im z₂`. -/
noncomputable def studentFourCoordinates : (Fin 4 → ℝ) ≃ᵐ (ℂ × ℂ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ))).trans
      (Complex.measurableEquivPi.symm.prodCongr Complex.measurableEquivPi.symm)

end UnitDistance.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.StudentFourierIntegrand ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-! Integrable four-coordinate Fourier integrands on the actual complex tube. -/
open MeasureTheory
namespace UnitDistance.Witness
noncomputable def studentFourPlanes (x : Fin 4 → ℝ) : StudentRealPlane × StudentRealPlane :=
  (WithLp.toLp 2 ![x 0, x 1], WithLp.toLp 2 ![x 2, x 3])

def studentFourTube (y : Fin 4 → ℝ) : Prop :=
  ‖(studentFourPlanes y).1‖ ≤ 1/1000 ∧ ‖(studentFourPlanes y).2‖ ≤ 1/1000

noncomputable def studentFourKernel (ξ x : Fin 4 → ℝ) : ℂ :=
  ∏ i, FourierContour.fourierKernel (ξ i) (x i:ℂ)

end UnitDistance.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.StudentFourierDirection ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-! The extremal direction in the product of the two actual Euclidean tube balls. -/
namespace UnitDistance.Witness
noncomputable def studentFourFrequency (ξ : ℂ × ℂ) : Fin 4 → ℝ :=
  ![ξ.1.re, ξ.1.im, ξ.2.re, ξ.2.im]
noncomputable def studentTubeDirectionScale (z : ℂ) : ℝ := -(1/1000)/‖z‖
noncomputable def studentFourDirection (ξ : ℂ × ℂ) : Fin 4 → ℝ :=
  ![studentTubeDirectionScale ξ.1*ξ.1.re, studentTubeDirectionScale ξ.1*ξ.1.im,
    studentTubeDirectionScale ξ.2*ξ.2.re, studentTubeDirectionScale ξ.2*ξ.2.im]

end UnitDistance.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.Sqrt241.Target ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-!
# The planar target at exponent `1.04315`

Same counting as `UnitDistance.Target` (`unitPairs` divides the ordered
unit-distance pairs by two); only the exponent changes. `increment` is the
exponent gain δ = 0.04315 of the 41-cap tower over `ℚ(√241)`.
-/
open Filter
namespace UnitDistance.Sqrt241
noncomputable def increment : ℝ := 863 / 20000

end UnitDistance.Sqrt241

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.Sqrt241.Witness ====
public section
@[expose] public section
set_option backward.privateInPublic true
/-!
# The witness for the tower over `ℚ(√241)` at δ = 0.04315

Port of `UnitDistance.Witness` with the five local types of
`certificates/finite-witness-241.json`: rational primes 2, 3, 5, 29 and 41 with
absolute (e, f) = (8,4), (2,2), (2,2), (1,4), (2,4). At 41 only the primes of the
tower above the capped prime of `ℚ(√241)` carry windows; they have true type (1,4) and
are half of the primes above 41, which the effective type (2,4) records. The pair
profile is the 1.0418235 manuscript's unchanged (`s`, `a` and the Bernstein matrix of
`UnitDistance.Witness`), so `pairProfile` and `pairOverlap` coincide with those of
the ℚ development and only the mass exponent changes: `q = s·p − 1`
(`pair_exponent_gap`). `ceiling` is the threshold for the fixed-base residue ceiling
of the tower fields; `thetaMin = 65535/131072` corresponds to a conjugacy class of
complex conjugation of size at least `2^15` in `Gal(K/B)`. These are definitions only;
their numerical bounds are proved separately (`Numerics/`, `FiniteCertificates/`).
-/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace UnitDistance.Sqrt241.Witness
/-- The radial exponent `s` of the pair profile (the manuscript's value). -/
def s : ℝ := (22920117 : ℝ) / 20000000
/-- The radial scale `a` of the pair profile (the manuscript's value). -/
def a : ℝ := (64316620879 : ℝ) / 5000000000000000
/-- The mass exponent `p = 2/(1+δ)`, `δ = increment`. -/
def p : ℝ := 2 / (1 + increment)

/-- The manuscript's Bernstein matrix, unchanged. -/
def bernsteinCoefficients : Fin 4 → Fin 4 → ℚ :=
  ![![(1 / 1 : ℚ), (24129438977 / 10000000000 : ℚ), (2772179921 / 1000000000 : ℚ), (66857798061 / 10000000000 : ℚ)], ![(24129438977 / 10000000000 : ℚ), (2408311493 / 625000000 : ℚ), (46371750119 / 10000000000 : ℚ), (81307168183 / 10000000000 : ℚ)], ![(2772179921 / 1000000000 : ℚ), (46371750119 / 10000000000 : ℚ), (13657239771 / 2500000000 : ℚ), (23878161897 / 2500000000 : ℚ)], ![(66857798061 / 10000000000 : ℚ), (81307168183 / 10000000000 : ℚ), (23878161897 / 2500000000 : ℚ), (13865943061 / 1000000000 : ℚ)]]
/-- The cubic Bernstein basis polynomial `C(3,i) tⁱ (1-t)^(3-i)`. -/
def bernstein3 (i : Fin 4) (t : ℝ) : ℝ :=
  (Nat.choose 3 i : ℝ) * t ^ (i : ℕ) * (1-t) ^ (3 - (i : ℕ))
/-- The Bernstein polynomial `P(t,u) = Σ c_ij B_i(t) B_j(u)` of the pair profile. -/
def polynomial (t u : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (bernsteinCoefficients i j : ℝ) *
    bernstein3 i t * bernstein3 j u

/-- The pair profile `t^s u^s P(t,u)` with `t = (1 + a‖z₁‖²)⁻¹`, `u = (1 + a‖z₂‖²)⁻¹`. -/
def pairProfile (z : ℂ × ℂ) : ℝ :=
  let t := (1 + a * ‖z.1‖^2)⁻¹
  let u := (1 + a * ‖z.2‖^2)⁻¹
  t ^ s * u ^ s * polynomial t u

/-- The `L^p` mass `∫ pairProfile^p` of the pair profile over `ℂ × ℂ`. -/
def pairMass : ℝ := ∫ z : ℂ × ℂ, pairProfile z ^ p

end UnitDistance.Sqrt241.Witness

end
end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.Sqrt241.Geometry.StudentComplexTubeCertificate ====
public section
-- Generated by scripts/sqrt241/regenerate_geometry.sh — do not edit by hand.
@[expose] public section
set_option backward.privateInPublic true
/-! Copy of `UnitDistance.StudentComplexTubeCertificate` for the witness `UnitDistance.Sqrt241.Witness`:
only its witness-dependent declarations, moved to `UnitDistance.Sqrt241`;
generic declarations are used from the original. -/
set_option autoImplicit false
/-!
# The exact Bernstein tube certificate of the published witness

The finite mixed differences, their maxima and the tube loss are defined
directly from the original rational coefficient array. The strict bound is
verified by kernel rational arithmetic, not by floating-point computation.
-/
open scoped BigOperators
namespace UnitDistance.Sqrt241.Witness
/-- Zero extension of the actual finite coefficient array. In all differences
used below, the indexing ranges keep the arguments within the original array. -/
def bernsteinCoefficientNat (i j : ℕ) : ℚ :=
  if hi : i < 4 then if hj : j < 4 then bernsteinCoefficients ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0
noncomputable def bernsteinDifferenceAbs (r s i j : ℕ) : ℚ≥0 :=
  ⟨|BernsteinTube.difference bernsteinCoefficientNat r s i j|, abs_nonneg _⟩
noncomputable def bernsteinDifferenceBound (r s : ℕ) : ℚ≥0 :=
  ((Finset.range (4-r)) ×ˢ (Finset.range (4-s))).sup
    (fun ij => bernsteinDifferenceAbs r s ij.1 ij.2)
noncomputable def bernsteinTaylorBound (r s : ℕ) : ℚ≥0 :=
  (Nat.choose 3 r : ℚ≥0)*(Nat.choose 3 s : ℚ≥0)*bernsteinDifferenceBound r s
/-- The manuscript's `q0`; the exact minimum coefficient is one. -/
noncomputable def fourierTubeLoss : ℚ :=
  ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4,
    if r+s=0 then 0 else (bernsteinTaylorBound r s : ℚ)*Witness.fourierTubeOmega^(r+s)

end UnitDistance.Sqrt241.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.Sqrt241.Geometry.StudentComplexPolynomial ====
public section
-- Generated by scripts/sqrt241/regenerate_geometry.sh — do not edit by hand.
@[expose] public section
set_option backward.privateInPublic true
/-! Copy of `UnitDistance.StudentComplexPolynomial` for the witness `UnitDistance.Sqrt241.Witness`:
only its witness-dependent declarations, moved to `UnitDistance.Sqrt241`;
generic declarations are used from the original. -/
set_option autoImplicit false
/-!
# The actual Bernstein polynomial is nonvanishing in its certified complex tube

The complex polynomial is independently defined from the published rational
coefficient array. Its real restriction is the original polynomial. Exact
mixed-difference maxima control its perturbation, and the checked tube loss
places its values strictly in the right half-plane.
-/
open scoped BigOperators
namespace UnitDistance.Sqrt241.Witness
noncomputable def complexBernsteinCoefficients (i j : ℕ) : ℂ := bernsteinCoefficientNat i j
noncomputable def complexPolynomial (t u : ℂ) : ℂ :=
  BernsteinTube.patch complexBernsteinCoefficients t u

end UnitDistance.Sqrt241.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.Sqrt241.Geometry.StudentComplexExtension ====
public section
-- Generated by scripts/sqrt241/regenerate_geometry.sh — do not edit by hand.
@[expose] public section
set_option backward.privateInPublic true
/-! Copy of `UnitDistance.StudentComplexExtension` for the witness `UnitDistance.Sqrt241.Witness`:
only its witness-dependent declarations, moved to `UnitDistance.Sqrt241`;
generic declarations are used from the original. -/
set_option autoImplicit false
/-!
# A genuine holomorphic extension of the polynomial Student weight

The extension uses the principal complex powers of independently defined
quadratic denominators and the actual Bernstein polynomial. Its branch
conditions are proved on the prescribed geometric tube.
-/
open scoped BigOperators
namespace UnitDistance.Sqrt241.Witness
/-- Complexification in normalized coordinates `x = sqrt(a) z`. The exact
published real exponent `p` is retained, including in the polynomial factor. -/
noncomputable def complexPairWeight (z : Witness.StudentComplexPlane × Witness.StudentComplexPlane) : ℂ :=
  (BernsteinTube.studentDenominator z.1)^((-s*p:ℝ):ℂ) *
  (BernsteinTube.studentDenominator z.2)^((-s*p:ℝ):ℂ) *
  (complexPolynomial (BernsteinTube.studentDenominator z.1)⁻¹
    (BernsteinTube.studentDenominator z.2)⁻¹)^(p:ℂ)

end UnitDistance.Sqrt241.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.Sqrt241.Geometry.StudentComplexRealRestriction ====
public section
-- Generated by scripts/sqrt241/regenerate_geometry.sh — do not edit by hand.
@[expose] public section
set_option backward.privateInPublic true
/-! Copy of `UnitDistance.StudentComplexRealRestriction` for the witness `UnitDistance.Sqrt241.Witness`:
only its witness-dependent declarations, moved to `UnitDistance.Sqrt241`;
generic declarations are used from the original. -/
set_option autoImplicit false
/-! The complex extension restricts to the exact published real p-th power. -/
open scoped BigOperators
namespace UnitDistance.Sqrt241.Witness
/-- Exactly the manuscript's normalization in each of the two complex
coordinates, retaining the ordinary complex Euclidean norm. -/
noncomputable def normalizedStudentPair (z : ℂ × ℂ) : Witness.StudentRealPlane × Witness.StudentRealPlane :=
  (Real.sqrt a • Witness.complexToStudentRealPlane z.1,
   Real.sqrt a • Witness.complexToStudentRealPlane z.2)

end UnitDistance.Sqrt241.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.Sqrt241.Geometry.StudentComplexMajorant ====
public section
-- Generated by scripts/sqrt241/regenerate_geometry.sh — do not edit by hand.
@[expose] public section
set_option backward.privateInPublic true
/-! Copy of `UnitDistance.StudentComplexMajorant` for the witness `UnitDistance.Sqrt241.Witness`:
only its witness-dependent declarations, moved to `UnitDistance.Sqrt241`;
generic declarations are used from the original. -/
set_option autoImplicit false
/-! The explicit pointwise contour majorant for the actual p-th power. -/
namespace UnitDistance.Sqrt241.Witness
/-- The explicit factor in the published two-coordinate Fourier envelope. -/
noncomputable def fourierTubeConstant : ℝ :=
  (1-(1/1000:ℝ)^2)^(-2*s*p) * (1+(fourierTubeLoss:ℝ))^p

end UnitDistance.Sqrt241.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.Sqrt241.Geometry.StudentFourierIntegrand ====
public section
-- Generated by scripts/sqrt241/regenerate_geometry.sh — do not edit by hand.
@[expose] public section
set_option backward.privateInPublic true
/-! Copy of `UnitDistance.StudentFourierIntegrand` for the witness `UnitDistance.Sqrt241.Witness`:
only its witness-dependent declarations, moved to `UnitDistance.Sqrt241`;
generic declarations are used from the original. -/
set_option autoImplicit false
/-! Integrable four-coordinate Fourier integrands on the actual complex tube. -/
open MeasureTheory
namespace UnitDistance.Sqrt241.Witness
noncomputable def studentFourWeight (y x : Fin 4 → ℝ) : ℂ :=
  complexPairWeight (Witness.pairComplexShift (normalizedStudentPair (Witness.studentFourCoordinates x))
    (Witness.studentFourPlanes y))

noncomputable def studentFourIntegrand (y ξ x : Fin 4 → ℝ) : ℂ :=
  studentFourWeight y x * Witness.studentFourKernel ξ x

end UnitDistance.Sqrt241.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Dependencies.v6f905a7529d0.UnitDistance.Sqrt241.Geometry.StudentFourierDirection ====
public section
-- Generated by scripts/sqrt241/regenerate_geometry.sh — do not edit by hand.
@[expose] public section
set_option backward.privateInPublic true
/-! Copy of `UnitDistance.StudentFourierDirection` for the witness `UnitDistance.Sqrt241.Witness`:
only its witness-dependent declarations, moved to `UnitDistance.Sqrt241`;
generic declarations are used from the original. -/
set_option autoImplicit false
/-! The extremal direction in the product of the two actual Euclidean tube balls. -/
namespace UnitDistance.Sqrt241.Witness
/-- The exact positive Fourier exponent supplied by the certified radius and
the original normalization `sqrt(a)`. -/
noncomputable def studentFourierSigma : ℝ := 2*Real.pi*(1/1000)/Real.sqrt a

end UnitDistance.Sqrt241.Witness

end
end

-- ==== Examples.enaslund__unit_distance_bound_0_0427.Examples.Example_5381afd026030c42a102_StudentFourierEnvelope ====
-- Generated by scripts/sqrt241/regenerate_geometry.sh — do not edit by hand.
@[expose] public section
set_option backward.privateInPublic true
/-! Copy of `UnitDistance.StudentFourierEnvelope` for the witness `UnitDistance.Sqrt241.Witness`:
only its witness-dependent declarations, moved to `UnitDistance.Sqrt241`;
generic declarations are used from the original. -/
set_option autoImplicit false
/-!
# The actual original Student Fourier envelope

The original noninteger `pairProfile^p` has the exact sum-of-coordinate-norms
Fourier decay, with its own independently defined mass and certified tube
constant. All contour and tube inputs are discharged in this theorem.
-/
open MeasureTheory FourierTransform
namespace UnitDistance.Sqrt241.Witness

set_option linter.unusedVariables false in
/-- The original profile has the exact product-tube Fourier envelope, with
the published noninteger power, original mass, and certified tube constant. -/
theorem pairProfile_fourier_envelope (ξ : WithLp 2 (ℂ × ℂ)) 
    (h_UnitDistance_Sqrt241_Witness_studentFourDirection_phase : ∀ (ξ : ℂ × ℂ),
      2 * Real.pi / √UnitDistance.Sqrt241.Witness.a *
          ∑ i : Fin 4,
            UnitDistance.Witness.studentFourFrequency ξ i *
              UnitDistance.Witness.studentFourDirection ξ i =
        -UnitDistance.Sqrt241.Witness.studentFourierSigma * (‖ξ.1‖ + ‖ξ.2‖))
    (h_UnitDistance_Sqrt241_Witness_integral_norm_studentFourWeight_le : ∀ (y : Fin 4 → ℝ),
      UnitDistance.Witness.studentFourTube y →
        ∫ (x : Fin 4 → ℝ), ‖UnitDistance.Sqrt241.Witness.studentFourWeight y x‖ ≤
          UnitDistance.Sqrt241.Witness.fourierTubeConstant * UnitDistance.Sqrt241.Witness.pairMass)
    (h_UnitDistance_Sqrt241_Witness_pairProfile_fourier_eq_studentFourIntegral : ∀ (ξ : WithLp 2 (ℂ × ℂ)),
      FourierTransform.fourier
          (fun (x : WithLp 2 (ℂ × ℂ)) ↦
            (↑(UnitDistance.Sqrt241.Witness.pairProfile x.ofLp ^ UnitDistance.Sqrt241.Witness.p) : ℂ))
          ξ =
        ∫ (x : Fin 4 → ℝ),
          UnitDistance.Sqrt241.Witness.studentFourIntegrand 0
            (UnitDistance.Witness.studentFourFrequency ξ.ofLp) x)
    (h_UnitDistance_Sqrt241_Witness_studentFourIntegral_shift : ∀ (y ξ : Fin 4 → ℝ),
      UnitDistance.Witness.studentFourTube y →
        ∫ (x : Fin 4 → ℝ), UnitDistance.Sqrt241.Witness.studentFourIntegrand 0 ξ x =
          (↑(Real.exp (2 * Real.pi / √UnitDistance.Sqrt241.Witness.a * ∑ i : Fin 4, ξ i * y i)) : ℂ) *
            ∫ (x : Fin 4 → ℝ), UnitDistance.Sqrt241.Witness.studentFourIntegrand y ξ x)
    (h_UnitDistance_Sqrt241_Witness_norm_studentFourIntegrand : ∀ (y ξ x : Fin 4 → ℝ),
      ‖UnitDistance.Sqrt241.Witness.studentFourIntegrand y ξ x‖ =
        ‖UnitDistance.Sqrt241.Witness.studentFourWeight y x‖)
    (h_UnitDistance_Witness_studentFourDirection_mem_tube : ∀ (ξ : ℂ × ℂ), UnitDistance.Witness.studentFourTube (UnitDistance.Witness.studentFourDirection ξ))
    :
    ‖𝓕 (fun x : WithLp 2 (ℂ × ℂ) => ((pairProfile (WithLp.ofLp x)^p:ℝ):ℂ)) ξ‖ ≤
      (fourierTubeConstant*pairMass)*
        Real.exp (-studentFourierSigma*(‖(WithLp.ofLp ξ).1‖+‖(WithLp.ofLp ξ).2‖)) := by
  let ζ := WithLp.ofLp ξ
  have hy := h_UnitDistance_Witness_studentFourDirection_mem_tube ζ
  rw [h_UnitDistance_Sqrt241_Witness_pairProfile_fourier_eq_studentFourIntegral,
    h_UnitDistance_Sqrt241_Witness_studentFourIntegral_shift (Witness.studentFourDirection ζ) _ hy, h_UnitDistance_Sqrt241_Witness_studentFourDirection_phase]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-studentFourierSigma*(‖ζ.1‖+‖ζ.2‖))*
        (∫ x, ‖studentFourIntegrand (Witness.studentFourDirection ζ) (Witness.studentFourFrequency ζ) x‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
        (Real.exp_pos _).le
    _ ≤ Real.exp (-studentFourierSigma*(‖ζ.1‖+‖ζ.2‖))*(fourierTubeConstant*pairMass) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [h_UnitDistance_Sqrt241_Witness_norm_studentFourIntegrand] using h_UnitDistance_Sqrt241_Witness_integral_norm_studentFourWeight_le _ hy
    _ = _ := by ring
end UnitDistance.Sqrt241.Witness
