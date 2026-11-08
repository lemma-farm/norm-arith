module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/
public import Mathlib
set_option Elab.async false
/- CONDITIONAL, UNCOMPILED structural experiment. See README.md. -/
/- BEGIN SOURCE 000: RequestProject/Audit/OldResidueFalse.lean -/
section ChunkedSource000
/-!
# Audit: the earlier hypothesis form of E6 was false

An earlier version of this development assumed the residue theorem in the form `OldResidue`
below, without the condition `N ≥ 1` on the number of principal-part terms. With `N = 0` the
principal parts vanish, so the statement asserts `∮ h = 2πi ∑_{a ∈ S} P(a,0)` for every
holomorphic `h` and every choice of `P`. That is false. Hence the earlier bundle of external
hypotheses could not be satisfied, and results proved from it held vacuously.

The current development does not assume any form of E6. It proves the correct statement
(`Buckling.circleIntegral_eq_explicit_residues`, with `0 < N`).
-/
@[expose] public section
namespace Buckling.Audit
end Buckling.Audit
end
end ChunkedSource000
/- END SOURCE 000 -/
/- BEGIN SOURCE 001: RequestProject/Bessel/Asymptotic/Fresnel.lean -/
section ChunkedSource001
/-!
# Finite Fresnel-type integrals

For `Re b ≥ 0`, `b ≠ 0`:
`∫₀¹ e^{-b s²} ds = (π/b)^{1/2}/2 - e^{-b}/(2b) + O(|b|^{-2})`.
The case `Re b > 0` follows from the Gaussian integral and two integrations by parts on
`(1, ∞)`; the case `Re b = 0` (Fresnel integrals) follows by continuity.
-/
@[expose] public section
open Complex Real MeasureTheory Filter Topology Set
namespace Buckling
end Buckling
end
end ChunkedSource001
/- END SOURCE 001 -/
/- BEGIN SOURCE 002: RequestProject/Bessel/Asymptotic/Oscillatory.lean -/
section ChunkedSource002
/-!
# Oscillatory integrals `∫₀¹ g(s) e^{-ixs²} ds` for large real `x`

* `norm_osc_le`: `|∫₀¹ h(s) e^{-ixs²} ds| ≤ 3 x^{-1/2} (|h(1)| + ∫₀¹ |h'|)`;
* `osc_asymp`: if `g(s) = g(0) + s k(s)` with `k(0) = 0` and `k` of class `C²` near `[0,1]`,
  then `∫₀¹ g(s) e^{-ixs²} ds = g(0)(π/(ix))^{1/2}/2 - g(1) e^{-ix}/(2ix) + O(x^{-3/2})`.
-/
@[expose] public section
open Complex Real MeasureTheory Filter Topology Set
namespace Buckling
end Buckling
end
end ChunkedSource002
/- END SOURCE 002 -/
/- BEGIN SOURCE 003: RequestProject/Bessel/Defs.lean -/
section ChunkedSource003
/-!
# Bessel functions of integer order (Definition 1.1 of the paper)

We define the Bessel function `J_n` of the first kind of integer order `n ≥ 0`
by its power series, both for a real and for a complex argument, the
enumeration `j_{n,1} < j_{n,2} < ⋯` of its positive zeros, the two distinguished
zeros `q = j_{0,1}` and `k = j_{1,1}`, and the finite partial sums `S_{ν,N}`
(Definition 3.4 of the paper).
-/
@[expose] public section
open scoped Nat
namespace Buckling
/-- The Bessel function `J_n(x) = ∑_{m ≥ 0} (-1)^m (x/2)^{2m+n} / (m! (m+n)!)`
of integer order `n ≥ 0`, for a real argument. -/
noncomputable def besselJ (n : ℕ) (x : ℝ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ) ^ m * (x / 2) ^ (2 * m + n) / ((m ! : ℝ) * ((m + n) ! : ℝ))
/-- The Bessel function `J_n(ζ)` of integer order `n ≥ 0`, for a complex argument. -/
noncomputable def besselJC (n : ℕ) (ζ : ℂ) : ℂ :=
  ∑' m : ℕ, (-1 : ℂ) ^ m * (ζ / 2) ^ (2 * m + n) / ((m ! : ℂ) * ((m + n) ! : ℂ))
/-- Enumeration of the positive zeros of `J_n`: `besselZero n 0 = 0` is a placeholder,
and `besselZero n (k+1)` is the infimum of the zeros of `J_n` exceeding
`besselZero n k`.  Under External Theorem E1 (`ExtZeros`), `besselZero n k` is the
`k`-th positive zero `j_{n,k}` for every `k ≥ 1`. -/
noncomputable def besselZero (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => sInf {x : ℝ | besselZero n k < x ∧ besselJ n x = 0}
/-- `q = j_{0,1}`, the first positive zero of `J_0`. -/
noncomputable def jq : ℝ := besselZero 0 1
/-- `k = j_{1,1}`, the first positive zero of `J_1`. -/
noncomputable def jk : ℝ := besselZero 1 1
end Buckling
end
end ChunkedSource003
/- END SOURCE 003 -/
/- BEGIN SOURCE 004: RequestProject/Bessel/Basic.lean -/
section ChunkedSource004
/-!
# Basic properties of the Bessel series (part of Lemma 2.5)

Summability, term-by-term differentiation, and the recurrences
`J₀' = -J₁`, `J_{n+1}' = (J_n - J_{n+2})/2`, `x (J_n + J_{n+2}) = 2(n+1) J_{n+1}`.
-/
@[expose] public section
open scoped Nat
open Filter Topology
namespace Buckling
end Buckling
end
end ChunkedSource004
/- END SOURCE 004 -/
/- BEGIN SOURCE 005: RequestProject/Bessel/Alternating.lean -/
section ChunkedSource005
/-!
# Alternating tail bounds (Lemma 3.5) and the finite rational certificate (Lemma 3.6)
-/
@[expose] public section
open scoped Nat
open Filter Topology
namespace Buckling
end Buckling
end
end ChunkedSource005
/- END SOURCE 005 -/
/- BEGIN SOURCE 006: RequestProject/Bessel/Certificate.lean -/
section ChunkedSource006
/-!
# The finite rational certificate (Lemma 3.6)

Each row `(ν, x, A, B)` of the table in the paper gives
`A/10⁸ < S_{ν,31}(x) < S_{ν,30}(x) < B/10⁸`, checked by exact rational arithmetic,
and hence `A/10⁸ < J_ν(x) < B/10⁸`.
-/
@[expose] public section
namespace Buckling
end Buckling
end
end ChunkedSource006
/- END SOURCE 006 -/
/- BEGIN SOURCE 007: RequestProject/Bessel/Radial.lean -/
section ChunkedSource007
/-!
# The Bessel series as a function of `s²`

`J_n(s) = (s/2)^n G_n(s²)` where `G_n(y) = ∑ (-1)^m (y/4)^m / (m! (m+n)!)` is an entire
function of `y`.  This gives the smoothness of the radial functions `x ↦ J₀(c|x - a|)` on the
plane (used in Section 11 of the paper), together with the identities
`G_n' = -G_{n+1}/4` and `G₀ - G₁ + (y/4) G₂ = 0` (the Bessel equation in the variable `y`).
-/
@[expose] public section
open scoped Nat
open Filter Topology
namespace Buckling
/-- The `m`-th term of `G_n(y)`. -/
noncomputable def gterm (n m : ℕ) (y : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * (y / 4) ^ m / ((m ! : ℝ) * ((m + n) ! : ℝ))
/-- `G_n(y) = ∑_{m ≥ 0} (-1)^m (y/4)^m / (m! (m+n)!)`, so that `J_n(s) = (s/2)^n G_n(s²)`. -/
noncomputable def besselG (n : ℕ) (y : ℝ) : ℝ := ∑' m, gterm n m y
lemma abs_gterm (n m : ℕ) (y : ℝ) :
    |gterm n m y| = (|y| / 4) ^ m / ((m ! : ℝ) * ((m + n) ! : ℝ)) := by
  unfold gterm
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (by positivity : (0 : ℝ) < (m ! : ℝ) * ((m + n) ! : ℝ))]
lemma abs_gterm_le (n m : ℕ) (y : ℝ) : |gterm n m y| ≤ (|y| / 4) ^ m / (m ! : ℝ) := by
  rw [abs_gterm]
  have h1 : (1 : ℝ) ≤ ((m + n) ! : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos _)
  rw [mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right (div_le_self (by positivity) h1) (by positivity)
lemma summable_abs_gterm (n : ℕ) (y : ℝ) : Summable fun m => |gterm n m y| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => abs_gterm_le n m y)
    (Real.summable_pow_div_factorial _)
lemma summable_gterm (n : ℕ) (y : ℝ) : Summable fun m => gterm n m y :=
  (summable_abs_gterm n y).of_abs
/-- The derivative of the `m`-th term. -/
noncomputable def dgterm (n m : ℕ) (y : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * ((m : ℝ) * (y / 4) ^ (m - 1) * (1 / 4)) / ((m ! : ℝ) * ((m + n) ! : ℝ))
lemma hasDerivAt_gterm (n m : ℕ) (y : ℝ) : HasDerivAt (gterm n m) (dgterm n m y) y := by
  unfold gterm dgterm
  have h := ((hasDerivAt_id y).div_const 4).fun_pow m
  have h2 := (h.const_mul ((-1 : ℝ) ^ m)).div_const ((m ! : ℝ) * ((m + n) ! : ℝ))
  simpa only [id_eq, Pi.pow_apply] using! h2
lemma dgterm_zero (n : ℕ) (y : ℝ) : dgterm n 0 y = 0 := by simp [dgterm]
lemma dgterm_succ (n m : ℕ) (y : ℝ) : dgterm n (m + 1) y = -(1 / 4) * gterm (n + 1) m y := by
  unfold dgterm gterm
  rw [Nat.add_sub_cancel, show m + 1 + n = m + (n + 1) by omega, Nat.factorial_succ]
  push_cast
  field_simp
  ring
lemma abs_dgterm_le (n m : ℕ) (y R : ℝ) (hy : |y| ≤ R) :
    |dgterm n m y| ≤ (if m = 0 then 0 else (1 / 4) * |gterm (n + 1) (m - 1) R|) := by
  rcases m with _ | m
  · simp [dgterm_zero]
  · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [dgterm_succ, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [abs_gterm, abs_gterm]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    linarith [le_abs_self R]
lemma summable_dgbound (n : ℕ) (R : ℝ) :
    Summable fun m : ℕ => (if m = 0 then 0 else (1 / 4) * |gterm (n + 1) (m - 1) R|) := by
  rw [← summable_nat_add_iff 1]
  simpa using (summable_abs_gterm (n + 1) R).mul_left (4⁻¹)
/-- `G_n' = -G_{n+1}/4`. -/
theorem hasDerivAt_besselG (n : ℕ) (y : ℝ) :
    HasDerivAt (besselG n) (-(1 / 4) * besselG (n + 1) y) y := by
  have hR : |y| < |y| + 1 := by linarith
  have key : HasDerivAt (besselG n) (∑' m, dgterm n m y) y := by
    refine hasDerivAt_tsum_of_isPreconnected (summable_dgbound n (|y| + 1))
      (isOpen_Ioo (a := -(|y| + 1)) (b := |y| + 1)) isPreconnected_Ioo
      (fun m z _ => hasDerivAt_gterm n m z) (fun m z hz => ?_) (y₀ := 0) ?_
      (summable_gterm n 0) ?_
    · rw [Real.norm_eq_abs]
      apply abs_dgterm_le
      rw [Set.mem_Ioo] at hz
      exact abs_le.mpr ⟨hz.1.le, hz.2.le⟩
    · constructor <;> linarith [abs_nonneg y]
    · constructor <;> linarith [neg_abs_le y, le_abs_self y]
  convert key using 1
  have hs : Summable fun m => dgterm n m y := by
    refine (summable_nat_add_iff 1).mp ?_
    simp only [dgterm_succ]
    exact (summable_gterm (n + 1) y).mul_left _
  rw [hs.tsum_eq_zero_add, dgterm_zero, zero_add]
  simp only [dgterm_succ]
  rw [tsum_mul_left]; rfl
lemma differentiable_besselG (n : ℕ) : Differentiable ℝ (besselG n) :=
  fun y => (hasDerivAt_besselG n y).differentiableAt
lemma deriv_besselG (n : ℕ) : deriv (besselG n) = fun y => -(1 / 4) * besselG (n + 1) y :=
  funext fun y => (hasDerivAt_besselG n y).deriv
/-- Each `G_n` is smooth. -/
theorem contDiff_besselG (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (besselG n) := by
  have : ∀ k : ℕ, ∀ n, ContDiff ℝ k (besselG n) := by
    intro k
    induction k with
    | zero => intro n; exact contDiff_zero.mpr (differentiable_besselG n).continuous
    | succ k ih =>
      intro n
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨differentiable_besselG n, by simp, ?_⟩
      rw [deriv_besselG]
      exact contDiff_const.mul (ih (n + 1))
  exact contDiff_infty.mpr fun k => this k n
end Buckling
end
end ChunkedSource007
/- END SOURCE 007 -/
/- BEGIN SOURCE 008: RequestProject/Bessel/Small.lean -/
section ChunkedSource008
/-!
# Small-argument bounds (Lemma 3.9 of the paper)
-/
@[expose] public section
namespace Buckling
end Buckling
end
end ChunkedSource008
/- END SOURCE 008 -/
/- BEGIN SOURCE 009: RequestProject/Calibration/Algebra.lean -/
section ChunkedSource009
/-!
# A two-dimensional positivity criterion (Proposition 4.12)

The calibration matrix
`M = [[a, d/2, L_A/2], [d/2, K, L_C/2], [L_A/2, L_C/2, H]]` with `a = K - g²`
satisfies the kernel identities (Proposition 4.11)
`L_C = -dA - 2KC`, `L_A = -2aA - dC`, `H = aA² + dAC + KC²`.
Under `d² + 4Kg² ≤ 4K²` it is positive semidefinite and `2K - g² - d ≥ 0`.
-/
@[expose] public section
namespace Buckling
end Buckling
end
end ChunkedSource009
/- END SOURCE 009 -/
/- BEGIN SOURCE 010: RequestProject/Concavity/ComplexBessel.lean -/
section ChunkedSource010
/-!
# Bessel functions of a complex argument

Term-by-term differentiation of the complex Bessel series: `J_n` is entire, `J₀' = -J₁`,
`J_{n+1}' = (J_n - J_{n+2})/2`, the three-term recurrence, parity, and agreement with the
real Bessel functions on the real axis.
-/
@[expose] public section
open scoped Nat
open Filter Topology
namespace Buckling
end Buckling
end
end ChunkedSource010
/- END SOURCE 010 -/
/- BEGIN SOURCE 011: RequestProject/Disk/Fourier1D.lean -/
section ChunkedSource011
/-!
# Real Fourier coefficients on `[0, 2π]`

For a continuous function `g` on `ℝ` we use the real coefficients
`cosC n g = (1/2π) ∫₀^{2π} g(θ) cos(nθ) dθ` and `sinC n g = (1/2π) ∫₀^{2π} g(θ) sin(nθ) dθ`,
`n ∈ ℤ`.  We record Parseval's identity (from Mathlib's complex version) and the rule
for derivatives of `2π`-periodic functions.
-/
@[expose] public section
open MeasureTheory Real Set Filter Topology intervalIntegral
namespace Buckling
namespace Fourier1D
end Fourier1D
end Buckling
end
end ChunkedSource011
/- END SOURCE 011 -/
/- BEGIN SOURCE 012: RequestProject/Disk/Ground1D.lean -/
section ChunkedSource012
/-!
# A one-dimensional weighted ground-state inequality with a spectral gap

Let `χ > 0` on `(0, R)` solve `(r χ')' = χ / r - μ r χ`, with `χ(0) = χ(R) = 0`,
`χ'(0) > 0 > χ'(R)`.  For admissible `w` (vanishing to first order at `0` and near `R`)
the ground-state substitution `ψ = w / χ` gives
`∫ (r w'² + w²/r) - μ ∫ r w² = ∫ r χ² ψ'²`,
and a weighted Hardy (Cheeger) argument with the weight `p = r χ²` yields a gap
`∫ r χ² ψ'² ≥ δ · (∫ r w² - (∫ r χ w)² / ∫ r χ²)`.
-/
@[expose] public section
open MeasureTheory Real Set Filter Topology intervalIntegral
namespace Buckling
namespace Ground1D
structure GroundState (R μ : ℝ) (χ dχ : ℝ → ℝ) : Prop where
  R_pos : 0 < R
  cont : Continuous χ
  dcont : Continuous dχ
  deriv : ∀ r, HasDerivAt χ (dχ r) r
  zero0 : χ 0 = 0
  zeroR : χ R = 0
  pos : ∀ r ∈ Ioo 0 R, 0 < χ r
  d0 : 0 < dχ 0
  dR : dχ R < 0
  flux : ∀ r ∈ Ioo 0 R, HasDerivAt (fun s => s * dχ s) (χ r / r - μ * r * χ r) r
/-- Admissible functions: differentiable on `(0, R)`, `O(r)` at `0`, vanishing near `R`. -/
structure Admissible (R : ℝ) (w dw : ℝ → ℝ) : Prop where
  deriv : ∀ r ∈ Ioo 0 R, HasDerivAt w (dw r) r
  dcont : ContinuousOn dw (Ioo 0 R)
  bound : ∃ C, ∀ r ∈ Ioo 0 R, |w r| ≤ C * r ∧ |dw r| ≤ C
  supp : ∃ R' ∈ Ioo 0 R, ∀ r ∈ Icc R' R, w r = 0 ∧ dw r = 0
variable {R μ : ℝ} {χ dχ : ℝ → ℝ}
namespace GroundState
variable (gs : GroundState R μ χ dχ)
include gs
end GroundState
section Admissible
variable (gs : GroundState R μ χ dχ) {w dw : ℝ → ℝ} (hw : Admissible R w dw)
include gs hw
end Admissible
end Ground1D
end Buckling
end
end ChunkedSource012
/- END SOURCE 012 -/
/- BEGIN SOURCE 013: RequestProject/Disk/Mode1D.lean -/
section ChunkedSource013
/-!
# Identities and inequalities for a single angular mode

For a radial coefficient `v` of angular frequency `n` (smooth, `v(0) = 0` if `n ≠ 0`,
`v'(0) = 0` if `n ≠ 1`, vanishing near `R`) put `w = v' - n v / r`.  Then
`∫ (r v'² + n² v²/r) = ∫ r w²` and
`∫ r (v'' + v'/r - n² v/r²)² = ∫ (r w'² + w²/r) + ((n+1)² - 1) ∫ w²/r`.
Combined with the one-dimensional ground-state inequality this gives the mode
inequalities used for the disk spectral gap.
-/
@[expose] public section
open MeasureTheory Real Set Filter Topology intervalIntegral
namespace Buckling
namespace Mode1D
open Ground1D
/-- Hypotheses on a radial coefficient of angular frequency `n`. -/
structure ModeFn (R : ℝ) (n : ℕ) (v : ℝ → ℝ) : Prop where
  R_pos : 0 < R
  smooth : ContDiff ℝ 2 v
  zero : n ≠ 0 → v 0 = 0
  dzero : n ≠ 1 → deriv v 0 = 0
  supp : ∃ R' ∈ Ioo 0 R, ∀ r, R' ≤ r → v r = 0
variable {R : ℝ} {n : ℕ} {v : ℝ → ℝ}
namespace ModeFn
variable (hv : ModeFn R n v)
include hv
end ModeFn
end Mode1D
end Buckling
end
end ChunkedSource013
/- END SOURCE 013 -/
/- BEGIN SOURCE 014: RequestProject/Disk/ModeInt.lean -/
section ChunkedSource014
/-!
# Integrability and positivity facts for radial modes
-/
@[expose] public section
open MeasureTheory Real Set Filter Topology
namespace Buckling
namespace Mode1D
open Ground1D
variable {R : ℝ} {n : ℕ} {v : ℝ → ℝ}
namespace ModeFn
variable (hv : ModeFn R n v)
include hv
end ModeFn
end Mode1D
end Buckling
end
end ChunkedSource014
/- END SOURCE 014 -/
/- BEGIN SOURCE 015: RequestProject/Elementary.lean -/
section ChunkedSource015
/-!
# Elementary analytic lemmas (Section 2 of the paper)

* Lemma 2.1 (a derivative with one change of sign),
* Lemma 2.2 (oriented zeros),
* Lemma 2.3 (a cubic interpolation inequality).
-/
@[expose] public section
open Set Filter Topology
namespace Buckling
end Buckling
end
end ChunkedSource015
/- END SOURCE 015 -/
/- BEGIN SOURCE 016: RequestProject/Functional/Perspective.lean -/
section ChunkedSource016
/-!
# Perspective extensions (Lemma 9.4 of the paper)

If `h ∈ C¹(ℝ)` with `h'` and `h - s h'` bounded, then `(A, P) ↦ P h(A/P)` is Lipschitz on
`ℝ × (0, ∞)` and extends Lipschitz-continuously to `P = 0` by its boundary limit.
-/
@[expose] public section
open Real Set Filter Topology
namespace Buckling
end Buckling
end
end ChunkedSource016
/- END SOURCE 016 -/
/- BEGIN SOURCE 017: RequestProject/Main.lean -/
section ChunkedSource017
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true
set_option grind.warning false
end ChunkedSource017
/- END SOURCE 017 -/
/- BEGIN SOURCE 018: RequestProject/Positivity/CubicParam.lean -/
section ChunkedSource018
/-!
# A parametric form of the cubic interpolation inequality (Lemma 2.3)

Lemma 2.3 of the paper is applied to a function `E` of a variable `X` which is itself a
strictly decreasing function of `r`.  We state it directly in the parameter `r`: the
`X`-derivatives of `E` are given by functions `E₁, E₂, E₃` with `dE/dr = X' E₁` etc.
-/
@[expose] public section
open Set
namespace Buckling
end Buckling
end
end ChunkedSource018
/- END SOURCE 018 -/
/- BEGIN SOURCE 019: RequestProject/Profiles/Taylor.lean -/
section ChunkedSource019
/-!
# One-sided Taylor bounds from derivative bounds

If `F(k) = 0` and `F' = O((k - s)^m)` as `s → k⁻`, then `F = O((k - s)^(m+1))`.
-/
@[expose] public section
open Real Set Filter Topology Asymptotics
namespace Buckling
end Buckling
end
end ChunkedSource019
/- END SOURCE 019 -/
/- BEGIN SOURCE 020: RequestProject/Sobolev/Defs.lean -/
section ChunkedSource020
/-!
# Sobolev form domains and variational eigenvalues (Definition 1.2 of the paper)

For an open set `Ω ⊆ ℝ²` we realise `H₀¹(Ω)` and `H₀²(Ω)` as the closures of
`C_c^∞(Ω)` in the respective Sobolev norms.  Concretely, a test function `φ` is
identified with the tuple of its derivatives up to order `m`, viewed as an element of
a finite product of copies of `L²(Ω)`; `H₀^m(Ω)` is the closure of the set of these
tuples.  This is the completion of `C_c^∞(Ω)` in the `H^m(Ω)` norm, and the
components of a limit tuple are the function and its weak derivatives.

The energies are
* `E₀(v) = ∫_Ω v²`,
* `E₁(v) = ∫_Ω |∇v|²`,
* `E₂(v) = ∫_Ω |Δv|²`,

and the variational eigenvalues are the infima of the Rayleigh quotients
`λ₁ᴰ(Ω) = inf E₁/E₀` over `H₀¹(Ω)` and `Λ₁(Ω) = inf E₂/E₁` over `H₀²(Ω)`.
The infima are taken over the elements with nonzero denominator; by Lemma 7.3 of
the paper (nonzero denominators) these are exactly the nonzero elements.
-/
@[expose] public section
open MeasureTheory
namespace Buckling
/-- The Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
/-- The partial derivative `∂ᵢ φ` of a function on the plane. -/
noncomputable def pderiv (i : Fin 2) (φ : Plane → ℝ) : Plane → ℝ :=
  fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
def IsTestFn (Ω : Set Plane) (φ : Plane → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω
/-- The real Hilbert space `L²(Ω)`. -/
noncomputable abbrev L2 (Ω : Set Plane) := Lp ℝ 2 (volume.restrict Ω)
lemma IsTestFn.pderiv {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) (i : Fin 2) :
    IsTestFn Ω (pderiv i φ) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) :=
      h.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact h1.clm_apply contDiff_const
  · exact (h.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun L => L (EuclideanSpace.single i 1))
      (by simp)
  · refine subset_trans ?_ h.2.2
    exact (tsupport_fderiv_subset ℝ).trans' (by
      apply closure_mono
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by simp [Buckling.pderiv, h0]))
lemma IsTestFn.memLp {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) :
    MemLp φ 2 (volume.restrict Ω) :=
  (h.1.continuous.memLp_of_hasCompactSupport h.2.1).restrict Ω
/-- A test function as an element of `L²(Ω)`. -/
noncomputable def IsTestFn.toL2 {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) : L2 Ω :=
  h.memLp.toLp φ
noncomputable def graphH2 {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω) :=
  (φ.2.toL2, fun i => (φ.2.pderiv i).toL2, fun i j => ((φ.2.pderiv j).pderiv i).toL2)
end Buckling
end
end ChunkedSource020
/- END SOURCE 020 -/
/- BEGIN SOURCE 021: RequestProject/Disk/Polar.lean -/
section ChunkedSource021
/-!
# Polar coordinates in the plane

`∫ F = ∫₀ᴿ r ∫₀^{2π} F(a + r e(θ)) dθ dr` for continuous `F` vanishing outside `B_R(a)`,
where `e(θ) = (cos θ, sin θ)`.
-/
@[expose] public section
open MeasureTheory Real Set Filter Topology intervalIntegral
namespace Buckling
end Buckling
end
end ChunkedSource021
/- END SOURCE 021 -/
/- BEGIN SOURCE 022: RequestProject/Disk/Coeff.lean -/
section ChunkedSource022
/-!
# Angular Fourier coefficients of a test function on a disk

For a smooth compactly supported `φ` and a centre `a`, put `u(r, θ) = φ(a + r e(θ))` and
let `aC n r`, `bC n r` be the cosine and sine coefficients of `u(r, ·)`.  We compute their
`r`-derivatives, express the angular derivatives through the coefficient rule, and show
that each coefficient is an admissible radial mode.
-/
@[expose] public section
open MeasureTheory Real Set Filter Topology intervalIntegral Metric
namespace Buckling
namespace DiskCoeff
open Fourier1D
variable (φ : Plane → ℝ) (a : Plane)
variable {φ}
section Smooth
variable (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
include hφ
variable (hc : HasCompactSupport φ)
include hc
end Smooth
end DiskCoeff
end Buckling
end
end ChunkedSource022
/- END SOURCE 022 -/
/- BEGIN SOURCE 023: RequestProject/External.lean -/
section ChunkedSource023
/-!
# External theorems (Section 1 of the paper) — explicit, auditable hypotheses

The paper declares a fixed list of external results, labelled `E1`–`E12`, which it
quotes from the literature and does not prove.  The formalization is **conditional**:
those external results that are actually used and are neither in Mathlib nor proved in
this project are recorded below as Lean propositions and bundled in the structure
`PaperExternals`, which the main theorems take as an explicit hypothesis.  No axioms are
introduced.

Status of the twelve external results:

* `E1` zeros/interlacing (DLMF §10.21(i), Eq. 10.21.2), in the form used (orders `0` and
  `1`): **proved** in `RequestProject/Bessel/ZerosE1.lean` (`extZeros_holds`); the
  proposition `ExtZeros` is kept only as the statement being proved.
* `E2` canonical product for `J₁` (DLMF Eq. 10.21.15): **proved** in
  `RequestProject/Bessel/Product/Main.lean` (`extProduct_holds`); the proposition
  `ExtProduct` is kept only as the statement being proved.
* `E3` integral representation (DLMF Eq. 10.9.2): **proved** in
  `RequestProject/Bessel/IntegralRep.lean` (`besselJ_integral_rep`, `extIntegral_holds`);
  the proposition `ExtIntegral` is kept only as the statement being proved.
* `E4` uniform large-argument estimate (DLMF Eq. 10.17.3, §10.17(iv)): **proved** in
  `RequestProject/Bessel/Asymptotic/Main.lean` (`extAsymptotic_holds`); the proposition
  `ExtAsymptotic` is kept only as the statement being proved.
* `E5` large zeros of `J₁` (DLMF Eq. 10.21.19): **not used** by the formal proof; removed.
* `E6` Taylor series and residues (Rudin RCA Thms 10.6, 10.16, 10.42): **proved** in
  `RequestProject/Concavity/Removable.lean` (`circleIntegral_eq_explicit_residues`) from
  Mathlib's Cauchy integral theorem; only the residue part was used.  (An earlier
  hypothesis-form of E6 omitted the necessary condition `N ≥ 1` and was therefore false;
  it has been removed.)
* `E7` Rademacher / Lipschitz weak derivatives (Evans–Gariepy §3.1.2 Thm 3.2, §4.2.3):
  in Mathlib (`LipschitzWith.ae_differentiableAt`, `LipschitzWith.integral_lineDeriv_mul_eq`).
* `E8` mollification in `H¹(ℝ²)` and `H²(ℝ²)` (Evans–Gariepy §4.2.1), in the forms used:
  **proved** in `RequestProject/Sobolev/Mollification.lean` (`extMollification_holds`,
  `extMollification2_holds`); the propositions `ExtMollification`, `ExtMollification2` are
  kept only as the statements being proved.
* `E9` planar Sobolev embedding `H²(ℝ²) ⊆ L^∞` (Adams–Fournier Thm 4.12), in the form
  used (on `C_c^∞(ℝ²)`): **proved** in `RequestProject/Sobolev/Embedding.lean`
  (`extEmbedding_holds`, with constant `1`).
* `E10` Rellich compactness (Evans PDE §5.7 Thm 1): **not used**; removed.
* `E11` Fourier completeness and Parseval (Rudin RCA §4.26, Thm 4.18): in Mathlib
  (`tsum_sq_fourierCoeff`).
* `E12` Faber–Krahn inequality with equality case (Brasco–De Philippis–Velichkov, Duke
  Math. J. 164 (2015), §1.1, Eq. (1.1)): hypothesis `ExtFaberKrahn`.

-/
@[expose] public section
open MeasureTheory Real Filter Topology
namespace Buckling
/-- **E1** (positive zeros and interlacing, DLMF §10.21(i)), in the form used: for
`n ∈ {0, 1}` the positive zeros of `J_n` form an unbounded strictly increasing sequence
`j_{n,1} < j_{n,2} < ⋯` of simple zeros, enumerated by `besselZero n`, and
`j_{0,k} < j_{1,k} < j_{0,k+1}`.  (The paper states E1 for every order `n`; only the orders
`0` and `1` are used.) -/
def ExtZeros : Prop :=
  ∀ n : ℕ, n ≤ 1 →
    StrictMono (besselZero n) ∧
    Tendsto (besselZero n) atTop atTop ∧
    (∀ k, 1 ≤ k → besselJ n (besselZero n k) = 0 ∧ deriv (besselJ n) (besselZero n k) ≠ 0) ∧
    (∀ x, 0 < x → besselJ n x = 0 → ∃ k, 1 ≤ k ∧ besselZero n k = x) ∧
    (∀ k, 1 ≤ k → besselZero 0 k < besselZero 1 k ∧ besselZero 1 k < besselZero 0 (k + 1))
/-- **E2** (canonical product for `J₁`, DLMF 10.21.15):
`J₁(ζ) = (ζ/2) ∏_{n ≥ 1} (1 - ζ²/κ_n²)`, locally uniformly on `ℂ`. -/
def ExtProduct : Prop :=
  TendstoLocallyUniformly
    (fun (N : ℕ) (ζ : ℂ) =>
      ζ / 2 * ∏ n ∈ Finset.range N, (1 - ζ ^ 2 / ((besselZero 1 (n + 1) : ℝ) : ℂ) ^ 2))
    (besselJC 1) atTop
end Buckling
end
end ChunkedSource023
/- END SOURCE 023 -/
/- BEGIN SOURCE 024: RequestProject/Bessel/IntegralRep.lean -/
section ChunkedSource024
/-!
# Bessel's integral representation (External theorem E3, proved)

We prove DLMF Eq. 10.9.2,
`J_n(x) = π⁻¹ ∫₀^π cos(x sin θ - n θ) dθ`, for every integer `n ≥ 0` and real `x`,
directly from the power-series definition of `J_n`.  Hence the hypothesis `ExtIntegral`
of the earlier formalization is a theorem (`extIntegral_holds`) and is no longer assumed.

Proof: expand `exp(i x sin θ) = ∑_k (i x sin θ)^k / k!`, integrate term by term against
`e^{-i n θ}` over `[0, 2π]` (dominated convergence), evaluate
`∫₀^{2π} sin^k θ e^{-inθ} dθ` with the binomial theorem and the orthogonality of the
exponentials, identify the resulting series with the Bessel series, take real parts, and
fold `[0, 2π]` onto `[0, π]` using `θ ↦ 2π - θ`.
-/
@[expose] public section
open Complex Real
open scoped Nat
namespace Buckling
end Buckling
end
end ChunkedSource024
/- END SOURCE 024 -/
/- BEGIN SOURCE 025: RequestProject/Bessel/IntegralRepC.lean -/
section ChunkedSource025
/-!
# Bessel's integral representation for a complex argument

`2π J_n(z) = ∫₀^{2π} e^{i z sin θ} e^{-inθ} dθ` for every complex `z`, and the consequences
`J₀(z) = (2/π) ∫₀^{π/2} cos(z cos t) dt`, `J₁(z) = (2/π) ∫₀^{π/2} sin(z cos t) cos t dt`.
-/
@[expose] public section
open Complex Real
open scoped Nat
namespace Buckling
end Buckling
namespace Buckling
end Buckling
end
end ChunkedSource025
/- END SOURCE 025 -/
/- BEGIN SOURCE 026: RequestProject/Bessel/Asymptotic/Subst.lean -/
section ChunkedSource026
/-!
# The substitution `cos t = 1 - s²`

`∫₀^{π/2} f(cos t) dt = ∫₀¹ f(1 - s²) · 2/√(2 - s²) ds`, and the resulting representations
`J₀(z) = (2/π) ∫₀¹ w(s) cos(z(1-s²)) ds`, `J₁(z) = (2/π) ∫₀¹ w(s)(1-s²) sin(z(1-s²)) ds`
with `w(s) = 2/√(2 - s²)`.
-/
@[expose] public section
open Complex Real
namespace Buckling
end Buckling
end
end ChunkedSource026
/- END SOURCE 026 -/
/- BEGIN SOURCE 027: RequestProject/Bessel/Asymptotic/RealAxis.lean -/
section ChunkedSource027
/-!
# Large-argument asymptotics of `J₀`, `J₁` on the positive real axis

`|√(πx/2) J₀(x) - cos(x - π/4)| ≤ C/x` and `|√(πx/2) J₁(x) - cos(x - 3π/4)| ≤ C/x`
for `x ≥ 1`.
-/
@[expose] public section
open Complex Real MeasureTheory Filter Topology Set
namespace Buckling
end Buckling
end
end ChunkedSource027
/- END SOURCE 027 -/
/- BEGIN SOURCE 028: RequestProject/Bessel/Asymptotic/ImagAxis.lean -/
section ChunkedSource028
/-!
# Large-argument asymptotics of `J₀`, `J₁` on the positive imaginary axis

Laplace's method: for `y ≥ 1`,
`|(π i y/2)^{1/2} J_ν(iy) - cos(iy - νπ/2 - π/4)| ≤ C e^y / y` (`ν = 0, 1`).
-/
@[expose] public section
open Complex Real MeasureTheory Filter Topology Set
namespace Buckling
end Buckling
end
end ChunkedSource028
/- END SOURCE 028 -/
/- BEGIN SOURCE 029: RequestProject/Bessel/Asymptotic/Main.lean -/
section ChunkedSource029
/-!
# External theorem E4 (large-argument asymptotics of `J₀`, `J₁`), proved

For `ν ∈ {0, 1}` put `E_ν(z) = (πz/2)^{1/2} J_ν(z) - cos(z - νπ/2 - π/4)`.  On the positive
real axis `|E_ν(x)| ≤ C/x` (stationary phase, `RealAxis.lean`) and on the positive imaginary
axis `|E_ν(iy)| ≤ C e^y/y` (Laplace's method, `ImagAxis.lean`).  The function
`z E_ν(z) e^{iz}` is holomorphic in the open first quadrant, continuous up to the boundary and of
exponential type, and it is bounded on both boundary rays; by the Phragmén–Lindelöf principle
it is bounded in the closed quadrant, i.e. `|E_ν(z)| ≤ C e^{Im z}/|z|` there.  The fourth
quadrant follows by complex conjugation.  This is `ExtAsymptotic` (`extAsymptotic_holds`).
-/
@[expose] public section
open Complex Real MeasureTheory Filter Topology Set
namespace Buckling
end Buckling
end
end ChunkedSource029
/- END SOURCE 029 -/
/- BEGIN SOURCE 030: RequestProject/Bessel/Zeros.lean -/
section ChunkedSource030
/-!
# Bessel equations, separation of zeros, and certified root intervals

* Bessel equations for `J₀` and `J₁` (part of Lemma 2.5),
* positivity of `J₁` near the origin,
* a Sturm comparison lemma and Lemma 3.3 (separation of consecutive positive zeros of
  `J₁` by more than `π`),
* Lemma 3.7 (certified root intervals).
-/
@[expose] public section
open Real Set Filter Topology
namespace Buckling
/-! ### Derivative identities -/
end Buckling
end
end ChunkedSource030
/- END SOURCE 030 -/
