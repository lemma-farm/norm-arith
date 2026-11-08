module

public import SquaresInCircles.Common.Analysis
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Trigonometric estimates

Rational bounds for `π`, `sin` and `cos`: on small angles, on quadrants, and
the Taylor polynomials of degrees four to seven, which bracket `cos` on the
whole line and `sin` for `x ≥ 0`, and on the whole line once chosen by the sign
of `x`. The first harmonic `A cos x + B sin x` is minus its own second
derivative, so it is concave where it is nonnegative, in particular on
`[0, π/2]` when `A, B ≥ 0`. Subtracting `R √(p + q sin x)` keeps it concave
where `q² ≤ p²` and the radical is at most four times the harmonic, since the
radical has the second derivative `-r/4 + (p² - q²)/(4r³)`. The length `L` of a
constant vector of length `a` plus a turning vector of length `b` has
`L² = P + Q cos x + T sin x` with `P = a² + b²` and `Q² + T² = 4a²b²`; the
second derivative of `-R L` is `R (L⁴ - (a² - b²)²)/(4L³)`, at most
`R ab/(a + b)`, because `4abL³ - (a + b)(L⁴ - (a² - b²)²)` is `a + b - L` times
a polynomial with nonnegative terms, and nonpositive when `a ≤ b` and
`L² ≤ b² - a²`. A square root lies below its tangents, the half-angle ratio
`sin t/(1 + cos t) = tan (t/2)` lies between `t/2` and `11t/20` on `[0, 4/5]`,
and the arcsine grows at least as fast as `x`, lies below `x + x³/4` on
`[0, 3/5]` and is concave on `[0, 1]`.
-/

@[expose] public section

noncomputable section
open Set
namespace SquaresInCircles

/-! ### Angles -/

lemma pi_lt_22_over_7 : Real.pi < (22:ℝ)/7 := by
  linarith [Real.pi_lt_d4]

lemma cos_pi_add (x : ℝ) : Real.cos (Real.pi+x) = -Real.cos x := by
  rw [add_comm,Real.cos_add_pi]

lemma sin_pi_add (x : ℝ) : Real.sin (Real.pi+x) = -Real.sin x := by
  rw [add_comm,Real.sin_add_pi]

/-- `cos` and `sin` are nonnegative on `[0, π/2]`. -/
lemma cos_sin_nonneg {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
    0 ≤ Real.cos x ∧ 0 ≤ Real.sin x :=
  ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hx.2⟩,
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_pos])⟩

lemma sin_le_cos_of_small {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/4) : Real.sin x ≤ Real.cos x := by
  rw [← Real.cos_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_pos]) (by linarith)

lemma cos_le_sin_of_quarter {x : ℝ} (hx : Real.pi/4 ≤ x ∧ x ≤ Real.pi/2) :
    Real.cos x ≤ Real.sin x := by
  rw [← Real.cos_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]) (by linarith)

lemma cos_ge_half {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/3) : (1/2 : ℝ) ≤ Real.cos z := by
  simpa only [Real.cos_pi_div_three] using
    Real.cos_le_cos_of_nonneg_of_le_pi hz.1 (by linarith [Real.pi_pos]) hz.2

/-- Rational bounds on `cos t` and `sin t` for `0 ≤ t ≤ π/4`. -/
lemma east_quadrant_trig {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.pi/4) :
    7/10 ≤ Real.cos t ∧ 0 ≤ Real.sin t ∧ Real.sin t ≤ Real.cos t := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ht0
    (show Real.pi/4 ≤ Real.pi by linarith [Real.pi_pos]) ht
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ t by linarith [Real.pi_pos])
    (show Real.pi/4 ≤ Real.pi/2 by linarith [Real.pi_pos]) ht
  rw [Real.cos_pi_div_four] at hc
  rw [Real.sin_pi_div_four] at hs
  have hsqrt : (7:ℝ)/10 ≤ Real.sqrt 2/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  exact ⟨hsqrt.trans hc,
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos]),hs.trans hc⟩

/-- `cos x + sin x` increases on `[0, π/4]`. -/
lemma cos_add_sin_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Real.pi/4) :
    Real.cos x+Real.sin x ≤ Real.cos y+Real.sin y := by
  have h := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ x+Real.pi/4 by linarith [Real.pi_pos])
    (show y+Real.pi/4 ≤ Real.pi/2 by linarith)
    (show x+Real.pi/4 ≤ y+Real.pi/4 by linarith)
  simp only [Real.sin_add,Real.sin_pi_div_four,Real.cos_pi_div_four] at h
  apply (mul_le_mul_iff_right₀ (show 0 < Real.sqrt 2/2 by positivity)).mp
  nlinarith only [h]

lemma one_le_abs_cos_add_abs_sin (t : ℝ) : 1 ≤ |Real.cos t|+|Real.sin t| := by
  have hc := abs_nonneg (Real.cos t)
  have hs := abs_nonneg (Real.sin t)
  have hu := Real.sin_sq_add_cos_sq t
  have hp := mul_nonneg hc hs
  by_contra! h
  have hprod := mul_pos (sub_pos.mpr h)
    (show 0 < 1+(|Real.cos t|+|Real.sin t|) by linarith)
  nlinarith [sq_abs (Real.cos t),sq_abs (Real.sin t)]

/-- A small angle: for `|t| ≤ r`, `1 - r²/2 ≤ cos t` and `|sin t| ≤ r`. -/
lemma small_angle {t r : ℝ} (ht : |t| ≤ r) :
    1-r^2/2 ≤ Real.cos t ∧ |Real.sin t| ≤ r := by
  have ht2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at ht2
  exact ⟨by nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)],
    Real.abs_sin_le_abs.trans ht⟩

/-- A small nonnegative angle: for `0 ≤ x ≤ r ≤ 3`, `1 - r²/2 ≤ cos x` and
`0 ≤ sin x ≤ r`. -/
lemma small_angle_nonneg {x r : ℝ} (hx : 0 ≤ x ∧ x ≤ r) (hr : r ≤ 3) :
    1-r^2/2 ≤ Real.cos x ∧ 0 ≤ Real.sin x ∧ Real.sin x ≤ r := by
  have h := small_angle (show |x| ≤ r by rw [abs_of_nonneg hx.1]; exact hx.2)
  exact ⟨h.1,Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_gt_three]),
    (le_abs_self _).trans h.2⟩

/-- A quadratic upper bound for `cos` on `[-π, π]`. -/
lemma cos_le_one_sub_fifth_sq {t : ℝ} (ht : |t| ≤ Real.pi) :
    Real.cos t ≤ 1-t^2/5 := by
  have hpi : Real.pi < (22:ℝ)/7 := by linarith [Real.pi_lt_d4]
  have hp := mul_pos (sub_pos.mpr hpi)
    (show 0 < (22:ℝ)/7+Real.pi by linarith [Real.pi_pos])
  have hpi2 : Real.pi^2 < 10 := by nlinarith
  have hcoeff : (1:ℝ)/5 ≤ 2/Real.pi^2 := by
    apply (le_div_iff₀ (pow_pos Real.pi_pos 2)).mpr
    linarith
  have hm := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg t)
  have hc := Real.cos_le_one_sub_mul_cos_sq ht
  nlinarith

lemma sin_zero_between {x : ℝ} (hx : -Real.pi<x ∧ x<Real.pi)
    (hs : Real.sin x=0) : x=0 := by
  rcases lt_trichotomy x 0 with h | h | h
  · have hp := Real.sin_pos_of_pos_of_lt_pi (show 0< -x by linarith) (by linarith [hx.1])
    rw [Real.sin_neg,hs] at hp
    linarith
  · exact h
  · have hp := Real.sin_pos_of_pos_of_lt_pi h hx.2
    rw [hs] at hp
    linarith

lemma cos_one_between {x : ℝ} (hx : -2*Real.pi<x ∧ x<2*Real.pi)
    (hc : Real.cos x=1) : x=0 := by
  have hhalf : Real.sin (x/2)=0 := by
    have he := Real.cos_two_mul (x/2)
    rw [show 2*(x/2)=x by ring,hc] at he
    have hu := Real.sin_sq_add_cos_sq (x/2)
    nlinarith
  have hh := sin_zero_between (x := x/2)
    ⟨by linarith [hx.1],by linarith [hx.2]⟩ hhalf
  linarith

lemma cos_zero_between {x : ℝ} (hx : -Real.pi/2<x ∧ x<Real.pi)
    (hc : Real.cos x=0) : x=Real.pi/2 := by
  have hs : Real.sin (x-Real.pi/2)=0 := by
    rw [Real.sin_sub]
    simpa using congrArg Neg.neg hc
  have h := sin_zero_between
    (x := x-Real.pi/2) ⟨by linarith [hx.1],by linarith [hx.2,Real.pi_pos]⟩ hs
  linarith

lemma first_octant_polar {x y : ℝ} (hx : 0<x) (hy : 0<y) (hxy : y≤x) :
    ∃ d b : ℝ, 0<d ∧ 0<b ∧ b≤Real.pi/4 ∧ d^2=x^2+y^2 ∧
      d*Real.cos b=x ∧ d*Real.sin b=y := by
  let d := Real.sqrt (x^2+y^2)
  have hd : 0<d := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg x,sq_nonneg y])
  have hd2 : d^2=x^2+y^2 := Real.sq_sqrt (by positivity)
  have hxd : 0<x/d := div_pos hx hd
  have hxd1 : x/d<1 := (div_lt_one hd).mpr (by nlinarith)
  let b := Real.arccos (x/d)
  have hc : Real.cos b=x/d := Real.cos_arccos (by linarith) hxd1.le
  have hb0 : 0≤b := Real.arccos_nonneg _
  have hbpi : b≤Real.pi := Real.arccos_le_pi _
  have hbhalf : b<Real.pi/2 := by
    have hs := Real.arcsin_pos.mpr hxd
    dsimp [b,Real.arccos]
    linarith
  have hbp : 0<b := by
    by_contra hn
    have he : b=0 := le_antisymm (le_of_not_gt hn) hb0
    rw [he,Real.cos_zero] at hc
    linarith
  have hdc : d*Real.cos b=x := by rw [hc]; field_simp
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hb0 hbpi
  have hds : d*Real.sin b=y := by
    have hu := congrArg (fun z : ℝ => d^2*z) (Real.sin_sq_add_cos_sq b)
    have hc2 := congrArg (fun z : ℝ => z^2) hdc
    have hn := mul_nonneg hd.le hs0
    nlinarith
  have hbq : b≤Real.pi/4 := by
    by_contra hn
    have hsin := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hbhalf.le
      (show Real.pi/2-b<b by linarith)
    rw [Real.sin_pi_div_two_sub] at hsin
    have hm := mul_lt_mul_of_pos_left hsin hd
    rw [hdc,hds] at hm
    linarith
  exact ⟨d,b,hd,hbp,hbq,hd2,hdc,hds⟩

/-! ### Taylor brackets -/

lemma cos_upper_four {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1-x^2/2+x^4/24 := by
  have h := nonneg_of_deriv_nonneg (fun t => 1-t^2/2+t^4/24-Real.cos t) (by fun_prop)
    (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [Real.sin_ge_sub_cube ht]) hx
  linarith

lemma sin_upper_five {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x-x^3/6+x^5/120 := by
  have h := nonneg_of_deriv_nonneg (fun t => t-t^3/6+t^5/120-Real.sin t) (by fun_prop)
    (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [cos_upper_four ht]) hx
  linarith

lemma cos_lower_six {x : ℝ} (hx : 0 ≤ x) : 1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-(1-t^2/2+t^4/24-t^6/720))
    (by fun_prop) (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [sin_upper_five ht]) hx
  linarith

lemma sin_lower_seven {x : ℝ} (hx : 0 ≤ x) : x-x^3/6+x^5/120-x^7/5040 ≤ Real.sin x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.sin t-(t-t^3/6+t^5/120-t^7/5040))
    (by fun_prop) (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [cos_lower_six ht]) hx
  linarith

/-- Polynomial brackets of `sin` and `cos` on an interval `[l, u] ⊆ [0, π/2]`. -/
lemma trig_bracket {l u x : ℝ} (hl : 0 ≤ l) (hu : u ≤ Real.pi/2) (hx : l ≤ x ∧ x ≤ u) :
    l-l^3/6+l^5/120-l^7/5040 ≤ Real.sin x ∧ Real.sin x ≤ u-u^3/6+u^5/120 ∧
    1-u^2/2+u^4/24-u^6/720 ≤ Real.cos x ∧ Real.cos x ≤ 1-l^2/2+l^4/24 := by
  have hx0 : 0 ≤ x := hl.trans hx.1
  have hu0 : 0 ≤ u := hx0.trans hx.2
  have hpi := Real.pi_pos
  exact ⟨(sin_lower_seven hl).trans (Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith) (hx.2.trans hu) hx.1),
    (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hu hx.2).trans (sin_upper_five hu0),
    (cos_lower_six hu0).trans (Real.cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith) hx.2),
    (Real.cos_le_cos_of_nonneg_of_le_pi hl (by linarith) hx.1).trans (cos_upper_four hl)⟩

/-- The Taylor polynomial of degree 6 of `cos`, below it on the whole line. -/
def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720

/-- The Taylor polynomial of degree 4 of `cos`, above it on the whole line. -/
def cosUpper (x : ℝ) : ℝ := 1-x^2/2+x^4/24

/-- The Taylor polynomial of degree 7 of `sin`, below it for `x ≥ 0`. -/
def sinLower (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040

/-- The Taylor polynomial of degree 5 of `sin`, above it for `x ≥ 0`. -/
def sinUpper (x : ℝ) : ℝ := x-x^3/6+x^5/120

/-- A Taylor polynomial below `sin` on the whole line: `sinLower` for `x ≥ 0`,
`sinUpper` for `x < 0`. -/
def sinBelow (x : ℝ) : ℝ := if 0 ≤ x then sinLower x else sinUpper x

/-- A Taylor polynomial above `sin` on the whole line. -/
def sinAbove (x : ℝ) : ℝ := if 0 ≤ x then sinUpper x else sinLower x

lemma cosLower_le (x : ℝ) : cosLower x ≤ Real.cos x := by
  rcases le_total 0 x with hx | hx
  · exact cos_lower_six hx
  · have h := cos_lower_six (x := -x) (by linarith)
    rw [Real.cos_neg] at h
    dsimp [cosLower]
    nlinarith only [h]

lemma le_cosUpper (x : ℝ) : Real.cos x ≤ cosUpper x := by
  rcases le_total 0 x with hx | hx
  · exact cos_upper_four hx
  · have h := cos_upper_four (x := -x) (by linarith)
    rw [Real.cos_neg] at h
    dsimp [cosUpper]
    nlinarith only [h]

lemma sinLower_le {x : ℝ} (hx : 0 ≤ x) : sinLower x ≤ Real.sin x := sin_lower_seven hx

lemma le_sinUpper {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ sinUpper x := sin_upper_five hx

lemma sinBelow_le (x : ℝ) : sinBelow x ≤ Real.sin x := by
  by_cases hx : 0 ≤ x
  · simpa only [sinBelow,ite_eq_left hx] using sinLower_le hx
  · have h := le_sinUpper (x := -x) (by linarith)
    rw [Real.sin_neg] at h
    simp only [sinBelow,ite_eq_right hx,sinUpper] at h ⊢
    nlinarith only [h]

lemma le_sinAbove (x : ℝ) : Real.sin x ≤ sinAbove x := by
  by_cases hx : 0 ≤ x
  · simpa only [sinAbove,ite_eq_left hx] using le_sinUpper hx
  · have h := sinLower_le (x := -x) (by linarith)
    rw [Real.sin_neg] at h
    simp only [sinAbove,ite_eq_right hx,sinLower] at h ⊢
    nlinarith only [h]

/-! ### First harmonics -/

/-- The first harmonic `A cos x + B sin x`. -/
def harmonic (A B x : ℝ) : ℝ := A*Real.cos x+B*Real.sin x

/-- The derivative of `harmonic A B` is `harmonic B (-A)`. -/
lemma harmonic_hasDerivAt (A B x : ℝ) :
    HasDerivAt (harmonic A B) (harmonic B (-A) x) x :=
  (((Real.hasDerivAt_cos x).const_mul A).add ((Real.hasDerivAt_sin x).const_mul B)).congr_deriv
    (by simp only [harmonic]; ring)

/-- A first harmonic with nonnegative coefficients is nonnegative on
`[0, π/2]`. -/
lemma harmonic_nonneg {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
    0 ≤ A*Real.cos x+B*Real.sin x :=
  add_nonneg (mul_nonneg hA (cos_sin_nonneg hx).1) (mul_nonneg hB (cos_sin_nonneg hx).2)

/-- A first harmonic is concave where it is nonnegative: its second derivative
is its negative. -/
lemma harmonic_concave {A B l u : ℝ} (h : ∀ x ∈ Icc l u, 0 ≤ A*Real.cos x+B*Real.sin x) :
    ConcaveOn ℝ (Icc l u) (harmonic A B) :=
  concave_of_deriv2 (fun x _ => harmonic_hasDerivAt A B x)
    (fun x _ => harmonic_hasDerivAt B (-A) x)
    (fun x hx => by have := h x hx; simp only [harmonic]; linarith)

/-- `αx + A sin x + B cos x` with `A, B ≥ 0` is concave on `[0, π/2]`, so on an
interval there it exceeds any bound that it exceeds at both ends. -/
lemma trig_concave_gt {α A B m l u x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hl : 0 ≤ l) (hu : u ≤ Real.pi/2) (hx : l ≤ x ∧ x ≤ u)
    (hml : m < α*l+A*Real.sin l+B*Real.cos l) (hmu : m < α*u+A*Real.sin u+B*Real.cos u) :
    m < α*x+A*Real.sin x+B*Real.cos x := by
  have hs : Icc l u ⊆ Icc 0 Real.pi := Icc_subset_Icc hl (by linarith [Real.pi_pos])
  have hc : Icc l u ⊆ Icc (-(Real.pi/2)) (Real.pi/2) :=
    Icc_subset_Icc (by linarith [Real.pi_pos]) hu
  have hlin : ConcaveOn ℝ (Icc l u) fun x => α*x :=
    ⟨convex_Icc l u,fun x _ y _ a b _ _ _ => by simp only [smul_eq_mul]; ring_nf; rfl⟩
  have hf : ConcaveOn ℝ (Icc l u) fun x => α*x+A*Real.sin x+B*Real.cos x :=
    (hlin.add ((strictConcaveOn_sin_Icc.concaveOn.subset hs (convex_Icc l u)).smul hA)).add
      ((strictConcaveOn_cos_Icc.concaveOn.subset hc (convex_Icc l u)).smul hB)
  exact (lt_min hml hmu).trans_le (hf.min_le_of_mem_Icc
    (left_mem_Icc.mpr (hx.1.trans hx.2)) (right_mem_Icc.mpr (hx.1.trans hx.2)) hx)

/-- `K + A cos x + B sin x`, with `A, B ≥ 0`, is positive on `[l, u] ⊆ [0, π/2]`
as soon as it is positive at both ends. -/
lemma harmonic_pos_of_endpoints {K A B l u x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hl : 0 ≤ l) (hu : u ≤ Real.pi/2) (hx : l ≤ x ∧ x ≤ u)
    (hleft : 0 < K+A*Real.cos l+B*Real.sin l) (hright : 0 < K+A*Real.cos u+B*Real.sin u) :
    0 < K+A*Real.cos x+B*Real.sin x := by
  have h := trig_concave_gt (α := 0) (m := -K) hB hA hl hu hx (by linarith) (by linarith)
  linarith

/-! ### Radicals and rotating lengths -/

/-- `A cos x + B sin x - R √(p + q sin x)`. -/
def radicalTrig (A B p q R x : ℝ) : ℝ :=
  A*Real.cos x+B*Real.sin x-R*Real.sqrt (p+q*Real.sin x)

lemma radical_second_identity {p q s c r : ℝ} (hr : r ≠ 0)
    (hsq : r^2=p+q*s) (hu : c^2+s^2=1) :
    -q*s/(2*r)-q^2*c^2/(4*r^3) = -r/4+(p^2-q^2)/(4*r^3) := by
  calc
    _ = (-2*q*s*r^2-q^2*c^2)/(4*r^3) := by field_simp [hr]; ring
    _ = (-r^4+p^2-q^2)/(4*r^3) := by
      congr 1
      linear_combination (r^2+p-q*s)*hsq-q^2*hu
    _ = _ := by field_simp [hr]; ring

lemma radical_first_derivative {p q x : ℝ} (hx : 0 < p+q*Real.sin x) :
    HasDerivAt (fun y => Real.sqrt (p+q*Real.sin y))
      (q*Real.cos x/(2*Real.sqrt (p+q*Real.sin x))) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul q).const_add p).sqrt (ne_of_gt hx)
  simpa only [mul_comm] using h

lemma radical_second_derivative {p q x : ℝ} (hx : 0 < p+q*Real.sin x) :
    HasDerivAt (fun y => q*Real.cos y/(2*Real.sqrt (p+q*Real.sin y)))
      (-Real.sqrt (p+q*Real.sin x)/4+
        (p^2-q^2)/(4*(Real.sqrt (p+q*Real.sin x))^3)) x := by
  let r := Real.sqrt (p+q*Real.sin x)
  have hr : 0 < r := Real.sqrt_pos.mpr hx
  have hroot := radical_first_derivative hx
  have hd := ((Real.hasDerivAt_cos x).const_mul q).div (hroot.const_mul 2)
    (mul_ne_zero (by norm_num) (ne_of_gt hr))
  have hformula : HasDerivAt (fun y => q*Real.cos y/(2*Real.sqrt (p+q*Real.sin y)))
      (-q*Real.sin x/(2*r)-q^2*(Real.cos x)^2/(4*r^3)) x := by
    convert hd using 1
    field_simp [ne_of_gt hr]
    ring
  have hsq : r^2=p+q*Real.sin x := Real.sq_sqrt hx.le
  rw [radical_second_identity (ne_of_gt hr) hsq
    (by nlinarith [Real.sin_sq_add_cos_sq x])] at hformula
  exact hformula

/-- `A cos x + B sin x - R √(p + q sin x)` is concave on `[l, u]` if `R ≥ 0`,
`q² ≤ p²`, and on `[l, u]` the radicand is positive and
`R √(p + q sin x) ≤ 4 (A cos x + B sin x)`. -/
theorem radicalTrig_concave {A B p q R l u : ℝ}
    (hR : 0 ≤ R) (hpq : q^2 ≤ p^2)
    (hroot : ∀ x ∈ Icc l u, 0 < p+q*Real.sin x)
    (hbound : ∀ x ∈ Icc l u,
      R*Real.sqrt (p+q*Real.sin x) ≤ 4*(A*Real.cos x+B*Real.sin x)) :
    ConcaveOn ℝ (Icc l u) (radicalTrig A B p q R) := by
  let d : ℝ → ℝ := fun x => -A*Real.sin x+B*Real.cos x-
    R*(q*Real.cos x/(2*Real.sqrt (p+q*Real.sin x)))
  let dd : ℝ → ℝ := fun x => -A*Real.cos x-B*Real.sin x-
    R*(-Real.sqrt (p+q*Real.sin x)/4+(p^2-q^2)/(4*(Real.sqrt (p+q*Real.sin x))^3))
  have hd (x : ℝ) (hx : x ∈ Icc l u) : HasDerivAt (radicalTrig A B p q R) (d x) x := by
    convert (((Real.hasDerivAt_cos x).const_mul A).add
      ((Real.hasDerivAt_sin x).const_mul B)).sub
      ((radical_first_derivative (hroot x hx)).const_mul R) using 1
    · funext y
      simp only [radicalTrig,Pi.add_apply,Pi.sub_apply]
    · simp only [d]
      ring
  have hdd (x : ℝ) (hx : x ∈ Icc l u) : HasDerivAt d (dd x) x := by
    convert (((Real.hasDerivAt_sin x).const_mul (-A)).add
      ((Real.hasDerivAt_cos x).const_mul B)).sub
      ((radical_second_derivative (hroot x hx)).const_mul R) using 1
    simp only [dd]
    ring
  refine concave_of_deriv2 hd hdd fun x hx => ?_
  have hr : 0 < Real.sqrt (p+q*Real.sin x) := Real.sqrt_pos.mpr (hroot x hx)
  have hquot : 0 ≤ R*((p^2-q^2)/(4*(Real.sqrt (p+q*Real.sin x))^3)) :=
    mul_nonneg hR (div_nonneg (sub_nonneg.mpr hpq) (by positivity))
  have hb := hbound x hx
  dsimp [dd]
  nlinarith

private lemma negative_sqrt_quotient_identity {z L d dd r : ℝ}
    (hL : 0 < L) (hs : L^2=z) :
    r*(d^2-2*z*dd)/(4*z*L) = ((-r*dd)*(2*L)-(-r*d)*(2*(d/(2*L))))/(2*L)^2 := by
  subst z
  field_simp [ne_of_gt hL]
  ring

/-- The derivative of `-r f'/(2√f)`, the derivative of `-r√f`, is
`r (f'² - 2f f'')/(4f√f)` where `f > 0`. -/
lemma hasDerivAt_negative_sqrt {f d : ℝ → ℝ} {r x dd : ℝ}
    (hf : HasDerivAt f (d x) x) (hd : HasDerivAt d dd x) (hx : 0 < f x) :
    HasDerivAt (fun y => -r*d y/(2*Real.sqrt (f y)))
      (r*((d x)^2-2*f x*dd)/(4*f x*Real.sqrt (f x))) x := by
  have hroot := hf.sqrt (ne_of_gt hx)
  have hpos : 0 < Real.sqrt (f x) := Real.sqrt_pos.mpr hx
  have hden : 2*Real.sqrt (f x) ≠ 0 := ne_of_gt (by positivity)
  have hquot := HasDerivAt.div (hd.const_mul (-r)) (hroot.const_mul 2) hden
  convert hquot using 1
  all_goals first
    | rfl
    | exact negative_sqrt_quotient_identity hpos (Real.sq_sqrt hx.le)

/-- The squared length `P + Q cos x + T sin x` of a constant vector plus a
turning one. -/
def harmonicArg (P Q T x : ℝ) : ℝ := P+Q*Real.cos x+T*Real.sin x

/-- Minus `R` times the length. -/
def harmonicRoot (R P Q T x : ℝ) : ℝ := -R*Real.sqrt (harmonicArg P Q T x)

/-- The derivative of `harmonicRoot`. -/
def harmonicRootD (R P Q T x : ℝ) : ℝ :=
  -R*(-Q*Real.sin x+T*Real.cos x)/(2*Real.sqrt (harmonicArg P Q T x))

/-- The second derivative of `harmonicRoot`. -/
def harmonicCurvature (R P Q T x : ℝ) : ℝ :=
  let z := Q*Real.cos x+T*Real.sin x
  R*(z^2+2*P*z+Q^2+T^2)/(4*(P+z)*Real.sqrt (P+z))

lemma harmonicRoot_deriv {R P Q T x : ℝ} (hx : 0 < harmonicArg P Q T x) :
    HasDerivAt (harmonicRoot R P Q T) (harmonicRootD R P Q T x) x := by
  have hd : HasDerivAt (harmonicArg P Q T) (-Q*Real.sin x+T*Real.cos x) x := by
    convert ((((Real.hasDerivAt_cos x).const_mul Q).add
      ((Real.hasDerivAt_sin x).const_mul T)).const_add P) using 1
    · funext y
      simp only [harmonicArg,Pi.add_apply,add_assoc]
    · ring
  have hroot := hd.sqrt (ne_of_gt hx)
  convert hroot.const_mul (-R) using 1
  · rfl
  · simp only [harmonicRootD]
    ring

lemma harmonicRoot_second {R P Q T x : ℝ} (hx : 0 < harmonicArg P Q T x) :
    HasDerivAt (harmonicRootD R P Q T) (harmonicCurvature R P Q T x) x := by
  have hf : HasDerivAt (harmonicArg P Q T) (-Q*Real.sin x+T*Real.cos x) x := by
    convert ((((Real.hasDerivAt_cos x).const_mul Q).add
      ((Real.hasDerivAt_sin x).const_mul T)).const_add P) using 1
    · funext y
      simp only [harmonicArg,Pi.add_apply,add_assoc]
    · ring
  have hd : HasDerivAt (fun y => -Q*Real.sin y+T*Real.cos y)
      (-Q*Real.cos x-T*Real.sin x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul (-Q)).add
      ((Real.hasDerivAt_cos x).const_mul T) using 1
    ring
  have hh := hasDerivAt_negative_sqrt (r := R) hf hd hx
  have hid : (-Q*Real.sin x+T*Real.cos x)^2-
      2*harmonicArg P Q T x*(-Q*Real.cos x-T*Real.sin x) =
      (Q*Real.cos x+T*Real.sin x)^2+2*P*(Q*Real.cos x+T*Real.sin x)+Q^2+T^2 := by
    dsimp [harmonicArg]
    linear_combination (Q^2+T^2)*(Real.sin_sq_add_cos_sq x)
  have hA : harmonicArg P Q T x=P+(Q*Real.cos x+T*Real.sin x) := by
    dsimp only [harmonicArg]
    ring
  convert hh using 1
  · rfl
  · rw [hid,hA]
    rfl

lemma harmonic_amplitude_bound {a b Q T x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hQT : Q^2+T^2=4*a^2*b^2) :
    |Q*Real.cos x+T*Real.sin x| ≤ 2*a*b := by
  have hid : (Q*Real.cos x+T*Real.sin x)^2+(-Q*Real.sin x+T*Real.cos x)^2=Q^2+T^2 := by
    linear_combination (Q^2+T^2)*(Real.sin_sq_add_cos_sq x)
  have hnonneg : 0 ≤ 2*a*b := by positivity
  have hs : (Q*Real.cos x+T*Real.sin x)^2 ≤ (2*a*b)^2 := by
    nlinarith [sq_nonneg (-Q*Real.sin x+T*Real.cos x)]
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

lemma harmonic_arg_positive {a b P Q T x : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : a ≠ b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2) : 0 < harmonicArg P Q T x := by
  have hl := (abs_le.mp (harmonic_amplitude_bound (x := x) ha hb hQT)).1
  have hd : 0 < (a-b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  dsimp [harmonicArg]
  nlinarith

lemma harmonic_length_bound {a b P Q T x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2) :
    Real.sqrt (harmonicArg P Q T x) ≤ a+b := by
  have hl := (abs_le.mp (harmonic_amplitude_bound (x := x) ha hb hQT)).1
  have hu := (abs_le.mp (harmonic_amplitude_bound (x := x) ha hb hQT)).2
  have harg : 0 ≤ harmonicArg P Q T x := by
    dsimp [harmonicArg]
    nlinarith [sq_nonneg (a-b)]
  have hr := Real.sq_sqrt harg
  have hn := Real.sqrt_nonneg (harmonicArg P Q T x)
  dsimp [harmonicArg] at *
  nlinarith

lemma rotating_length_factor (a b L : ℝ) :
    4*a*b*L^3-(a+b)*(L^4-(a^2-b^2)^2) =
      (a+b-L)*((a+b)*L^3+(a-b)^2*L^2+(a+b)*(a-b)^2*L+(a+b)^2*(a-b)^2) := by ring

/-- Where the squared length is positive, the second derivative of `-R` times
the length is at most `R ab/(a + b)`. -/
theorem harmonicCurvature_le_harmonic_mean {R a b P Q T x : ℝ}
    (hR : 0 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2)
    (hx : 0 < harmonicArg P Q T x) :
    harmonicCurvature R P Q T x ≤ R*a*b/(a+b) := by
  let L := Real.sqrt (harmonicArg P Q T x)
  have hL : 0 < L := Real.sqrt_pos.mpr hx
  have hLup : L ≤ a+b := harmonic_length_bound ha hb hP hQT
  have hLsq : L^2=harmonicArg P Q T x := Real.sq_sqrt hx.le
  have he : harmonicCurvature R P Q T x = R*(L^4-(a^2-b^2)^2)/(4*L^3) := by
    have hs : L^2=P+(Q*Real.cos x+T*Real.sin x) := by
      rw [hLsq]
      dsimp only [harmonicArg]
      ring
    have hid : (Q*Real.cos x+T*Real.sin x)^2+2*P*(Q*Real.cos x+T*Real.sin x)+Q^2+T^2 =
        L^4-(a^2-b^2)^2 := by
      linear_combination hQT-(P+a^2+b^2)*hP-(L^2+P+(Q*Real.cos x+T*Real.sin x))*hs
    have hroot : Real.sqrt (P+(Q*Real.cos x+T*Real.sin x))=L := by
      rw [← hs]
      exact Real.sqrt_sq hL.le
    dsimp only [harmonicCurvature]
    rw [hid,hroot,← hs]
    ring
  rw [he]
  have hpositive : 0 ≤ (a+b)*L^3+(a-b)^2*L^2+(a+b)*(a-b)^2*L+(a+b)^2*(a-b)^2 := by
    positivity
  have hprod := mul_nonneg (sub_nonneg.mpr hLup) hpositive
  rw [← rotating_length_factor] at hprod
  have hprodR := mul_nonneg hR hprod
  apply (div_le_div_iff₀ (show 0 < 4*L^3 by positivity) hab).mpr
  nlinarith only [hprodR]

lemma harmonic_mean_mono {a b A B : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a+b)
    (hA : a ≤ A) (hB : b ≤ B) : a*b/(a+b) ≤ A*B/(A+B) := by
  have hAB : 0 < A+B := by linarith
  have hp := mul_nonneg (mul_nonneg ha (ha.trans hA)) (sub_nonneg.mpr hB)
  have hq := mul_nonneg (mul_nonneg hb (hb.trans hB)) (sub_nonneg.mpr hA)
  apply (div_le_div_iff₀ hab hAB).mpr
  nlinarith only [hp,hq]

/-- If `a ≤ b` and `Q cos x + T sin x ≤ -2a²`, so that the squared length is at
most `b² - a²`, the second derivative is nonpositive. -/
theorem harmonicCurvature_nonpos_of_opposition {R a b P Q T x : ℝ}
    (hR : 0 ≤ R) (ha : 0 ≤ a) (hb : a ≤ b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2)
    (hx : 0 < harmonicArg P Q T x)
    (hop : Q*Real.cos x+T*Real.sin x ≤ -2*a^2) :
    harmonicCurvature R P Q T x ≤ 0 := by
  have hsq := mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ a+b by linarith)
  have hsecond : 0 ≤ Q*Real.cos x+T*Real.sin x+2*b^2 := by
    dsimp [harmonicArg] at hx
    nlinarith
  have hproduct := mul_nonpos_of_nonpos_of_nonneg
    (show Q*Real.cos x+T*Real.sin x+2*a^2 ≤ 0 by linarith) hsecond
  have hid : (Q*Real.cos x+T*Real.sin x)^2+2*P*(Q*Real.cos x+T*Real.sin x)+Q^2+T^2 =
      (Q*Real.cos x+T*Real.sin x+2*a^2)*(Q*Real.cos x+T*Real.sin x+2*b^2) := by
    linear_combination 2*(Q*Real.cos x+T*Real.sin x)*hP+hQT
  have hA : 0 < P+(Q*Real.cos x+T*Real.sin x) := by
    have h := hx
    dsimp only [harmonicArg] at h
    linarith
  dsimp only [harmonicCurvature]
  rw [hid]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hR hproduct)
    (mul_nonneg (by linarith) (Real.sqrt_nonneg _))

/-! ### Square roots and half angles -/

/-- The tangent majorant of the square root: `√y ≤ (y + c²)/(2c)` for `c > 0`. -/
lemma sqrt_le_tangent {y c : ℝ} (hc : 0 < c) (hy : 0 ≤ y) : Real.sqrt y ≤ (y+c^2)/(2*c) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg (Real.sqrt y-c),Real.sq_sqrt hy]

/-- The tangent majorant squared dominates: `y ≤ ((y + c²)/(2c))²` for `c > 0`. -/
lemma sq_le_tangent_sq {y c : ℝ} (hc : 0 < c) : y ≤ ((y+c^2)/(2*c))^2 := by
  rw [div_pow,le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (y-c^2)]

/-- `sin t/(1 + cos t)`, which is `tan (t/2)`. -/
def halfRatio (t : ℝ) : ℝ := Real.sin t/(1+Real.cos t)

lemma small_polynomial_trig {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) :
    17/25 ≤ Real.cos t ∧ (89/100)*t ≤ Real.sin t ∧
      Real.sin t ≤ t ∧ 1+(12/25)*t ≤ Real.cos t+Real.sin t := by
  have hsq := mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ 4/5+t by linarith [ht.1])
  have ht2 : t^2 ≤ 16/25 := by nlinarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hs := Real.sin_ge_sub_cube ht.1
  have hsinprod := mul_nonneg ht.1 (show 0 ≤ 1-89/100-t^2/6 by linarith)
  have hsumprod := mul_nonneg ht.1 (show 0 ≤ 1-12/25-t/2-t^2/6 by linarith [ht.2])
  exact ⟨by linarith,by nlinarith only [hs,hsinprod],Real.sin_le ht.1,
    by nlinarith only [hs,hc,hsumprod]⟩

lemma halfRatio_den_pos {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) : 0 < 1+Real.cos t := by
  linarith [(small_polynomial_trig ht).1]

lemma halfRatio_nonnegative {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) : 0 ≤ halfRatio t := by
  apply div_nonneg _ (halfRatio_den_pos ht).le
  nlinarith [(small_polynomial_trig ht).2.1,ht.1]

lemma halfRatio_identities {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) :
    halfRatio t*(1+Real.cos t)=Real.sin t ∧ halfRatio t*Real.sin t=1-Real.cos t := by
  have hden := ne_of_gt (halfRatio_den_pos ht)
  constructor
  · exact div_mul_cancel₀ _ hden
  · unfold halfRatio
    field_simp [hden]
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- `tan (t/2) ≥ t/2`, as `2 sin t - t (1 + cos t)` increases from `0`. -/
lemma halfRatio_lower {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) : t/2 ≤ halfRatio t := by
  let H : ℝ → ℝ := fun x => Real.cos x-1+x*Real.sin x
  have hHd (x : ℝ) : HasDerivAt H (x*Real.cos x) x := by
    convert ((Real.hasDerivAt_cos x).sub_const 1).fun_add
      ((hasDerivAt_id x).fun_mul (Real.hasDerivAt_sin x)) using 1 <;> dsimp [H]
    ring
  have hHm : MonotoneOn H (Icc 0 (4/5)) := by
    apply monoOn_of_hasDeriv_nonneg (by dsimp [H]; fun_prop)
      (fun x _ => hHd x)
    intro x hx
    exact mul_nonneg hx.1.le (by linarith [(small_polynomial_trig ⟨hx.1.le,hx.2.le⟩).1])
  let F : ℝ → ℝ := fun x => 2*Real.sin x-x*(1+Real.cos x)
  have hFd (x : ℝ) : HasDerivAt F (H x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul 2).fun_sub
      ((hasDerivAt_id x).fun_mul ((Real.hasDerivAt_cos x).const_add 1)) using 1 <;>
      dsimp [F,H]
    ring
  have hFm : MonotoneOn F (Icc 0 (4/5)) :=
    monoOn_of_hasDeriv_nonneg (by dsimp [F]; fun_prop)
      (fun x _ => hFd x) (fun x hx => by
        simpa [H] using hHm (show (0:ℝ) ∈ Icc 0 (4/5) by constructor <;> norm_num)
          ⟨hx.1.le,hx.2.le⟩ hx.1.le)
  have hF := hFm (show (0:ℝ) ∈ Icc 0 (4/5) by constructor <;> norm_num) ht ht.1
  have hF' : 0 ≤ 2*Real.sin t-t*(1+Real.cos t) := by simpa [F] using hF
  unfold halfRatio
  apply (le_div_iff₀ (halfRatio_den_pos ht)).mpr
  nlinarith only [hF']

/-- `tan (t/2) ≤ 11t/20` on `[0, 4/5]`, by the Taylor bound of `sin` of degree
five. -/
lemma halfRatio_upper {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 4/5) : halfRatio t ≤ (11/20)*t := by
  have hsq := mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ 4/5+t by linarith [ht.1])
  have ht2 : t^2 ≤ 16/25 := by nlinarith
  have hfour := mul_nonneg (sub_nonneg.mpr ht2) (show 0 ≤ 16/25+t^2 by positivity)
  have hp := mul_nonneg ht.1 (show 0 ≤ 1/10-(13/120)*t^2-t^4/120 by nlinarith)
  have hs := sin_upper_five ht.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have hcm := mul_le_mul_of_nonneg_left hc (show 0 ≤ (11/20)*t by linarith [ht.1])
  unfold halfRatio
  apply (div_le_iff₀ (halfRatio_den_pos ht)).mpr
  nlinarith only [hp,hs,hcm]

/-- `cos q - cos d ≥ 89 (d² - q²)/200` for `0 ≤ q ≤ d ≤ 4/5`, since
`cos x + 89x²/200` decreases there. -/
lemma cosine_difference_lower {q d : ℝ} (hq : 0 ≤ q) (hqd : q ≤ d) (hd : d ≤ 4/5) :
    (89/200)*(d^2-q^2) ≤ Real.cos q-Real.cos d := by
  let f : ℝ → ℝ := fun x => Real.cos x+(89/200)*x^2
  have hfd (x : ℝ) : HasDerivAt f (-Real.sin x+(89/100)*x) x := by
    convert (Real.hasDerivAt_cos x).fun_add (((hasDerivAt_id x).fun_pow 2).const_mul (89/200))
      using 1 <;> dsimp [f]
    ring
  have hanti : AntitoneOn f (Icc 0 (4/5)) := by
    apply antiOn_of_hasDeriv_nonpos (by dsimp [f]; fun_prop) (fun x _ => hfd x)
    intro x hx
    linarith [(small_polynomial_trig ⟨hx.1.le,hx.2.le⟩).2.1]
  have h := hanti ⟨hq,hqd.trans hd⟩ ⟨hq.trans hqd,hd⟩ hqd
  dsimp [f] at h
  linarith

lemma halfRatio_shift {w d : ℝ} (hw : 0 ≤ w ∧ w ≤ 4/5) :
    Real.sin (d-w)+halfRatio w*Real.cos (d-w)=Real.sin d-halfRatio w*Real.cos d := by
  have h := halfRatio_identities hw
  rw [Real.sin_sub,Real.cos_sub]
  linear_combination Real.sin d*h.2+Real.cos d*h.1

/-! ### The arcsine -/

lemma asin_half : Real.arcsin (1/2 : ℝ) = Real.pi/6 := by
  have h := Real.arcsin_sin (x := Real.pi/6)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  simpa only [Real.sin_pi_div_six] using h

/-- The arcsine grows at least as fast as the identity, since the sine is
1-Lipschitz: `y-x ≤ arcsin y-arcsin x` for `-1 ≤ x ≤ y ≤ 1`. -/
lemma sub_le_arcsin_sub {x y : ℝ} (hx : -1 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    y-x ≤ Real.arcsin y-Real.arcsin x := by
  have h := Real.abs_sin_sub_sin_le (Real.arcsin y) (Real.arcsin x)
  rwa [Real.sin_arcsin (by linarith) hy,Real.sin_arcsin hx (by linarith),
    abs_of_nonneg (sub_nonneg.2 hxy),
    abs_of_nonneg (sub_nonneg.2 (Real.arcsin_le_arcsin hxy))] at h

lemma arcsin_ge_self {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ Real.arcsin x := by
  simpa using sub_le_arcsin_sub (x := 0) (by norm_num) hx0 hx1

lemma arcsin_le_self_of_nonpos {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 0) :
    Real.arcsin x ≤ x := by
  simpa using sub_le_arcsin_sub (y := 0) hx0 hx1 (by norm_num)

/-- A deliberately non-sharp, polynomial upper bound on `[0,3/5]`. -/
lemma arcsin_le_cubic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 3/5) :
    Real.arcsin x ≤ x+x^3/4 := by
  rcases hx0.eq_or_lt with rfl | hx
  · norm_num
  have hx3 := pow_pos hx 3
  have ht : x+x^3/4 ≤ 109/100*x := by nlinarith [mul_nonneg hx0 (sub_nonneg.2 hx1)]
  rw [Real.arcsin_le_iff_le_sin ⟨by linarith,by linarith⟩
    ⟨by linarith [Real.pi_pos],by linarith [Real.two_le_pi]⟩]
  have hcube := pow_le_pow_left₀ (by positivity) ht 3
  nlinarith [Real.sin_gt_sub_cube (x := x+x^3/4) (by positivity)]

/-- A two-point arcsine comparison, from the concavity of the sine. -/
lemma arcsin_sum_gt_of_sin_lt {u v θ : ℝ}
    (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1)
    (hθ : θ ∈ Icc (0:ℝ) (Real.pi/2)) (hs : Real.sin θ < (u+v)/2) :
    2*θ < Real.arcsin u+Real.arcsin v := by
  have hA := Real.arcsin_nonneg.mpr hu.1
  have hB := Real.arcsin_nonneg.mpr hv.1
  have hA' := Real.arcsin_le_pi_div_two u
  have hB' := Real.arcsin_le_pi_div_two v
  have hc := strictConcaveOn_sin_Icc.concaveOn.2 ⟨hA,by linarith [Real.pi_pos]⟩
    ⟨hB,by linarith [Real.pi_pos]⟩ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  simp only [smul_eq_mul,Real.sin_arcsin (by linarith [hu.1]) hu.2,
    Real.sin_arcsin (by linarith [hv.1]) hv.2] at hc
  by_contra hn
  have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hθ.2
    (show 1/2*Real.arcsin u+1/2*Real.arcsin v ≤ θ by linarith)
  linarith

end SquaresInCircles
