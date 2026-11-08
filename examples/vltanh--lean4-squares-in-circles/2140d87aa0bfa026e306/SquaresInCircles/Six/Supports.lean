module

public import SquaresInCircles.Six.Normalization.Basic

/-!
# Six squares: supports of the squares in the disk

A force `(U, V)` does work at most `R0 |(U, V)| - (|U| + |V|)/2` on the centre
`(a, b)` of a chart in the disk of radius `R0`, by its far vertex
(`local_vertex_support`), and the centre lies within `ρ0` of the origin
(`chart_radial_work`). A linear function on the part of the disk beyond a line
`A = l` is largest at a corner of that part (`disk_corner_support`,
`circle_support_above_primary`), so a force close to the primary axis has the
cap bound `ρ0 U` (`cap_linear_upper`); the far corner gives
`a + (31/100)(|b| + b²) ≤ ρ0` (`radial_transverse_quadratic`), and hence the
cone supports `ρ̄ U` for `|V| ≤ (31/100) U` and `ρ̄ U` plus a multiple of `V²`
in wider cones, by completed squares; and the force `(z + sin q, cos q - 1)` on
D has length at most `(2 + z²/4) sin (q/2) + z cos (q/2)` (`chord_support`). The
centre of C lies in the box `[0, c0]²`, where the work of a force is largest at
a corner or on the face chosen by the sign of a component (`center_face`).
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six
open Normalization

/-! ### The far vertex -/

/-- The far-vertex support of a chart in the disk of radius `R0`. -/
lemma local_vertex_support {a b : ℝ} (hc : ContainedChart a |b|) (U V : ℝ) :
    U*a+V*b ≤ R0*Real.sqrt (U^2+V^2)-(|U|+|V|)/2 :=
  box_vertex_support R0_nonneg (by rw [R0_sq]; exact hc.abs_box) U V

/-- The far-vertex support with the ceiling `radiusBound` and a bound `r` on the
length of the force. -/
lemma vertex_support {a b U V r : ℝ} (hc : ContainedChart a |b|) (hr : 0 ≤ r)
    (hUV : U^2+V^2 ≤ r^2) :
    U*a+V*b ≤ radiusBound*r-(|U|+|V|)/2 := by
  have h := local_vertex_support hc U V
  have hm := mul_le_mul ceiling_bounds.1 (Real.sqrt_le_iff.mpr ⟨hr,hUV⟩)
    (Real.sqrt_nonneg _) (by norm_num [radiusBound])
  linarith

/-- The far-vertex support with the ceiling `1.689`, for a force `(U, -V)`
with `V ≥ 0` of length at most `L`. -/
lemma vertex_linear_upper {a b U V L : ℝ} (hc : ContainedChart a |b|)
    (hV : 0≤V) (hL : 0≤L) (hNorm : U^2+V^2≤L^2) :
    U*a-V*b≤(1.689)*L-(U+V)/2 := by
  have h := local_vertex_support hc U (-V)
  have hs : Real.sqrt (U^2+(-V)^2) ≤ L := Real.sqrt_le_iff.mpr ⟨hL,by rw [neg_sq]; exact hNorm⟩
  have hm := mul_le_mul (show R0 ≤ 1.689 by linarith [R0_bounds.2]) hs
    (Real.sqrt_nonneg _) (by norm_num)
  rw [abs_neg,abs_of_nonneg hV] at h
  linarith [le_abs_self U]

/-- A majorant of the length of the force `(z + sin q, cos q - 1)` on D. -/
def chordMajorant (z q : ℝ) : ℝ := (2+z^2/4)*Real.sin (q/2)+z*Real.cos (q/2)

/-- The far-vertex support of D with the length of its force bounded by
`chordMajorant`, whose square exceeds the squared length by
`(z³/2) sin (q/2) cos (q/2) + (z⁴/16) sin² (q/2)`. -/
lemma chord_support {a b z q : ℝ} (hc : ContainedChart a |b|) (hz : 0 ≤ z)
    (hq : 0 ≤ q ∧ q ≤ Real.pi) :
    (z+Real.sin q)*a+(Real.cos q-1)*b ≤
      radiusBound*chordMajorant z q-(z+Real.sin q+1-Real.cos q)/2 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ q/2 by linarith)
    (show q/2 ≤ Real.pi by linarith [Real.pi_pos])
  have hc2 := Real.cos_nonneg_of_mem_Icc
    (show q/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
  have hsin : Real.sin q=2*Real.sin (q/2)*Real.cos (q/2) := by
    simpa only [show 2*(q/2)=q by ring] using Real.sin_two_mul (q/2)
  have hcos : Real.cos q=2*Real.cos (q/2)^2-1 := by
    simpa only [show 2*(q/2)=q by ring] using Real.cos_two_mul (q/2)
  have hsq : (z+Real.sin q)^2+(Real.cos q-1)^2 ≤ chordMajorant z q^2 := by
    rw [hsin,hcos]
    dsimp [chordMajorant]
    nlinarith [Real.sin_sq_add_cos_sq (q/2),mul_nonneg (mul_nonneg (pow_nonneg hz 3) hs) hc2,
      mul_nonneg (pow_nonneg hz 4) (sq_nonneg (Real.sin (q/2)))]
  have h := vertex_support hc (by dsimp [chordMajorant]; positivity) hsq
  linarith [le_abs_self (z+Real.sin q),neg_le_abs (Real.cos q-1)]

/-! ### The cap and the cones -/

/-- A linear function `A c + B s`, with `c ≥ 0` and `a s ≤ b c`, on the part
`B ≥ b` of the disk of squared radius `Q0` is largest at the point `(a, b)` of
the circle. -/
lemma disk_corner_support {A B a b c s : ℝ}
    (ha : 0 < a) (hB : b ≤ B) (hc : 0 ≤ c)
    (hcircle : a ^ 2 + b ^ 2 = Q0) (hbox : A ^ 2 + B ^ 2 ≤ Q0)
    (hslope : a * s ≤ b * c) : A * c + B * s ≤ a * c + b * s := by
  have ht : a * (A - a) + b * (B - b) ≤ 0 := by
    nlinarith [sq_nonneg (A - a), sq_nonneg (B - b)]
  have hct := mul_nonpos_of_nonneg_of_nonpos hc ht
  have hp := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hB)
  have hprod : a * (A * c + B * s - (a * c + b * s)) ≤ 0 := by
    nlinarith
  by_contra! h
  exact (not_lt_of_ge hprod)
    (mul_pos ha (show 0 < A * c + B * s - (a * c + b * s) by linarith))

/-- The cap bound: if `(ρ0 + 1/2) V ≤ U/2`, the work `U a - V b` is at most
`ρ0 U`, and so at most `1.113 U`. -/
lemma cap_linear_upper {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 0≤U) (hV : 0≤V) (hslope : (rho0+1/2)*V≤U/2) :
    U*a-V*b≤(1.113)*U := by
  have hh := disk_corner_support (A := a+1/2) (B := |b|+1/2)
    (a := rho0+1/2) (b := (1:ℝ)/2) (c := U) (s := V)
    (by linarith [rho0_bounds.1]) (by linarith [abs_nonneg b]) hU
    (by nlinarith [rho0_identity]) hc.containment (by linarith)
  have hsign := mul_le_mul_of_nonneg_left (neg_le_abs b) hV
  have hrad := mul_le_mul_of_nonneg_right (show rho0 ≤ 1.113 by linarith [rho0_bounds.2]) hU
  nlinarith

/-- The centre lies within `ρ0 < 1.113` of the origin. -/
lemma chart_radial_work {a b : ℝ} (hc : ContainedChart a |b|) (g : Point) :
    dot g (a,b)≤(1.113)*vectorLength g := by
  have h := dot_le_radius (v := g) (p := (a,b))
    (show 0≤rho0 by linarith [rho0_bounds.1]) hc.center_sq_le
  have hr := mul_le_mul_of_nonneg_right (show rho0 ≤ 1.113 by linarith [rho0_bounds.2])
    (vectorLength_nonneg g)
  exact h.trans hr

private lemma constrained_root_bounds {a b l : ℝ}
    (hl : 0<l) (ha : l≤a+1/2)
    (hbox : (a+1/2)^2+(|b|+1/2)^2≤Q0) :
    1/2≤Real.sqrt (Q0-l^2) ∧ (Real.sqrt (Q0-l^2))^2+l^2=Q0 := by
  have hA := mul_nonneg (sub_nonneg.mpr ha) (show 0≤a+1/2+l by linarith)
  have hrad : (1/2:ℝ)^2≤Q0-l^2 := by nlinarith [abs_nonneg b,sq_nonneg b]
  refine ⟨Real.le_sqrt_of_sq_le hrad,?_⟩
  have hs := Real.sq_sqrt (show 0≤Q0-l^2 by linarith)
  linarith

/-- If `a + 1/2 ≥ l > 0` and `R0 s ≤ l`, the work of the unit force `(s, c)`,
`s, c ≥ 0`, is at most its value at the corner `(l, √(Q0 - l²))` of the part
`A ≥ l` of the disk. -/
theorem circle_support_above_primary {a b l s c : ℝ}
    (hl : 0<l) (ha : l≤a+1/2)
    (hbox : (a+1/2)^2+(|b|+1/2)^2≤Q0)
    (hs : 0≤ s) (hc : 0≤c) (hu : s^2+c^2=1)
    (hbranch : R0*s≤l) :
    a*s+b*c≤(l-1/2)*s+(Real.sqrt (Q0-l^2)-1/2)*c := by
  let B := Real.sqrt (Q0-l^2)
  have hb := constrained_root_bounds hl ha hbox
  have hBpos : 0<B := by dsimp [B]; linarith [hb.1]
  have hcircle : B^2+l^2=Q0 := hb.2
  have hbranchSq := mul_nonneg (sub_nonneg.mpr hbranch)
    (show 0≤l+R0*s from add_nonneg hl.le (mul_nonneg R0_nonneg hs))
  have hidentity : (B*s)^2-(l*c)^2=(R0*s)^2-l^2 := by
    have h1 := congrArg (fun z : ℝ => s^2*z) hcircle
    have h2 := congrArg (fun z : ℝ => l^2*z) hu
    have h3 := congrArg (fun z : ℝ => s^2*z) R0_sq
    nlinarith only [h1,h2,h3]
  have hslope : B*s≤l*c := by
    by_contra! hbad
    have hp := mul_pos (sub_pos.mpr hbad)
      (show 0<B*s+l*c by nlinarith [mul_nonneg hl.le hc])
    nlinarith only [hp,hidentity,hbranchSq]
  have hcorner := disk_corner_support
    (A := |b|+1/2) (B := a+1/2) (a := B) (b := l) (c := c) (s := s)
    hBpos ha hc hcircle (by linarith) hslope
  have hbproj := mul_le_mul_of_nonneg_right (le_abs_self b) hc
  change a*s+b*c≤(l-1/2)*s+(B-1/2)*c
  nlinarith only [hcorner,hbproj]

/-- Every contained state satisfies `a + 31 (|b| + b²)/100 ≤ ρ0`. -/
theorem radial_transverse_quadratic {a b : ℝ} (hc : ContainedChart a |b|) :
    a+(31/100)*(|b|+b^2)≤rho0 := by
  have ha := hc.a_le_rho0
  have hcircle : |b|+b^2≤(rho0-a)*(rho0+a+1) := by
    nlinarith [hc.containment,rho0_sq,sq_abs b]
  have hcoef : (31/100)*(rho0+a+1)≤1 := by
    linarith [rho0_bounds.2]
  have hprod := mul_nonneg (sub_nonneg.mpr ha)
    (show 0≤1-(31/100)*(rho0+a+1) by linarith)
  nlinarith only [hcircle,hprod]

/-- A force in the axial cone `|V| ≤ (31/100) U` does work at most `ρ̄ U`. -/
lemma cone_support {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 0 ≤ U) (hV : |V| ≤ (31/100)*U) :
    U*a+V*b ≤ rhoBound*U := by
  have hrad := radial_transverse_quadratic hc
  have hp := mul_nonneg hU (show 0 ≤ rho0-a-(31/100)*|b| by nlinarith [sq_nonneg b])
  have hv := mul_le_mul_of_nonneg_right hV (abs_nonneg b)
  have hm : V*b ≤ |V| * |b| := by simpa only [abs_mul] using le_abs_self (V*b)
  have hR := mul_le_mul_of_nonneg_right ceiling_bounds.2.1 hU
  nlinarith only [hp,hv,hm,hR]

/-- A force with `U ≥ 7/5` and `|V| ≤ U/2` does work at most `ρ̄ U + V²/12`. -/
lemma soft_support {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 7/5 ≤ U) (hV : |V| ≤ U/2) :
    U*a+V*b ≤ rhoBound*U+V^2/12 := by
  have hrad := radial_transverse_quadratic hc
  have hm := mul_nonneg (show 0 ≤ U by linarith)
    (show 0 ≤ rho0-a-(31/100)*(|b|+b^2) by linarith)
  have hlinear := mul_nonneg (show 0 ≤ (31/100)*U-(31/50)*|V| by linarith) (abs_nonneg b)
  have hquadratic := mul_nonneg (sub_nonneg.mpr hU) (sq_nonneg b)
  have hprod : V*b ≤ |V| * |b| := by simpa only [abs_mul] using le_abs_self (V*b)
  have hsq : 0 ≤ (31/100)*(7/5)*|b|^2-(19/50)*|b| * |V|+|V|^2/12 := by
    nlinarith [sq_nonneg (|V|-(57/25)*|b|),sq_nonneg |b|]
  rw [sq_abs,sq_abs] at hsq
  have hR := mul_le_mul_of_nonneg_right ceiling_bounds.2.1
    (show 0 ≤ U by linarith)
  nlinarith only [hm,hlinear,hquadratic,hprod,hsq,hR]

/-- A force with `U ≥ 33/20` and `|V| ≤ 3U/5` does work at most
`ρ̄ U + (3/25) V²`. -/
lemma wide_support {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 33/20 ≤ U) (hV : |V| ≤ (3/5)*U) :
    U*a+V*b ≤ rhoBound*U+(3/25)*V^2 := by
  have hrad := radial_transverse_quadratic hc
  have hm := mul_nonneg (show 0 ≤ U by linarith)
    (show 0 ≤ rho0-a-(31/100)*(|b|+b^2) by linarith)
  have hlinear := mul_nonneg (show 0 ≤ (31/100)*U-(31/60)*|V| by linarith) (abs_nonneg b)
  have hquadratic := mul_nonneg (show 0 ≤ (31/100)*U-1/2 by linarith) (sq_nonneg b)
  have hprod : V*b ≤ |V| * |b| := by simpa only [abs_mul] using le_abs_self (V*b)
  have hsq : 0 ≤ |b|^2/2-(29/60)*|b| * |V|+(3/25)*|V|^2 := by
    nlinarith [sq_nonneg (|b|-(29/60)*|V|),sq_nonneg |V|]
  rw [sq_abs,sq_abs] at hsq
  have hR := mul_le_mul_of_nonneg_right ceiling_bounds.2.1
    (show 0 ≤ U by linarith)
  nlinarith only [hm,hlinear,hquadratic,hprod,hsq,hR]

/-- The support of a nearly radial force exceeds `ρ0 U` by at most `1/160`,
by the far-corner bound `a + (31/100)(|b| + b²) ≤ ρ0` and a completed square. -/
theorem narrow_support {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 3/5≤U ∧ U≤7/10) (hV : |V|≤(2/5)*U) : U*a+V*b≤rho0*U+1/160 := by
  have hU0 : 0≤U := by linarith [hU.1]
  have hrad := radial_transverse_quadratic hc
  have hm := mul_nonneg hU0 (show 0≤rho0-a-(31/100)*(|b|+b^2) by linarith)
  have hlinear := mul_nonneg (show 0≤(31/100)*U-(31/40)*|V| by linarith [hV]) (abs_nonneg b)
  have hquadratic := mul_nonneg (sub_nonneg.mpr hU.1) (sq_nonneg b)
  have hproduct : V*b≤|V| *|b| := by simpa only [abs_mul] using le_abs_self (V*b)
  have hsq : 0≤(31/100)*(3/5)*|b|^2-(9/40)*|b| *|V|+(7/100)*|V|^2 := by
    nlinarith [sq_nonneg (|V|-(45/28)*|b|),sq_nonneg |b|]
  rw [sq_abs,sq_abs] at hsq
  have hsoft : U*a+V*b≤rho0*U+(7/100)*V^2 := by
    nlinarith only [hm,hlinear,hquadratic,hproduct,hsq]
  have habs : |V|≤7/25 := by linarith [hV,hU.2]
  have hbound : V^2≤(7/25:ℝ)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr habs) (show 0≤7/25+|V| by positivity),sq_abs V]
  nlinarith only [hsoft,hbound]

/-! ### The box of the centre of C -/

/-- On `[0, h]` the work `x v` is at most `h` times the positive part of `v`. -/
lemma scalar_box_support {x h v : ℝ} (hx : 0 ≤ x ∧ x ≤ h) : x*v ≤ h*max v 0 := by
  by_cases hv : 0 ≤ v
  · rw [max_eq_left hv]
    exact mul_le_mul_of_nonneg_right hx.2 hv
  · rw [max_eq_right (le_of_not_ge hv),mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hx.1 (le_of_not_ge hv)

/-- The work of a force with components at most `X, Y ≥ 0` on the central
square, whose centre lies in the box `[0, c0]²`. -/
lemma coarse_central_work {cx cy gx gy X Y : ℝ}
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hX : 0≤X) (hY : 0≤Y) (hx : gx≤X) (hy : gy≤Y) :
    gx*cx+gy*cy≤(0.113)*(X+Y) := by
  have hcx : cx≤0.113 := by dsimp [c0] at hc; linarith [rho0_bounds.2]
  have hcy : cy≤0.113 := by dsimp [c0] at hc; linarith [rho0_bounds.2]
  have h1 := mul_le_mul_of_nonneg_right hx hc.1.1
  have h2 := mul_le_mul_of_nonneg_right hy hc.2.1
  have h3 := mul_le_mul_of_nonneg_left hcx hX
  have h4 := mul_le_mul_of_nonneg_left hcy hY
  nlinarith

/-- The work on the centre of C for a force with nonnegative components is at
most its value at the corner `(c̄, c̄)` of the box. -/
lemma center_corner {X Y cx cy : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hx : cx ≤ c0) (hy : cy ≤ c0) :
    X*cx+Y*cy ≤ coreUpper*(X+Y) := by
  have hc := ceiling_bounds.2.2.2
  nlinarith [mul_le_mul_of_nonneg_left (hx.trans hc) hX,mul_le_mul_of_nonneg_left (hy.trans hc) hY]

/-- The work on the centre of C, for a force with a nonnegative first component,
is at most its value on the face `y` of the box chosen by the sign of the second
component. -/
lemma center_face {X Y cx cy : ℝ} (hX : 0 ≤ X) (hx : cx ≤ coreUpper)
    (hy : 0 ≤ cy ∧ cy ≤ coreUpper) :
    ∃ y, (y = 0 ∨ y = coreUpper) ∧ X*cx+Y*cy ≤ coreUpper*X+y*Y := by
  have hx' := mul_le_mul_of_nonneg_left hx hX
  by_cases hY : 0 ≤ Y
  · exact ⟨_,Or.inr rfl,by nlinarith [mul_le_mul_of_nonneg_left hy.2 hY]⟩
  · exact ⟨0,Or.inl rfl,by nlinarith [mul_nonpos_of_nonneg_of_nonpos hy.1 (le_of_not_ge hY)]⟩

end SquaresInCircles.Six
