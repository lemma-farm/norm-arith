module

public import SquaresInCircles.Common.Contacts
public import SquaresInCircles.Common.Sweep
public import SquaresInCircles.Common.ExteriorCharts
public import SquaresInCircles.Common.DiskSupport
public import SquaresInCircles.Common.Trigonometry
public import SquaresInCircles.Common.Congruence
public import SquaresInCircles.Six.Constants
public import SquaresInCircles.Common.SeparatingAxes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Six squares: charts and the separating axes of the central square

The normalization works in disks of squared radius at most `Q0`, just above the
square of the optimal radius, with the constants `R0`, `ρ0`, `c0`, `coreRadius`,
`aMin` and `U0` of `Constants`. An exterior square is read as
`orientedSquare t a b`, the square at the phase `t` with centre `(a, b)` in its
frame; a sorted chart has `1/2 ≤ a`, `|b| ≤ a` and
`(a + 1/2)² + (|b| + 1/2)² ≤ Q0` (`ContainedChart`), and if the square avoids
the core disk also `2 - ρ0 ≤ a` and `|b| ≤ U0` (`AvoidsCore`). Its centre lies
within `ρ0` of the origin. By the separating axis theorem it is separated from C
along its own axis, its secondary axis in either direction, or a side of C
(`central_separators_complete`); `centralMargin k t a b cx cy ≥ 0` is the
separating inequality along the axis `k`, with threshold `1/2 + angularWidth t`.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- A point beyond `(A, B)`, with `A, B ≥ 0`, lies outside the disk of squared
radius `Q0` if `(A, B)` does. -/
lemma corner_sq_le {A B x y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAx : A ≤ x) (hBy : B ≤ y)
    (h : x ^ 2 + y ^ 2 ≤ Q0) : A ^ 2 + B ^ 2 ≤ Q0 := by
  nlinarith [mul_le_mul hAx hAx hA (hA.trans hAx), mul_le_mul hBy hBy hB (hB.trans hBy)]

/-! ### Charts of exterior squares -/

/-- A sorted chart `(a, u)` whose far corner lies in the disk of squared radius
`Q0`. -/
abbrev ContainedChart (a u : ℝ) : Prop := ExteriorChart Q0 a u

/-- The closed square avoids the open disk of radius `coreRadius` about the
origin: for `a ≥ 1/2` and `u ≥ 0`, the right side is the squared distance of its
nearest point. -/
def AvoidsCore (a u : ℝ) : Prop :=
  coreRadius ^ 2 ≤ (a - 1 / 2) ^ 2 + (max (u - 1 / 2) 0) ^ 2

namespace ContainedChart
variable {a u : ℝ} (h : ContainedChart a u)
include h

lemma a_le_rho0 : a ≤ rho0 := coordinate_le_of_phi h.u_nonneg h.phi_le

/-- A square that avoids the core has `u < 1/2`: its nearest point is not a
corner. -/
lemma u_lt_half (hc : AvoidsCore a u) : u < 1 / 2 := by
  by_contra! hu
  have hx : 0 ≤ a - 1 / 2 := by linarith [h.half_le]
  have hy : 0 ≤ u - 1 / 2 := by linarith
  have hd : coreRadius ^ 2 ≤ (a - 1 / 2) ^ 2 + (u - 1 / 2) ^ 2 := by
    simpa only [AvoidsCore, max_eq_left hy] using hc
  have hsum : coreRadius ≤ a + u - 1 := by
    by_contra! hs
    have hp := mul_pos (sub_pos.mpr hs)
      (show 0 < coreRadius + (a + u - 1) by linarith [coreRadius_pos])
    nlinarith [mul_nonneg hx hy]
  have hr : 3 / 8 < coreRadius := by linarith [coreRadius_bounds.1]
  have ht := h.containment
  norm_num [Q0] at ht
  nlinarith [mul_lt_mul'' hr hr (by norm_num) (by norm_num)]

/-- A square that avoids the core has `a ≥ aMin`: its nearest point is on its
near edge. -/
lemma aMin_le (hc : AvoidsCore a u) : aMin ≤ a := by
  have hu := h.u_lt_half hc
  have hd : coreRadius ^ 2 ≤ (a - 1 / 2) ^ 2 := by
    simpa only [AvoidsCore, max_eq_right (by linarith : u - 1 / 2 ≤ 0),
      zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using hc
  have hr : coreRadius ≤ a - 1 / 2 := by
    by_contra! hs
    have hp := mul_pos (sub_pos.mpr hs)
      (show 0 < coreRadius + (a - 1 / 2) by linarith [coreRadius_pos, h.half_le])
    nlinarith
  rw [aMin_eq_coreRadius_add_half]
  linarith

/-- A square that avoids the core has `u ≤ U0`, by its far corner at
`a ≥ aMin`. -/
lemma u_le_U0 (hc : AvoidsCore a u) : u ≤ U0 := by
  have ha := h.aMin_le hc
  have hp := mul_nonneg (sub_nonneg.mpr ha)
    (show 0 ≤ a + aMin + 1 by linarith [h.half_le, aMin_bounds.1])
  dsimp [aMin] at hp
  have hs : (u + 1 / 2) ^ 2 ≤ Q0 - (5 / 2 - rho0) ^ 2 := by
    nlinarith [h.containment]
  have hr := Real.le_sqrt_of_sq_le hs
  dsimp [U0]
  linarith

/-- A square that avoids the core has `a > 7/8` and `u < 1/2`. -/
lemma bounds (hc : AvoidsCore a u) : 7 / 8 < a ∧ u < 1 / 2 :=
  ⟨by linarith [h.aMin_le hc, aMin_bounds.1], h.u_lt_half hc⟩

end ContainedChart

/-- If the local coordinates of `o` in the frame of C are at most `c0`, an
exterior square whose interior is disjoint from that of C avoids the core
disk. -/
lemma avoidsCore_of_disjoint {S C : UnitSquare} {o : Point} (T : SquareChart S o)
    (hsort : T.b ≤ T.a) (hout : ¬ openSquare S o)
    (hc : alpha C o ≤ c0 ∧ beta C o ≤ c0)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare C p)) :
    AvoidsCore T.a T.b := by
  obtain ⟨p, hp, hdist⟩ := chart_exists_clipped_point T
  have hn := closed_open_disjoint S C hd hp
  have hcore : coreRadius ^ 2 ≤ normSq (sub p o) := by
    by_contra! ht
    exact hn (inscribed_disk_mem C o coreRadius_pos c0_add_coreRadius hc.1 hc.2 ht)
  have ha : 0 ≤ T.a - 1 / 2 := by linarith [T.exterior hsort hout]
  rw [hdist, max_eq_left ha] at hcore
  exact hcore

/-- A square in the disk of squared radius `Q0` has its centre within `rho0`
of `o`. -/
theorem center_radius_sq {S : UnitSquare} {o : Point}
    (hc : phi (alpha S o) (beta S o) ≤ Q0) :
    normSq (sub S.center o) ≤ rho0 ^ 2 := by
  rw [local_center_norm]
  exact radial_sq_le_of_phi (alpha_nonneg S o) (beta_nonneg S o) (by rw [rho0_sq]; exact hc)

lemma projection_abs_le_rho0 {x y c s : ℝ}
    (hp : x ^ 2 + y ^ 2 ≤ rho0 ^ 2) (hu : c ^ 2 + s ^ 2 = 1) :
    |x*c + y*s| ≤ rho0 := by
  have h := dot_sq_le (p := c) (r := s) hp
  rw [hu,mul_one] at h
  exact abs_le_of_sq_le_sq (by linarith) (by linarith [rho0_bounds.1])

lemma chart_center_east_bound {a b t : ℝ} (hc : ContainedChart a |b|) :
    a * Real.cos t - b * Real.sin t ≤ rho0 := by
  have hh := projection_abs_le_rho0 hc.center_sq_le
    (c := Real.cos t) (s := -Real.sin t)
    (by nlinarith [Real.sin_sq_add_cos_sq t])
  have hu := (abs_le.mp hh).2
  nlinarith

/-! ### Oriented squares -/


/-- The open square of a chart is the model square at its phase and signed
coordinates. -/
theorem chart_same_open_model {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    ∀ p, openSquare S p ↔ openSquare (modelSquare o C.phase (C.a, C.signedB)) p := by
  intro p
  obtain ⟨q, rfl⟩ := (frameEquiv o C.phase).surjective p
  rw [frameEquiv_apply]
  have hm := modelSquare_local o C.phase (C.a, C.signedB) q.1 q.2
  simp only [openSquare, hm.1, hm.2]
  exact C.cartesian q.1 q.2

/-- The open square of a chart about the origin is the oriented square at a
real representative of its phase. -/
theorem chart_same_open_oriented {S : UnitSquare} (C : SquareChart S (0, 0))
    {t : ℝ} (ht : (t : Direction) = C.phase) :
    ∀ p, openSquare S p ↔ openSquare (orientedSquare t C.a C.signedB) p := by
  rw [orientedSquare_eq_modelSquare, ht]
  exact chart_same_open_model C

/-! ### Phases -/

/-- Every phase lies within `π/4` of one of the four axes: it is `v`, `π/2 - v`,
`π + v` or `-π/2 - v` as a direction, for some `|v| ≤ π/4`. -/
theorem four_primary_quadrants (t:ℝ) :
    (∃ v : ℝ, |v|≤Real.pi/4 ∧ (t:Direction)=(v:Direction)) ∨
    (∃ v, |v|≤Real.pi/4 ∧ (t:Direction)=(Real.pi/2-v:ℝ)) ∨
    (∃ v, |v|≤Real.pi/4 ∧ (t:Direction)=(Real.pi+v:ℝ)) ∨
    (∃ v, |v|≤Real.pi/4 ∧ (t:Direction)=(-Real.pi/2-v:ℝ)) := by
  let z := (t:Direction).toReal
  have hz0 : -Real.pi≤z := (t:Direction).neg_pi_lt_toReal.le
  have hz1 : z≤Real.pi := (t:Direction).toReal_le_pi
  have hz : (z:Direction)=(t:Direction) := Real.Angle.coe_toReal _
  by_cases h0 : -Real.pi/4≤z
  · by_cases h1 : z≤Real.pi/4
    · exact Or.inl ⟨z,abs_le.mpr ⟨by linarith,h1⟩,hz.symm⟩
    · by_cases h2 : z≤3*Real.pi/4
      · right; left
        refine ⟨Real.pi/2-z,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
        have h : Real.pi/2-(Real.pi/2-z)=z := by ring
        rw [h]; exact hz.symm
      · right; right; left
        refine ⟨z-Real.pi,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
        have h : Real.pi+(z-Real.pi)=z := by ring
        rw [h]; exact hz.symm
  · by_cases h2 : z≤-3*Real.pi/4
    · right; right; left
      refine ⟨z+Real.pi,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
      have h : Real.pi+(z+Real.pi)=z+2*Real.pi := by ring
      rw [h,Real.Angle.coe_add,Real.Angle.coe_two_pi,add_zero]
      exact hz.symm
    · right; right; right
      refine ⟨-Real.pi/2-z,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
      have h : -Real.pi/2-(-Real.pi/2-z)=z := by ring
      rw [h]; exact hz.symm

/-- Two lifts of one direction less than `2π` apart are equal. -/
lemma phase_eq_of_short_difference {t u:ℝ} (he:(t:Direction)=(u:Direction))
    (hshort:|t-u|<2*Real.pi) : t=u := by
  obtain ⟨k,hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp he
  have hb := abs_lt.mp hshort
  rw [hk] at hb
  have hp : 0<2*Real.pi := by positivity
  have hlo : (-1:ℝ)<(k:ℝ) := by
    by_contra! hc
    have := mul_le_mul_of_nonneg_left hc hp.le
    linarith [hb.1]
  have hhi : (k:ℝ)<1 := by
    by_contra! hc
    have := mul_le_mul_of_nonneg_left hc hp.le
    linarith [hb.2]
  have hlo' : (-1:ℤ)<k := by exact_mod_cast hlo
  have hhi' : k<1 := by exact_mod_cast hhi
  have hz : k=0 := by omega
  simp only [hz,Int.cast_zero,mul_zero] at hk
  linarith

end SquaresInCircles.Six.Normalization

namespace SquaresInCircles.Six

/-! ### Projections of a square -/

/-- The unit normal to the sides `x = ±1/2` of `S`, its first frame axis. -/
def normalX (S : UnitSquare) : Point := (S.cosine,S.sine)

/-- The unit normal to the sides `y = ±1/2` of `S`, its second frame axis. -/
def normalY (S : UnitSquare) : Point := (-S.sine,S.cosine)

lemma open_projection_bounds (S : UnitSquare) {n p : Point} (hn : n ≠ (0,0))
    (hp : openSquare S p) :
    dot n S.center - width S n < dot n p ∧ dot n p < dot n S.center + width S n := by
  have hh := abs_lt.mp (dot_open_bound_of_ne S hn hp)
  rw [dot_sub_right] at hh
  constructor <;> linarith [hh.1,hh.2]

/-- If `n` separates S from T, every point of the open square S projects below
every point of the open square T. -/
lemma separator_orients_pins {S T : UnitSquare} {n p q : Point}
    (hn : n ≠ (0,0)) (hp : openSquare S p) (hq : openSquare T q)
    (hsep : width S n + width T n ≤ dot n (sub T.center S.center)) :
    dot n p < dot n q := by
  have hS := open_projection_bounds S hn hp
  have hT := open_projection_bounds T hn hq
  rw [dot_sub_right] at hsep
  linarith [hS.2,hT.1]

end SquaresInCircles.Six

namespace SquaresInCircles.Six.Normalization

/-! ### Separating axes of the central square -/

/-- A square whose chart is contained lies in the closed disk of radius `R0`. -/
lemma oriented_contained_of_chart {t a b : ℝ} (hc : ContainedChart a |b|) :
    ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0,0) R0 p := by
  intro p hp
  apply inDisk_of_phi_le (S := orientedSquare t a b) (o := (0,0)) (R := R0) _ hp
  rw [orientedSquare_alpha,orientedSquare_beta,R0_sq]
  simpa [phi,abs_of_nonneg (show 0 ≤ a by linarith [hc.half_le])] using hc.containment

/-- The seven axes along which an exterior square can be separated from the
central square: its own axis, its secondary axis in either direction, and the
four sides of the central square. -/
inductive CentralAxis where
  | own | secPlus | secMinus | east | west | north | south
  deriving DecidableEq

/-- The projection of the centre `(cx, cy)` of C on the axis `(cos t, sin t)`. -/
def centralNormal (t cx cy : ℝ) : ℝ := cx*Real.cos t+cy*Real.sin t
/-- The projection of `(cx, cy)` on the axis `(-sin t, cos t)`. -/
def centralTransverse (t cx cy : ℝ) : ℝ := -cx*Real.sin t+cy*Real.cos t

/-- The separating inequality of the exterior square and the central square
along the axis `k`, as a margin: it is nonnegative when they are separated
along `k`. -/
def centralMargin (k : CentralAxis) (t a b cx cy : ℝ) : ℝ :=
  match k with
  | .own => a-1/2-centralNormal t cx cy-angularWidth t
  | .secPlus => b-1/2-centralTransverse t cx cy-angularWidth t
  | .secMinus => centralTransverse t cx cy-1/2-angularWidth t-b
  | .east => centerX t a b-angularWidth t-cx-1/2
  | .west => cx-1/2-centerX t a b-angularWidth t
  | .north => centerY t a b-angularWidth t-cy-1/2
  | .south => cy-1/2-centerY t a b-angularWidth t

/-- At the phase `π + t`, the own margin of a square exceeds its margin along the
west side of C by `(1 - cos t)(a - cx) + sin t (b + cy)`. -/
lemma own_sub_west_margin (t a b cx cy : ℝ) :
    centralMargin .own (Real.pi+t) a b cx cy-centralMargin .west (Real.pi+t) a b cx cy=
      (1-Real.cos t)*(a-cx)+Real.sin t*(b+cy) := by
  simp only [centralMargin,centralNormal,centerX,cos_pi_add,sin_pi_add]
  ring

lemma centralNormal_le_width {t cx cy : ℝ}
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx : cx ≤ 1/2) (hy : cy ≤ 1/2) :
    centralNormal t cx cy ≤ angularWidth t := by
  have hc := mul_le_mul_of_nonneg_left (le_abs_self (Real.cos t)) hx0
  have hs := mul_le_mul_of_nonneg_left (le_abs_self (Real.sin t)) hy0
  have hcx := mul_le_mul_of_nonneg_right hx (abs_nonneg (Real.cos t))
  have hcy := mul_le_mul_of_nonneg_right hy (abs_nonneg (Real.sin t))
  dsimp [centralNormal,angularWidth]
  linarith

lemma primary_difference (t a b cx cy : ℝ) :
    frameX (orientedSquare t a b)
      (sub (orientedSquare t a b).center (cx,cy)) = a-centralNormal t cx cy := by
  dsimp [frameX,orientedSquare,sub,centralNormal]
  linear_combination a*(Real.sin_sq_add_cos_sq t)

/-- An exterior square with interior disjoint from the central square has a
nonnegative margin along one of the seven axes. -/
theorem central_separators_complete {t a b cx cy : ℝ}
    (ha : 1/2 ≤ a) (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy)
    (hx : cx ≤ 1/2) (hy : cy ≤ 1/2)
    (hd : ∀ p, ¬ (openSquare (axisSquare (cx,cy)) p ∧
      openSquare (orientedSquare t a b) p)) :
    ∃ k : CentralAxis, 0 ≤ centralMargin k t a b cx cy := by
  rw [← orientedSquare_zero] at hd
  have hc := centralNormal_le_width (t := t) hx0 hy0 hx hy
  dsimp only [centralNormal] at hc
  have hs := oriented_separating_axes hd
  rw [sub_zero] at hs
  rcases hs with h | h | h | h <;> rcases le_abs'.mp h with h | h <;>
    first
    | exact ⟨.east,by dsimp only [centralMargin,centerX]; linarith⟩
    | exact ⟨.west,by dsimp only [centralMargin,centerX]; linarith⟩
    | exact ⟨.north,by dsimp only [centralMargin,centerY]; linarith⟩
    | exact ⟨.south,by dsimp only [centralMargin,centerY]; linarith⟩
    | exact ⟨.own,by dsimp only [centralMargin,centralNormal]; linarith⟩
    | exact ⟨.secPlus,by dsimp only [centralMargin,centralTransverse]; linarith⟩
    | exact ⟨.secMinus,by dsimp only [centralMargin,centralTransverse]; linarith⟩

lemma east_margin_cap {t a b cx cy : ℝ} (he : 0 ≤ centralMargin .east t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → cx+1/2 ≤ p.1 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).1.1
  dsimp [centralMargin] at he
  linarith

lemma west_margin_cap {t a b cx cy : ℝ} (hw : 0 ≤ centralMargin .west t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → p.1 ≤ cx-1/2 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).1.2
  dsimp [centralMargin] at hw
  linarith

lemma north_margin_cap {t a b cx cy : ℝ} (hn : 0 ≤ centralMargin .north t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → cy+1/2 ≤ p.2 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).2.1
  dsimp [centralMargin] at hn
  linarith

lemma south_margin_cap {t a b cx cy : ℝ} (hs : 0 ≤ centralMargin .south t a b cx cy) :
    ∀ p, closedSquare (orientedSquare t a b) p → p.2 ≤ cy-1/2 := by
  intro p hp
  have hh := (closed_center_coordinate_bounds hp).2.2
  dsimp [centralMargin] at hs
  linarith

/-- If `cx > c0`, a square in the disk is not separated from C along the east
side of C, at any angle `t`. -/
theorem east_separator_negative {a b t cx : ℝ} (hc : ContainedChart a |b|)
    (hx : c0 < cx) :
    a * Real.cos t - b * Real.sin t -
      (|Real.cos t| + |Real.sin t|) / 2 - cx - 1 / 2 < 0 := by
  have hw := one_le_abs_cos_add_abs_sin t
  have hP := chart_center_east_bound (t := t) hc
  dsimp [c0] at hx
  linarith

lemma transverse_distance_lt_one {b cx cy t : ℝ}
    (hb : |b| ≤ U0) (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy)
    (hx : cx ≤ c0) (hy : cy ≤ c0) :
    |b - (-cx * Real.sin t + cy * Real.cos t)| < 1 := by
  have hb' := abs_le.mp hb
  have hslo := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin t) hx0
  have hshi := mul_le_mul_of_nonneg_left (Real.sin_le_one t) hx0
  have hclo := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos t) hy0
  have hchi := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hy0
  apply abs_lt.mpr
  constructor <;> nlinarith [U0_upper, c0_bounds.2]

/-- Both margins of separation along the secondary axis are negative. -/
theorem secondary_separators_fail {b cx cy t : ℝ}
    (hb : |b| ≤ U0) (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy)
    (hx : cx ≤ c0) (hy : cy ≤ c0) :
    b - 1 / 2 - (-cx * Real.sin t + cy * Real.cos t) -
        (|Real.cos t| + |Real.sin t|) / 2 < 0 ∧
      (-cx * Real.sin t + cy * Real.cos t) - 1 / 2 - b -
        (|Real.cos t| + |Real.sin t|) / 2 < 0 := by
  have hd := abs_lt.mp (transverse_distance_lt_one (t := t) hb hx0 hy0 hx hy)
  have hw := one_le_abs_cos_add_abs_sin t
  constructor <;> linarith

end SquaresInCircles.Six.Normalization
