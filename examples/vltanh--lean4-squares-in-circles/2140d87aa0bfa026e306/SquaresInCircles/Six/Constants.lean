module

public import SquaresInCircles.Common.Basic
public import SquaresInCircles.Common.Trigonometry

/-!
# Six squares: the constants

The constants of the six-square proof, each with one decimal bracket.

The model (defined with the statement, in `Geometry.lean`) is built from
`h = √2/2` and the smaller root `s*` of `s² - A s + B`; `t*`, `d*` and the
squared radius `q* = 2s*² + 4s* + 5/2` follow from it. The far corners of E and
W and the far vertices of D lie on the circle of squared radius `q*`. The
stress of the model has weight `1` on the four contacts of
C, `r* = (s* + 1/2)/(s* + 3/2)` on N–W and E–S, and `m* = (1 + r*) k*`, with
`k* = (t* + 1/2)/(3/2 - s*)`, on W–D and D–S; the force on D has length
`diagonalK = 2h m*`, the centre of D lies at distance `ρ* = √(q* - 1/4) - 1/2`
from the disk centre, and `pairBase = m* (1/2 - t*)`. The forces of the model
point at the far corners of N and W on the circle, which gives their lengths,
and `2 pairBase + diagonalK (1 - ρ*) = 0` because `ρ* = 2h d*`. The brackets
have as many decimals as their uses need: seven or eight for `h`, `s*`, `t*`,
`r*`, `k*` and `m*`, from which the others are computed, and at most five for
the rest. `s*` comes from the sign of its quadratic, the others from it by
products, quotients and square roots.

The normalization works below the ceiling `Q0 = 2.85118` on the squared radius,
less than `3·10⁻⁶` above `q*`. With `R0 = √Q0`, the number
`ρ0 = √(Q0 - 1/4) - 1/2` is the largest radial coordinate of a square in the
disk, `c0 = ρ0 - 1` bounds the centre of the central square C,
`coreRadius = 3/2 - ρ0` is the radius of a disk about the origin inside C,
`aMin = 2 - ρ0` is the least radial coordinate of a square outside that disk and
`U0` its largest transverse coordinate. The decimals `radiusBound`, `rhoBound`,
`coreLower` and `coreUpper` stand for `R0`, `ρ0` and `c0`, rounded, in the
estimates, and `A` and `B` for `1/2 ∓ coreUpper`.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six

/-! ### The model -/

lemma trig_bracket_half :
    0.8775 ≤ Real.cos (1/2) ∧ Real.cos (1/2) ≤ 0.878 ∧
    0.4794 ≤ Real.sin (1/2) ∧ Real.sin (1/2) ≤ 0.4795 := by
  have h := trig_bracket (l := 1/2) (u := 1/2) (x := 1/2) (by norm_num)
    (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  norm_num at h
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma trig_bracket_two_thirds :
    0.785 ≤ Real.cos (2/3) ∧ Real.cos (2/3) ≤ 0.787 ∧
    0.618 ≤ Real.sin (2/3) ∧ Real.sin (2/3) ≤ 0.619 := by
  have h := trig_bracket (l := 2/3) (u := 2/3) (x := 2/3) (by norm_num)
    (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  norm_num at h
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma trig_bracket_seven_sixths :
    0.3931 ≤ Real.cos (7/6) ∧ Real.cos (7/6) ≤ 0.4 ∧
    0.9194 ≤ Real.sin (7/6) ∧ Real.sin (7/6) ≤ 0.9201 := by
  have h := trig_bracket (l := 7/6) (u := 7/6) (x := 7/6) (by norm_num)
    (by linarith [Real.pi_gt_d2]) ⟨le_rfl,le_rfl⟩
  norm_num at h
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma hStar_pos : 0 < hStar := halfDiagonal_pos

lemma hStar_sq : hStar^2=1/2 := halfDiagonal_sq

/-- `hStar` is the cosine and the sine of `π/4`. -/
lemma cos_quarter : Real.cos (Real.pi/4)=hStar := by simp [hStar]

lemma sin_quarter : Real.sin (Real.pi/4)=hStar := by simp [hStar]

lemma hStar_bounds : 0.70710678 < hStar ∧ hStar < 0.70710679 := by
  constructor <;> nlinarith [hStar_sq,hStar_pos]

private lemma AStar_bounds : 10 < AStar ∧ AStar < 11 := by
  dsimp [AStar]
  constructor <;> linarith [hStar_bounds.1,hStar_bounds.2]

private lemma BStar_bounds : 4/5 < BStar ∧ BStar < 1 := by
  dsimp [BStar]
  constructor <;> linarith [hStar_bounds.1,hStar_bounds.2]

private lemma discriminant_pos : 0 < discriminant := by
  dsimp [discriminant]
  nlinarith [AStar_bounds.1,BStar_bounds.2,sq_nonneg (AStar-10)]

private lemma sStar_den_pos : 0 < AStar+Real.sqrt discriminant := by
  linarith [AStar_bounds.1,Real.sqrt_nonneg discriminant]

lemma sStar_pos : 0 < sStar := by
  dsimp [sStar]
  exact div_pos (by linarith [BStar_bounds.1]) sStar_den_pos

private lemma sStar_lt_fifth : sStar < 1/5 := by
  rw [sStar,div_lt_iff₀ sStar_den_pos]
  linarith [BStar_bounds.2,AStar_bounds.1,Real.sqrt_nonneg discriminant]

/-- `s*` is a root of `s² - A s + B`. -/
lemma sStar_polynomial : sStar^2-AStar*sStar+BStar=0 := by
  have hd : AStar+Real.sqrt discriminant ≠ 0 := ne_of_gt sStar_den_pos
  have hs : sStar*(AStar+Real.sqrt discriminant)=2*BStar := by
    rw [sStar]
    exact div_mul_cancel₀ _ hd
  have hr := Real.sq_sqrt discriminant_pos.le
  have hp : (sStar^2-AStar*sStar+BStar)*(AStar+Real.sqrt discriminant)^2=0 := by
    calc
      _ = (sStar*(AStar+Real.sqrt discriminant))^2-
          AStar*(sStar*(AStar+Real.sqrt discriminant))*(AStar+Real.sqrt discriminant)+
          BStar*(AStar+Real.sqrt discriminant)^2 := by ring
      _ = BStar*((Real.sqrt discriminant)^2-discriminant) := by
        rw [hs]
        dsimp [discriminant]
        ring
      _ = 0 := by rw [hr]; ring
  exact (mul_eq_zero.mp hp).resolve_right (pow_ne_zero 2 hd)

/-- `s*` is the root of the quadratic below `1/5`, where the quadratic changes
sign between the two ends of the bracket. -/
lemma sStar_bounds : 0.08424567 < sStar ∧ sStar < 0.0842457 := by
  have hs := sStar_lt_fifth
  have hA := AStar_bounds.1
  have hp (x : ℝ) : x^2-AStar*x+BStar=(x-sStar)*(x+sStar-AStar) := by
    linear_combination sStar_polynomial
  have pl : 0 < 0.08424567^2-AStar*0.08424567+BStar := by
    dsimp [AStar,BStar]
    linarith [hStar_bounds.1,hStar_bounds.2]
  have pu : 0.0842457^2-AStar*0.0842457+BStar < 0 := by
    dsimp [AStar,BStar]
    linarith [hStar_bounds.1,hStar_bounds.2]
  rw [hp] at pl pu
  exact ⟨by linarith [neg_of_mul_pos_left pl (by linarith)],
    by linarith [pos_of_mul_neg_left pu (by linarith)]⟩

lemma tStar_bounds : 0.4202266 < tStar ∧ tStar < 0.4202267 := by
  obtain ⟨hh1,hh2⟩ := hStar_bounds
  obtain ⟨hs1,hs2⟩ := sStar_bounds
  dsimp [tStar]
  constructor <;> nlinarith [mul_pos (sub_pos.mpr hh1) (sub_pos.mpr hs1),
    mul_pos (sub_pos.mpr hh1) (sub_pos.mpr hs2)]

lemma dStar_pos : 0 < dStar := by
  dsimp [dStar]
  linarith [hStar_bounds.1,tStar_bounds.2]

lemma qStar_pos : 0 < qStar := by
  dsimp [qStar]
  nlinarith [sStar_pos,sq_nonneg sStar]

lemma qStar_bounds : 2.85117 < qStar ∧ qStar < 2.85118 := by
  obtain ⟨hs1,hs2⟩ := sStar_bounds
  dsimp [qStar]
  constructor <;> nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hs1),
    mul_pos (sub_pos.mpr hs2) sStar_pos]

lemma radius_pos : 0 < radius := Real.sqrt_pos.mpr qStar_pos

lemma radius_sq : radius^2=qStar := Real.sq_sqrt qStar_pos.le

lemma radius_bounds : 1.68854 < radius ∧ radius < 1.68855 := by
  have hq := qStar_bounds
  constructor
  · rw [radius,Real.lt_sqrt (by norm_num)]; linarith
  · rw [radius,Real.sqrt_lt' (by norm_num)]; linarith

/-- The far corner `(s* + 3/2, s* + 1/2)` of E lies on the circle. -/
lemma east_radius_identity : qStar=(sStar+1/2)^2+(sStar+3/2)^2 := by
  dsimp [qStar]
  ring

/-- The far corner `(3/2 - s*, t* + 1/2)` of W, reflected, lies on the circle:
with `h² = 1/2`, the two sides differ by `1200 h - 849` times the quadratic of
`s*`. -/
lemma west_radius_identity : qStar=(3/2-sStar)^2+(tStar+1/2)^2 := by
  have hp := sStar_polynomial
  have hh := hStar_sq
  dsimp [qStar,tStar,AStar,BStar] at *
  linear_combination (1200*hStar-849)*hp-
    ((30*sStar-9/2)^2-1200*(1940*sStar/267-432/712))*hh

/-- The far vertices of D lie on the circle: with `h² = 1/2`, the two sides differ
by `2400 h - 1698` times the quadratic of `s*`. -/
lemma diagonal_radius_identity : qStar=2*dStar^2+2*hStar*dStar+1/2 := by
  have hp := sStar_polynomial
  have hh := hStar_sq
  dsimp [qStar,dStar,tStar,AStar,BStar] at *
  linear_combination (2400*hStar-1698)*hp-
    (2*(11/2-30*sStar)*(13/2-30*sStar)-2400*(1940*sStar/267-432/712))*hh

/-! ### The stress of the model -/

/-- The weight of N–W and E–S in the stress of the model. -/
def rStar : ℝ := (sStar+1/2)/(sStar+3/2)
/-- The factor `k*` of the weight `m* = (1 + r*) k*`. -/
def kStar : ℝ := (tStar+1/2)/(3/2-sStar)
/-- The weight of W–D and D–S in the stress of the model. -/
def mStar : ℝ := (1+rStar)*kStar
/-- The length of the force on D in the model. -/
def diagonalK : ℝ := 2*hStar*mStar
/-- The distance of the centre of D from the disk centre in the model, the largest
first coordinate of the centre of a unit square in the disk whose second
coordinate is `0`. -/
def rhoStar : ℝ := Real.sqrt (radius^2-1/4)-1/2
/-- The amount by which the thresholds of the pair N, W of the model exceed the
supports of its forces. -/
def pairBase : ℝ := mStar*(1/2-tStar)

lemma rStar_den_pos : 0 < sStar+3/2 := by linarith [sStar_pos]
lemma kStar_den_pos : 0 < 3/2-sStar := by linarith [sStar_bounds.2]

lemma rStar_bounds : 0.3687847 < rStar ∧ rStar < 0.3687848 := by
  have hs := sStar_bounds
  constructor
  · rw [rStar,lt_div_iff₀ rStar_den_pos]; linarith
  · rw [rStar,div_lt_iff₀ rStar_den_pos]; linarith

lemma kStar_bounds : 0.6499903 < kStar ∧ kStar < 0.6499904 := by
  have hs := sStar_bounds
  have ht := tStar_bounds
  constructor
  · rw [kStar,lt_div_iff₀ kStar_den_pos]; linarith
  · rw [kStar,div_lt_iff₀ kStar_den_pos]; linarith

lemma rStar_pos : 0 < rStar := by linarith [rStar_bounds.1]
lemma kStar_pos : 0 < kStar := by linarith [kStar_bounds.1]
lemma one_add_rStar_pos : 0 < 1+rStar := by linarith [rStar_bounds.1]

lemma mStar_bounds : 0.8896967 < mStar ∧ mStar < 0.889697 := by
  obtain ⟨hr1,hr2⟩ := rStar_bounds
  obtain ⟨hk1,hk2⟩ := kStar_bounds
  dsimp [mStar]
  constructor <;> nlinarith [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hk1),
    mul_pos (sub_pos.mpr hr2) (sub_pos.mpr hk2)]

lemma mStar_pos : 0 < mStar := by linarith [mStar_bounds.1]

lemma diagonalK_bounds : 1.258 < diagonalK ∧ diagonalK < 1.259 := by
  obtain ⟨hh1,hh2⟩ := hStar_bounds
  obtain ⟨hm1,hm2⟩ := mStar_bounds
  dsimp [diagonalK]
  constructor <;> nlinarith [mul_pos (sub_pos.mpr hh1) (sub_pos.mpr hm1),
    mul_pos (sub_pos.mpr hh2) (sub_pos.mpr hm2)]

lemma diagonalK_pos : 0 < diagonalK := by linarith [diagonalK_bounds.1]

lemma pairBase_bounds : 0.07097 < pairBase ∧ pairBase < 0.07098 := by
  obtain ⟨hm1,hm2⟩ := mStar_bounds
  obtain ⟨ht1,ht2⟩ := tStar_bounds
  dsimp [pairBase]
  constructor <;> nlinarith [mul_pos (sub_pos.mpr hm1) (sub_pos.mpr ht2),
    mul_pos (sub_pos.mpr hm2) (sub_pos.mpr ht1)]

lemma rhoStar_bounds : 1.11281 < rhoStar ∧ rhoStar < 1.11282 := by
  have hq := qStar_bounds
  have hR := radius_sq
  constructor
  · rw [rhoStar,lt_sub_iff_add_lt,Real.lt_sqrt (by norm_num)]; linarith
  · rw [rhoStar,sub_lt_iff_lt_add,Real.sqrt_lt' (by norm_num)]; linarith

lemma rhoStar_identity : rhoStar^2+rhoStar+1/2=qStar := by
  have hR := radius_sq
  have h := Real.sq_sqrt (show 0 ≤ radius^2-1/4 by nlinarith [radius_bounds.1])
  dsimp [rhoStar]
  nlinarith

/-- The centre of D in the model is at distance `rhoStar` from the disk centre. -/
lemma rhoStar_eq_two_h_d : rhoStar=2*hStar*dStar := by
  have hx : (2*hStar*dStar)^2+2*hStar*dStar+1/2=qStar := by
    linear_combination 4*dStar^2*hStar_sq-diagonal_radius_identity
  have hsum : 0 < rhoStar+2*hStar*dStar+1 := by
    have := mul_pos hStar_pos dStar_pos
    linarith [rhoStar_bounds.1]
  have hf : (rhoStar-2*hStar*dStar)*(rhoStar+2*hStar*dStar+1)=0 := by
    linear_combination rhoStar_identity-hx
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hsum.ne')

/-- The force `(1, rStar)` on E of the model points at its far corner
`(sStar + 3/2, sStar + 1/2)` on the circle, so `radius` times its length is its
work on that corner. -/
lemma radius_mul_north_length :
    radius*Real.sqrt (1+rStar^2)=(sStar+3/2)+rStar*(sStar+1/2) := by
  have hd := rStar_den_pos
  have hr : rStar*(sStar+3/2)=sStar+1/2 := div_mul_cancel₀ _ hd.ne'
  have h1 : 1+rStar^2=(radius/(sStar+3/2))^2 := by
    rw [div_pow,radius_sq,eq_div_iff (pow_ne_zero 2 hd.ne')]
    linear_combination (rStar*(sStar+3/2)+(sStar+1/2))*hr-east_radius_identity
  rw [h1,Real.sqrt_sq (div_nonneg radius_pos.le hd.le),mul_div_assoc',← pow_two,radius_sq,
    div_eq_iff hd.ne']
  linear_combination east_radius_identity-(sStar+1/2)*hr

/-- The force `(1 + rStar, mStar)` on S of the model points at its far corner
`(3/2 - sStar, tStar + 1/2)` on the circle. -/
lemma radius_mul_west_length :
    radius*Real.sqrt ((1+rStar)^2+mStar^2)=(1+rStar)*(3/2-sStar)+mStar*(tStar+1/2) := by
  have hd := kStar_den_pos
  have hr := one_add_rStar_pos
  have hk : kStar*(3/2-sStar)=tStar+1/2 := div_mul_cancel₀ _ hd.ne'
  have h1 : (1+rStar)^2+mStar^2=((1+rStar)*radius/(3/2-sStar))^2 := by
    rw [div_pow,mul_pow,radius_sq,eq_div_iff (pow_ne_zero 2 hd.ne'),mStar]
    linear_combination (1+rStar)^2*(kStar*(3/2-sStar)+(tStar+1/2))*hk-
      (1+rStar)^2*west_radius_identity
  rw [h1,Real.sqrt_sq (div_nonneg (mul_nonneg hr.le radius_pos.le) hd.le),mul_div_assoc',
    show radius*((1+rStar)*radius)=(1+rStar)*radius^2 by ring,radius_sq,div_eq_iff hd.ne',mStar]
  linear_combination (1+rStar)*west_radius_identity-(1+rStar)*(tStar+1/2)*hk

/-- The pairs N, W and E, S of the model exceed their supports by `pairBase` each,
and the turned square falls short of its support by `diagonalK (rhoStar - 1)`:
the two cancel. -/
lemma pairBase_diagonal_identity : 2*pairBase+diagonalK*(1-rhoStar)=0 := by
  rw [rhoStar_eq_two_h_d]
  dsimp [pairBase,diagonalK,dStar]
  linear_combination (-4*mStar*(1/2+hStar-tStar))*hStar_sq

/-! ### The ceiling of the normalization -/

/-- The ceiling on the squared radius, just above `qStar`. -/
def Q0 : ℝ := 2.85118

/-- The radius of the disk of squared radius `Q0`. -/
def R0 : ℝ := Real.sqrt Q0

/-- The largest radial offset of a square in the disk: its far corner
`(ρ0 + 1/2, 1/2)` lies on the circle of radius `R0`. -/
def rho0 : ℝ := Real.sqrt (Q0-1/4)-1/2

/-- The bound on the coordinates of the centre of C in its frame. -/
def c0 : ℝ := rho0-1

/-- The radius of a disk about the origin inside C, for the centre of C in
`[0, c0]²`. -/
def coreRadius : ℝ := 3/2-rho0

/-- The least radial coordinate of an exterior square that avoids the core. -/
def aMin : ℝ := 2-rho0

/-- The largest transverse coordinate of an exterior square that avoids the
core: its far corner at `a = aMin`. -/
def U0 : ℝ := Real.sqrt (Q0-(5/2-rho0)^2)-1/2

/-- The squared optimal radius lies below the ceiling `Q0`. -/
lemma qStar_lt_Q0 : qStar < Q0 := by
  dsimp [Q0]
  linarith [qStar_bounds.2]

lemma Q0_pos : 0 < Q0 := by norm_num [Q0]

lemma R0_nonneg : 0 ≤ R0 := Real.sqrt_nonneg _

lemma R0_sq : R0^2=Q0 := Real.sq_sqrt Q0_pos.le

lemma R0_pos : 0 < R0 := Real.sqrt_pos.mpr Q0_pos

lemma R0_bounds : 1.6885 < R0 ∧ R0 < 1.6886 := by
  constructor
  · rw [R0,Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  · rw [R0,Real.sqrt_lt' (by norm_num)]
    norm_num [Q0]

/-- The corners `(ρ0 + 1/2, ±1/2)` lie on the circle of radius `R0`. -/
lemma rho0_identity : (rho0+1/2)^2+1/4=Q0 := by
  have hs := Real.sq_sqrt (show 0 ≤ Q0-1/4 by norm_num [Q0])
  dsimp [rho0]
  nlinarith

lemma rho0_sq : rho0^2+rho0+1/2=Q0 := by
  nlinarith [rho0_identity]

lemma rho0_bounds : 1.11281 < rho0 ∧ rho0 < 1.11282 := by
  constructor
  · rw [rho0,lt_sub_iff_add_lt,Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  · rw [rho0,sub_lt_iff_lt_add,Real.sqrt_lt' (by norm_num)]
    norm_num [Q0]

/-- The model lies inside the ceiling: `ρ* < ρ0`, as `q* < Q0`. -/
lemma rhoStar_lt_rho0 : rhoStar < rho0 := by
  nlinarith [rhoStar_identity,rho0_sq,qStar_lt_Q0,rhoStar_bounds.1,rho0_bounds.1]

lemma c0_bounds : 0.11281 < c0 ∧ c0 < 0.11282 := by
  dsimp [c0]
  constructor <;> linarith [rho0_bounds.1,rho0_bounds.2]

lemma c0_pos : 0 < c0 := by linarith [c0_bounds.1]

lemma coreRadius_bounds : 0.387 < coreRadius ∧ coreRadius < 0.388 := by
  dsimp [coreRadius]
  constructor <;> linarith [rho0_bounds.1,rho0_bounds.2]

lemma coreRadius_pos : 0 < coreRadius := by linarith [coreRadius_bounds.1]

lemma c0_add_coreRadius : c0+coreRadius=1/2 := by
  dsimp [c0,coreRadius]
  ring

lemma aMin_eq_coreRadius_add_half : aMin=coreRadius+1/2 := by
  dsimp [aMin,coreRadius]
  ring

lemma aMin_bounds : 0.887 < aMin ∧ aMin < 0.888 := by
  dsimp [aMin]
  constructor <;> linarith [rho0_bounds.1,rho0_bounds.2]

lemma U0_radicand : Q0-(5/2-rho0)^2=6*rho0-23/4 := by
  nlinarith [rho0_sq]

lemma U0_radicand_pos : 0 < Q0-(5/2-rho0)^2 := by
  rw [U0_radicand]
  linarith [rho0_bounds.1]

lemma U0_upper : U0 < 0.463 := by
  rw [U0,sub_lt_iff_lt_add,Real.sqrt_lt' (by norm_num),U0_radicand]
  linarith [rho0_bounds.2]

/-! ### Decimal ceilings -/

/-- `R0` rounded up. -/
def radiusBound : ℝ := 1.6886
/-- `ρ0` rounded up. -/
def rhoBound : ℝ := 1.11282
/-- `c0` rounded up. -/
def coreUpper : ℝ := 0.11282
/-- `c0` rounded down. -/
def coreLower : ℝ := 0.1128

lemma ceiling_bounds : R0 ≤ radiusBound ∧ rho0 ≤ rhoBound ∧ coreLower ≤ c0 ∧ c0 ≤ coreUpper := by
  dsimp [radiusBound,rhoBound,coreLower,coreUpper]
  exact ⟨R0_bounds.2.le,by linarith [rho0_bounds.2],by linarith [c0_bounds.1],
    by linarith [c0_bounds.2]⟩

namespace Wings

/-- `1/2 - coreUpper` and `1/2 + coreUpper`: the coefficients that the half-width
of a square and the box of the centre of C leave in the separating inequalities
of the wings. -/
def A : ℝ := 0.38718
def B : ℝ := 0.61282

end Wings

end SquaresInCircles.Six
