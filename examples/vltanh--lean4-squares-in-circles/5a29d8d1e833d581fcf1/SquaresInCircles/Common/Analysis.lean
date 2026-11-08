module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# One-variable calculus

A function with a nonnegative derivative increases, and one that increases up
to a point and decreases after it is largest there. A function with a
nonpositive second derivative on an interval is concave, and a concave function
exceeds inside the interval every bound that it exceeds at both ends; concavity
survives an affine change of the argument, and a function on a rectangle that
is concave in each variable is positive once it is positive at the four corners.
A function with second derivative at least `κ` lies above its tangent parabola.
A continuous function that is positive at the left
end of an interval, nonnegative at the right end and somewhere nonpositive has
a leftmost minimum inside; where the function is a sinusoid there, the minimum
is stationary and the sinusoid negative.
-/

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles

/-! ### Monotonicity -/

lemma monoOn_of_hasDeriv_nonneg {l u : ℝ} {f d : ℝ → ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ x ∈ Ioo l u, HasDerivAt f (d x) x)
    (hs : ∀ x ∈ Ioo l u, 0 ≤ d x) : MonotoneOn f (Icc l u) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc l u) hc
    (by simpa only [interior_Icc] using fun x hx => (hd x hx).hasDerivWithinAt)
    (by simpa only [interior_Icc] using hs)

lemma antiOn_of_hasDeriv_nonpos {l u : ℝ} {f d : ℝ → ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ x ∈ Ioo l u, HasDerivAt f (d x) x)
    (hs : ∀ x ∈ Ioo l u, d x ≤ 0) : AntitoneOn f (Icc l u) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l u) hc
    (by simpa only [interior_Icc] using fun x hx => (hd x hx).hasDerivWithinAt)
    (by simpa only [interior_Icc] using hs)

/-- A function that vanishes at `0` and has a nonnegative derivative on `[0, ∞)`
is nonnegative there. -/
lemma nonneg_of_deriv_nonneg (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hzero : f 0 = 0) (hder : ∀ x, 0 ≤ x → 0 ≤ deriv f x)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x :=
  hzero ▸ monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuous.continuousOn
    hf.differentiableOn (fun t ht => hder t (interior_subset ht)) self_mem_Ici hx hx

/-- A function increasing up to `c` and decreasing after it is largest at `c`. -/
lemma le_at_peak {f d : ℝ → ℝ} {l c u x : ℝ}
    (hc : l ≤ c ∧ c ≤ u) (hx : l ≤ x ∧ x ≤ u)
    (hf : Continuous f) (hd : ∀ y, HasDerivAt f (d y) y)
    (hleft : ∀ y ∈ Icc l c, 0 ≤ d y)
    (hright : ∀ y ∈ Icc c u, d y ≤ 0) : f x ≤ f c := by
  rcases le_total x c with hxc | hcx
  · exact monoOn_of_hasDeriv_nonneg hf.continuousOn (fun y _ => hd y)
      (fun y hy => hleft y ⟨hy.1.le,hy.2.le⟩) ⟨hx.1,hxc⟩ ⟨hc.1,le_rfl⟩ hxc
  · exact antiOn_of_hasDeriv_nonpos hf.continuousOn (fun y _ => hd y)
      (fun y hy => hright y ⟨hy.1.le,hy.2.le⟩) ⟨le_rfl,hc.2⟩ ⟨hcx,hx.2⟩ hcx

/-! ### Concavity -/

/-- A function whose second derivative is nonpositive on `[l, u]` is concave
there. -/
lemma concave_of_deriv2 {f f' f'' : ℝ → ℝ} {l u : ℝ}
    (hf : ∀ x ∈ Icc l u, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc l u, HasDerivAt f' (f'' x) x)
    (h : ∀ x ∈ Icc l u, f'' x ≤ 0) : ConcaveOn ℝ (Icc l u) f :=
  concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc l u)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => (hf' x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => h x (interior_subset hx))

/-- A concave function exceeds inside `[l, u]` every bound that it exceeds at
both ends. -/
lemma concave_gt_of_endpoints {f : ℝ → ℝ} {l u x c : ℝ}
    (hf : ConcaveOn ℝ (Icc l u) f) (hx : l ≤ x ∧ x ≤ u) (hl : c < f l) (hu : c < f u) :
    c < f x :=
  (lt_min hl hu).trans_le
    (hf.min_le_of_mem_Icc ⟨le_rfl,hx.1.trans hx.2⟩ ⟨hx.1.trans hx.2,le_rfl⟩ hx)

/-- A concave function that vanishes at `l` and is positive at `u` is positive on
`(l, u]`: it lies above its chord. -/
lemma concave_pos_of_zero_left {f : ℝ → ℝ} {l u x : ℝ}
    (hf : ConcaveOn ℝ (Icc l u) f) (hx : l < x ∧ x ≤ u) (hl : f l = 0) (hu : 0 < f u) :
    0 < f x := by
  have hlu : 0 < u-l := by linarith [hx.1,hx.2]
  have ht : 0 < (x-l)/(u-l) := div_pos (by linarith [hx.1]) hlu
  have ht1 : (x-l)/(u-l) ≤ 1 := (div_le_one hlu).mpr (by linarith [hx.2])
  have h := hf.2 (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
    (sub_nonneg.mpr ht1) ht.le (by ring)
  have hx' : (1-(x-l)/(u-l))•l+((x-l)/(u-l))•u = x := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hx',hl] at h
  simp only [smul_eq_mul,mul_zero,zero_add] at h
  exact (mul_pos ht hu).trans_le h

/-- A function concave on `[L, U]`, composed with an affine map from `[l, u]`
into `[L, U]`, is concave on `[l, u]`. -/
lemma concave_affine_argument {f : ℝ → ℝ} {L U l u a b : ℝ}
    (hf : ConcaveOn ℝ (Icc L U) f) (hmap : ∀ x ∈ Icc l u, a*x+b ∈ Icc L U) :
    ConcaveOn ℝ (Icc l u) (fun x => f (a*x+b)) := by
  refine ⟨convex_Icc l u,?_⟩
  intro x hx y hy r s hr hs hrs
  have h := hf.2 (hmap x hx) (hmap y hy) hr hs hrs
  have hid : a*(r*x+s*y)+b=r*(a*x+b)+s*(a*y+b) := by
    linear_combination -b*hrs
  simpa only [smul_eq_mul,hid] using h

/-- An affine function is concave. -/
lemma affine_concave (a b l u : ℝ) : ConcaveOn ℝ (Icc l u) (fun x : ℝ => a*x+b) := by
  refine ⟨convex_Icc l u,fun x _ y _ p q _ _ hpq => ?_⟩
  simp only [smul_eq_mul]
  have he : p*(a*x+b)+q*(a*y+b)=a*(p*x+q*y)+b*(p+q) := by ring
  rw [he,hpq,mul_one]

/-- A function on `[l, u] × [L, U]`, concave in the first variable and concave
in the second on the edges `x = l` and `x = u`, is positive if it is positive
at the four corners. -/
lemma positive_on_separately_concave_rectangle {f : ℝ → ℝ → ℝ} {l u L U x y : ℝ}
    (hx : l ≤ x ∧ x ≤ u) (hy : L ≤ y ∧ y ≤ U)
    (hfirst : ∀ t ∈ Icc L U, ConcaveOn ℝ (Icc l u) (fun z => f z t))
    (hleft : ConcaveOn ℝ (Icc L U) (f l))
    (hright : ConcaveOn ℝ (Icc L U) (f u))
    (hll : 0 < f l L) (hlu : 0 < f l U) (hul : 0 < f u L) (huu : 0 < f u U) : 0 < f x y :=
  concave_gt_of_endpoints (f := fun z => f z y) (hfirst y hy) hx
    (concave_gt_of_endpoints (f := f l) hleft hy hll hlu)
    (concave_gt_of_endpoints (f := f u) hright hy hul huu)

/-- A function on `[l, u]` with nonpositive second derivative is positive if it
is positive at both ends. -/
lemma positive_of_second_nonpos {l u x : ℝ} {f d dd : ℝ → ℝ} (hx : x ∈ Icc l u)
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, dd y ≤ 0)
    (hl : 0 < f l) (hu : 0 < f u) : 0 < f x :=
  concave_gt_of_endpoints (concave_of_deriv2 hd hdd hm) hx hl hu

/-- A function on `[l, u]` with second derivative at least `κ` lies above its
tangent parabola of curvature `κ` at any point. -/
lemma curvature_tangent {l u x t κ : ℝ} {f d dd : ℝ → ℝ}
    (hx : x ∈ Icc l u) (ht : t ∈ Icc l u)
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, κ ≤ dd y) : f t+d t*(x-t)+κ/2*(x-t)^2 ≤ f x := by
  let g : ℝ → ℝ := fun y => f y-κ/2*y^2
  have hg (y : ℝ) (hy : y ∈ Icc l u) : HasDerivAt g (d y-κ*y) y := by
    convert (hd y hy).sub (((hasDerivAt_id y).pow 2).const_mul (κ/2)) using 1
    · rfl
    · dsimp; ring
  have hc : ConvexOn ℝ (Icc l u) g := convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc l u)
    (fun y hy => (hg y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hg y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => ((hdd y (interior_subset hy)).sub
      ((hasDerivAt_id y).const_mul κ)).hasDerivWithinAt)
    (fun y hy => by linarith [hm y (interior_subset hy)])
  have htan : g t+(d t-κ*t)*(x-t) ≤ g x := by
    rcases lt_trichotomy t x with h | rfl | h
    · have hs := hc.le_slope_of_hasDerivAt ht hx h (hg t ht)
      rw [slope_def_field,le_div_iff₀ (sub_pos.2 h)] at hs
      linarith
    · simp
    · have hs := hc.slope_le_of_hasDerivAt hx ht h (hg t ht)
      rw [slope_def_field,div_le_iff₀ (sub_pos.2 h)] at hs
      linarith
  dsimp [g] at htan
  linarith

/-- A function on `[l, u]` with second derivative at least `κ > 0` is positive
if at one point its slope `d` and value `f` satisfy `d² < 2κf`. -/
lemma positive_of_curvature {l u x t κ : ℝ} {f d dd : ℝ → ℝ} (hκ : 0 < κ)
    (hx : x ∈ Icc l u) (ht : t ∈ Icc l u)
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, κ ≤ dd y) (hval : d t^2 < 2*κ*f t) : 0 < f x := by
  nlinarith [curvature_tangent hx ht hd hdd hm,sq_nonneg (κ*(x-t)+d t)]

/-! ### Leftmost minima -/

/-- A nonpositive value after a positive left endpoint and before a nonnegative
right endpoint has an interior leftmost minimizer. Every earlier point has
strictly larger value. -/
lemma leftmost_nonpositive_minimum {f : ℝ → ℝ} {l u y : ℝ}
    (hf : Continuous f) (hy : y∈Ico l u) (hbad : f y≤0)
    (hl : 0<f l) (hu : 0≤f u) :
    ∃ x, x∈Ioo l u ∧ f x≤0 ∧
      (∀z∈Icc l u,f x≤f z) ∧
      (∀z∈Icc l u,z<x → f x<f z) := by
  have hy' : y∈Icc l u := Ico_subset_Icc_self hy
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨y,hy'⟩ hf.continuousOn
  let K : Set ℝ := Icc l u ∩ {x | f x=f m}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_eq hf continuous_const)
  have hn : K.Nonempty := ⟨m,hm,rfl⟩
  obtain ⟨x,hx,hleft⟩ := hK.exists_isMinOn hn continuous_id.continuousOn
  have hxval : f x=f m := hx.2
  have hym : f m≤f y := hmin hy'
  have hxnon : f x≤0 := hxval.le.trans (hym.trans hbad)
  have hxl : l<x := by
    have hle := hx.1.1
    by_contra hn
    have he : x=l := le_antisymm (le_of_not_gt hn) hle
    rw [he] at hxnon
    linarith
  have hxu : x<u := by
    refine lt_of_le_of_ne hx.1.2 fun he => ?_
    rw [he] at hxval
    have hyK : y∈K := ⟨hy',le_antisymm (by linarith) hym⟩
    have hxy : x≤y := hleft hyK
    linarith [hy.2]
  refine ⟨x,⟨hxl,hxu⟩,hxnon,?_,?_⟩
  · intro z hz
    rw [hxval]
    exact hmin hz
  · intro z hz hzx
    have hle : f x≤f z := hxval.le.trans (hmin hz)
    by_contra hn
    have he : f z=f m := by linarith
    have hk : z∈K := ⟨hz,he⟩
    have hh : x≤z := hleft hk
    linarith

lemma absolute_sign_eventually {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ}
    (hx : f x≠0) :
    ∀ᶠ y in 𝓝 x, |f y|=(if 0<f x then (1:ℝ) else -1)*f y := by
  by_cases hpos : 0<f x
  · filter_upwards [(hf.tendsto x).eventually (lt_mem_nhds hpos)] with y hy
    simp only [ite_eq_left hpos,one_mul,abs_of_pos hy]
  · have hneg : f x<0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
    filter_upwards [(hf.tendsto x).eventually (gt_mem_nhds hneg)] with y hy
    simp only [ite_eq_right hpos,neg_one_mul,abs_of_neg hy]

lemma sinusoid_leftmost_minimum {f : ℝ → ℝ} {l u x c A B Z : ℝ}
    (hx : x∈Ioo l u)
    (hmin : ∀y∈Icc l u,f x≤f y)
    (hleft : ∀y∈Icc l u,y<x → f x<f y)
    (hevent : f =ᶠ[𝓝 x] (fun y => c+A*Real.cos (Z-y)+B*Real.sin (Z-y))) :
    A*Real.sin (Z-x)-B*Real.cos (Z-x)=0 ∧
      A*Real.cos (Z-x)+B*Real.sin (Z-x)<0 := by
  let g : ℝ → ℝ := fun y => c+A*Real.cos (Z-y)+B*Real.sin (Z-y)
  have he0 : f x=g x := hevent.eq_of_nhds
  have hlocal : IsLocalMin f x := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hmin y ⟨hy.1.le,hy.2.le⟩
  have harg : HasDerivAt (fun y : ℝ => Z-y) (-1) x := (hasDerivAt_id' x).const_sub Z
  have hg : HasDerivAt g (A*Real.sin (Z-x)-B*Real.cos (Z-x)) x := by
    convert (((harg.cos.const_mul A).const_add c).add (harg.sin.const_mul B)) using 1
    ring
  have hf := hg.congr_of_eventuallyEq hevent
  have hstationary : A*Real.sin (Z-x)-B*Real.cos (Z-x)=0 :=
    hlocal.hasDerivAt_eq_zero hf
  refine ⟨hstationary,?_⟩
  by_contra hn
  have hnon : 0≤A*Real.cos (Z-x)+B*Real.sin (Z-x) := le_of_not_gt hn
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hevent
  let e := min (r/2) ((x-l)/2)
  have hepos : 0<e := lt_min (by positivity) (by linarith [hx.1])
  have her : e<r := (min_le_left _ _).trans_lt (by linarith)
  have hex : e≤(x-l)/2 := min_le_right _ _
  have hy : x-e∈Icc l u := ⟨by linarith,by linarith [hx.2]⟩
  have hyl : x-e<x := by linarith
  have hye : f (x-e)=g (x-e) := hball
    (by rw [Metric.mem_ball,Real.dist_eq,show (x-e)-x=-e by ring,abs_neg,abs_of_pos hepos]; exact her)
  have hstrict := hleft (x-e) hy hyl
  rw [he0,hye] at hstrict
  have hid : g (x-e)-g x=
      (A*Real.cos (Z-x)+B*Real.sin (Z-x))*(Real.cos e-1) := by
    have he : Z-(x-e)=(Z-x)+e := by ring
    dsimp [g]
    rw [he,Real.cos_add,Real.sin_add]
    linear_combination (-Real.sin e)*hstationary
  have hprod := mul_nonpos_of_nonneg_of_nonpos hnon
    (sub_nonpos.mpr (Real.cos_le_one e))
  linarith

end SquaresInCircles
