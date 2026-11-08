module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.vf15e846202ba.RequestProject.Euler.ScalarLemmas
/-!
# The weighted Gronwall estimate for the outer vortices (Theorem `ca:thm:envelope`)

Formalization of Theorem `ca:thm:envelope` of Section `part:ca`: for the weighted mild
system of Definition `ca:def:system` (diagonal propagators bounded by `M e^{σ a_j (t-s)}`,
`a_j = b^{k-j}`, interaction coefficients `B^±`, local terms `n_j`, forcing `f_j` and remaining
sources `r_j`), the weighted maximum `Z(t) = max_{j<k} h^{-(k-j)} ‖x_j(t)‖`, `h = C₀ρ⁶`, obeys

`Z(t) ≤ M e^{νt} Z(0) + (M C_int / C₀) ∫₀ᵗ e^{ν(t-s)} E(s) ds + M ∫₀ᵗ e^{ν(t-s)} 𝓡(s) ds`

with `ν = bσ + M C_int b (1/(C₀-1) + ζ_ρ/(1-ζ_ρ) + d_a + R⁸)` (`nuExp`), `ζ_ρ = C₀ρ⁸`.

We also prove the version of the scalar convolution inequality (`ca:lem:gronwall`) on a finite
interval `[0,T]`, which the proof uses.
-/
@[expose] public section
open Filter Topology Set MeasureTheory Real
namespace Euler2D
/-! ### The scalar convolution inequality on a finite interval -/
/-- Lemma `ca:lem:gronwall` on `[0,T]`, for globally continuous data. -/
theorem scalar_convolution_gronwall_Icc {Z g : ℝ → ℝ} {T : ℝ} (hZ : Continuous Z)
    (hg : Continuous g) {A c d : ℝ} (hd : 0 ≤ d)
    (h : ∀ t ∈ Icc 0 T, Z t ≤ A * exp (c * t) +
      ∫ s in (0)..t, exp (c * (t - s)) * (d * Z s + g s))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Z t ≤ A * exp ((c + d) * t) + ∫ s in (0)..t, exp ((c + d) * (t - s)) * g s := by
  set z : ℝ → ℝ := fun s => exp (-c * s) * Z s
  set f : ℝ → ℝ := fun s => exp (-c * s) * g s
  have hz : Continuous z := by fun_prop
  have hf : Continuous f := by fun_prop
  set v : ℝ → ℝ := fun t => A + ∫ s in (0)..t, (d * z s + f s)
  have hzv : ∀ t ∈ Icc 0 T, z t ≤ v t := by
    intro t ht
    have h1 := h t ht
    have h2 : exp (-c * t) * (∫ s in (0)..t, exp (c * (t - s)) * (d * Z s + g s)) =
        ∫ s in (0)..t, (d * z s + f s) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [z, f]
      have : exp (-c * t) * exp (c * (t - s)) = exp (-c * s) := by
        rw [← exp_add]; ring_nf
      rw [← mul_assoc, this]; ring
    have h3 : exp (-c * t) * (A * exp (c * t)) = A := by
      rw [mul_left_comm, ← exp_add]; simp
    have hpos : 0 < exp (-c * t) := exp_pos _
    calc z t = exp (-c * t) * Z t := rfl
      _ ≤ exp (-c * t) * (A * exp (c * t) + ∫ s in (0)..t, exp (c * (t - s)) * (d * Z s + g s)) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = v t := by rw [mul_add, h3, h2]
  have hv : ∀ t, HasDerivAt v (d * z t + f t) t := fun t => by
    have := intervalIntegral.integral_hasDerivAt_right ((hz.const_smul d).add hf |>.intervalIntegrable 0 t)
      (((hz.const_smul d).add hf).stronglyMeasurableAtFilter _ _) ((hz.const_smul d).add hf).continuousAt
    simpa [v] using this.const_add A
  set W : ℝ → ℝ := fun t => exp (-d * t) * v t - ∫ s in (0)..t, exp (-d * s) * f s
  have hW : ∀ t, HasDerivAt W (exp (-d * t) * (d * z t + f t) + (-d * exp (-d * t)) * v t
      - exp (-d * t) * f t) t := fun t => by
    have he : HasDerivAt (fun t => exp (-d * t)) (-d * exp (-d * t)) t := by
      have := ((hasDerivAt_id t).const_mul (-d)).exp
      simpa [mul_comm] using this
    have hI := intervalIntegral.integral_hasDerivAt_right
      ((by fun_prop : Continuous fun s => exp (-d * s) * f s).intervalIntegrable 0 t)
      ((by fun_prop : Continuous fun s => exp (-d * s) * f s).stronglyMeasurableAtFilter _ _)
      (by fun_prop : Continuous fun s => exp (-d * s) * f s).continuousAt
    have := (he.mul (hv t)).sub hI
    convert this using 1; ring
  have hWanti : AntitoneOn W (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact (continuous_iff_continuousAt.2 fun t => (hW t).continuousAt).continuousOn
    · exact fun t _ => (hW t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hW t).deriv]
      have := hzv t (Ioo_subset_Icc_self ht)
      have hpos : 0 < exp (-d * t) := exp_pos _
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hd hpos.le)]
  have hW0 : W 0 = A := by simp [W, v]
  have hWt : W t ≤ A := hW0 ▸ hWanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  -- `v t ≤ A e^{dt} + ∫ e^{d(t-s)} f`
  have hvt : v t ≤ A * exp (d * t) + ∫ s in (0)..t, exp (d * (t - s)) * f s := by
    have e1 : (∫ s in (0)..t, exp (d * (t - s)) * f s) =
        exp (d * t) * ∫ s in (0)..t, exp (-d * s) * f s := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [show d * (t - s) = d * t + -d * s by ring, exp_add]; ring
    have hWt' : exp (-d * t) * v t ≤ A + ∫ s in (0)..t, exp (-d * s) * f s := by
      simp only [W] at hWt; linarith
    have := mul_le_mul_of_nonneg_left hWt' (exp_pos (d * t)).le
    rw [← mul_assoc, ← exp_add, show d * t + -d * t = 0 by ring, exp_zero, one_mul] at this
    rw [e1]; linarith
  have hZt : Z t = exp (c * t) * z t := by
    simp only [z]; rw [← mul_assoc, ← exp_add]; simp
  have e2 : (∫ s in (0)..t, exp ((c + d) * (t - s)) * g s) =
      exp (c * t) * ∫ s in (0)..t, exp (d * (t - s)) * f s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [f]
    rw [show exp (c * t) * (exp (d * (t - s)) * (exp (-c * s) * g s)) =
      (exp (c * t) * exp (d * (t - s)) * exp (-c * s)) * g s by ring, ← exp_add, ← exp_add]
    ring_nf
  rw [hZt, e2, show (c + d) * t = c * t + d * t by ring, exp_add]
  have := mul_le_mul_of_nonneg_left ((hzv t ht).trans hvt) (exp_pos (c * t)).le
  linarith
/-- Lemma `ca:lem:gronwall` on `[0,T]`, for data continuous on `[0,T]`. -/
theorem scalar_convolution_gronwall_on {Z g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hZ : ContinuousOn Z (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T)) {A c d : ℝ} (hd : 0 ≤ d)
    (h : ∀ t ∈ Icc 0 T, Z t ≤ A * exp (c * t) +
      ∫ s in (0)..t, exp (c * (t - s)) * (d * Z s + g s))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Z t ≤ A * exp ((c + d) * t) + ∫ s in (0)..t, exp ((c + d) * (t - s)) * g s := by
  set Z' : ℝ → ℝ := IccExtend hT (fun s : Icc 0 T => Z s) with hZ'
  set g' : ℝ → ℝ := IccExtend hT (fun s : Icc 0 T => g s) with hg'
  have hZ'c : Continuous Z' := (ContinuousOn.restrict hZ).Icc_extend'
  have hg'c : Continuous g' := (ContinuousOn.restrict hg).Icc_extend'
  have eZ : ∀ s ∈ Icc 0 T, Z' s = Z s := fun s hs => by simp [hZ', IccExtend_of_mem _ _ hs]
  have eg : ∀ s ∈ Icc 0 T, g' s = g s := fun s hs => by simp [hg', IccExtend_of_mem _ _ hs]
  have hsub : ∀ t ∈ Icc 0 T, ∀ s ∈ uIcc 0 t, s ∈ Icc 0 T := fun t ht s hs => by
    rw [uIcc_of_le ht.1] at hs; exact ⟨hs.1, hs.2.trans ht.2⟩
  have h' : ∀ t ∈ Icc 0 T, Z' t ≤ A * exp (c * t) +
      ∫ s in (0)..t, exp (c * (t - s)) * (d * Z' s + g' s) := by
    intro t ht
    rw [eZ t ht]
    convert h t ht using 2
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [eZ s (hsub t ht s hs), eg s (hsub t ht s hs)]
  have := scalar_convolution_gronwall_Icc hZ'c hg'c hd h' ht
  rw [eZ t ht] at this
  convert this using 2
  refine intervalIntegral.integral_congr fun s hs => ?_
  simp only [eg s (hsub t ht s hs)]
/-! ### The weighted system -/
lemma sum_pow_le_of_injOn {ι : Type*} (s : Finset ι) (φ : ι → ℕ) (hφ : Set.InjOn φ s)
    (hpos : ∀ i ∈ s, 1 ≤ φ i) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑ i ∈ s, q ^ φ i ≤ q / (1 - q) := by
  classical
  set N : ℕ := (s.image φ).sup id + 1
  have hsub : s.image φ ⊆ Finset.Ico 1 N := by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    refine Finset.mem_Ico.mpr ⟨hpos a ha, ?_⟩
    have : φ a ≤ (s.image φ).sup id := Finset.le_sup (f := id) hi
    omega
  calc ∑ i ∈ s, q ^ φ i = ∑ i ∈ s.image φ, q ^ i := (Finset.sum_image hφ).symm
    _ ≤ ∑ i ∈ Finset.Ico 1 N, q ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => pow_nonneg hq0 i
    _ ≤ q ^ 1 / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 hq1
    _ = q / (1 - q) := by rw [pow_one]
lemma rho_pow_down (C₀ ρ : ℝ) (a c : ℕ) :
    ρ ^ (2 * c) * (C₀ * ρ ^ 6) ^ (a + c) = (C₀ * ρ ^ 6) ^ a * (C₀ * ρ ^ 8) ^ c := by
  rw [pow_add, pow_mul, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  ring_nf
end Euler2D
end
