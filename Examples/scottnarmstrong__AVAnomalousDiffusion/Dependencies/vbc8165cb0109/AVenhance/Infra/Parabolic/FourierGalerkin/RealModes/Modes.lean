-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Frequency
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
attribute [local instance] realModesMeasureSpace realModesMeasureIsAddHaar realModesProbability
namespace AVenhance.Infra.Parabolic.FourierGalerkin
theorem Modes.pairFrequency_injective {p q : ℤ × ℤ}
    (h : pairFrequency p = pairFrequency q) : p = q := by
  have h₀ := congrFun h (0 : Fin 2)
  have h₁ := congrFun h (1 : Fin 2)
  simp [pairFrequency] at h₀ h₁
  exact Prod.ext h₀ h₁
theorem Modes.integral_mFourier (k : Fin 2 → ℤ) :
    ∫ x : Torus, UnitAddTorus.mFourier k x = if k = 0 then (1 : ℂ) else 0 := by
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier))
    (0 : Fin 2 → ℤ) k
  rw [ContinuousMap.inner_toLp] at h
  simpa [UnitAddTorus.mFourier_zero, eq_comm] using h
theorem Modes.mFourierCoeff_mFourier (k l : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier l) k =
      if k = l then (1 : ℂ) else 0 := by
  change ∫ x : Torus, UnitAddTorus.mFourier (-k) x *
      UnitAddTorus.mFourier l x = _
  have hprod : (fun x : Torus => UnitAddTorus.mFourier (-k) x *
      UnitAddTorus.mFourier l x) = fun x => UnitAddTorus.mFourier (-k + l) x := by
    funext x
    rw [← UnitAddTorus.mFourier_add]
  rw [hprod, Modes.integral_mFourier]
  simp [add_eq_zero_iff_eq_neg]
/-- A Fourier character in the cutoff box is exactly fixed by the finite Fourier sum. -/
theorem complexFourierPartialSumComplex_mFourier {N : ℕ} (k : Fin 2 → ℤ)
    (hk : frequencyPair k ∈ symmetricFrequencyBox N) (x : Torus) :
    complexFourierPartialSumComplex N (UnitAddTorus.mFourier k) x =
      UnitAddTorus.mFourier k x := by
  classical
  rw [complexFourierPartialSumComplex, Finset.sum_eq_single_of_mem
    (frequencyPair k) hk]
  · simp [Modes.mFourierCoeff_mFourier, pairFrequency_frequencyPair]
  · intro p hp hne
    have hfreq : pairFrequency p ≠ k := by
      intro heq
      apply hne
      apply Modes.pairFrequency_injective
      calc
        pairFrequency p = k := heq
        _ = pairFrequency (frequencyPair k) := (pairFrequency_frequencyPair k).symm
    simp [Modes.mFourierCoeff_mFourier, hfreq]
theorem Modes.integrable_mFourier_mul_of_continuous {f : Torus → ℂ}
    (hf : Continuous f) (k : Fin 2 → ℤ) :
    Integrable (fun x : Torus => UnitAddTorus.mFourier (-k) x * f x) volume := by
  exact ((UnitAddTorus.mFourier (-k)).continuous.mul hf)
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
theorem Modes.mFourierCoeff_add_of_continuous {f g : Torus → ℂ}
    (hf : Continuous f) (hg : Continuous g) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x => f x + g x) k =
      UnitAddTorus.mFourierCoeff f k + UnitAddTorus.mFourierCoeff g k := by
  change ∫ x : Torus, UnitAddTorus.mFourier (-k) x * (f x + g x) = _
  have hpoint : (fun x : Torus => UnitAddTorus.mFourier (-k) x * (f x + g x)) =
      fun x => UnitAddTorus.mFourier (-k) x * f x +
        UnitAddTorus.mFourier (-k) x * g x := by
    funext x
    ring
  rw [hpoint, integral_add (Modes.integrable_mFourier_mul_of_continuous hf k)
    (Modes.integrable_mFourier_mul_of_continuous hg k)]
  rfl
theorem Modes.mFourierCoeff_const_mul {f : Torus → ℂ}
    (c : ℂ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x => c * f x) k =
      c * UnitAddTorus.mFourierCoeff f k := by
  change ∫ x : Torus, UnitAddTorus.mFourier (-k) x * (c * f x) = _
  have hpoint : (fun x : Torus => UnitAddTorus.mFourier (-k) x * (c * f x)) =
      fun x => c * (UnitAddTorus.mFourier (-k) x * f x) := by
    funext x
    ring
  rw [hpoint, integral_const_mul]
  rfl
theorem complexFourierPartialSumComplex_add {N : ℕ} {f g : Torus → ℂ}
    (hf : Continuous f) (hg : Continuous g) (x : Torus) :
    complexFourierPartialSumComplex N (fun y => f y + g y) x =
      complexFourierPartialSumComplex N f x +
        complexFourierPartialSumComplex N g x := by
  classical
  unfold complexFourierPartialSumComplex
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Modes.mFourierCoeff_add_of_continuous hf hg]
  ring
theorem complexFourierPartialSumComplex_const_mul {N : ℕ} {f : Torus → ℂ}
    (c : ℂ) (x : Torus) :
    complexFourierPartialSumComplex N (fun y => c * f y) x =
      c * complexFourierPartialSumComplex N f x := by
  classical
  unfold complexFourierPartialSumComplex
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Modes.mFourierCoeff_const_mul c]
  ring
theorem Modes.ofReal_sqrtTwo_mul_re (z : ℂ) :
    ((Real.sqrt 2 * z.re : ℝ) : ℂ) =
      (Real.sqrt 2 / 2 : ℝ) * (z + star z) := by
  apply Complex.ext
  · simp [Complex.mul_re]
    ring
  · simp [Complex.mul_im]
theorem Modes.ofReal_sqrtTwo_mul_im (z : ℂ) :
    ((Real.sqrt 2 * z.im : ℝ) : ℂ) =
      (Real.sqrt 2 / 2 : ℝ) * (-Complex.I) * (z - star z) := by
  apply Complex.ext
  · simp [Complex.mul_re]
    ring
  · simp [Complex.mul_im]
theorem Modes.mFourier_star_at (k : Fin 2 → ℤ) (x : Torus) :
    star (UnitAddTorus.mFourier k x) = UnitAddTorus.mFourier (-k) x := by
  rw [Complex.star_def]
  exact (UnitAddTorus.mFourier_neg (n := k) (x := x)).symm
def representativeFrequency {N : ℕ}
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) : Fin 2 → ℤ :=
  pairFrequency p.1
theorem representativeFrequency_mem_box {N : ℕ}
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    frequencyPair (representativeFrequency p) ∈ symmetricFrequencyBox N := by
  have hp := (mem_positiveFrequencyRepresentatives p.2).1
  have hpair : frequencyPair (pairFrequency p.1) = p.1 := by
    rcases p.1 with ⟨a, b⟩
    simp [frequencyPair, pairFrequency]
  simpa [representativeFrequency, hpair] using hp
theorem representativeFrequency_injective {N : ℕ}
    {p q : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}}
    (h : representativeFrequency p = representativeFrequency q) : p = q := by
  apply Subtype.ext
  exact Modes.pairFrequency_injective h
theorem representativeFrequency_ne_neg {N : ℕ}
    (p q : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    representativeFrequency p ≠ -representativeFrequency q := by
  intro h
  have hpq : p.1 = -q.1 := by
    apply Modes.pairFrequency_injective
    simpa [representativeFrequency, pairFrequency_neg] using h
  have hneg : -q.1 ∈ positiveFrequencyRepresentatives N := by rw [← hpq]; exact p.2
  exact positiveFrequencyRepresentatives_neg_not q.2 hneg
/-- The finite real Fourier index: one constant mode and a cosine/sine pair for each representative.
`Bool.false` selects cosine and `Bool.true` selects sine. -/
abbrev RealFourierIndex (N : ℕ) :=
  Option ({p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N} × Bool)
noncomputable instance realFourierIndexFintype (N : ℕ) : Fintype (RealFourierIndex N) :=
  by
    dsimp [RealFourierIndex]
    infer_instance
/-- Real trigonometric modes on the unit torus, normalized so nonconstant modes have norm one. -/
def realFourierMode (N : ℕ) (a : RealFourierIndex N) (x : Torus) : ℝ :=
  match a with
  | none => 1
  | some (p, isSine) =>
    let z := UnitAddTorus.mFourier (representativeFrequency p) x
    if isSine then Real.sqrt 2 * z.im else Real.sqrt 2 * z.re
/-- Complexification of a cosine mode as the two characters at opposite frequencies. -/
theorem realFourierMode_cos_complexExpansion (N : ℕ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) (x : Torus) :
    (realFourierMode N (some (p, false)) x : ℂ) =
      (Real.sqrt 2 / 2 : ℝ) *
        (UnitAddTorus.mFourier (representativeFrequency p) x +
          UnitAddTorus.mFourier (-representativeFrequency p) x) := by
  have h := Modes.ofReal_sqrtTwo_mul_re
    (UnitAddTorus.mFourier (representativeFrequency p) x)
  simpa only [realFourierMode, Bool.false_eq_true, ↓reduceIte, Modes.mFourier_star_at] using h
/-- Complexification of a sine mode as the two characters at opposite frequencies. -/
theorem realFourierMode_sin_complexExpansion (N : ℕ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) (x : Torus) :
    (realFourierMode N (some (p, true)) x : ℂ) =
      (Real.sqrt 2 / 2 : ℝ) * (-Complex.I) *
        (UnitAddTorus.mFourier (representativeFrequency p) x -
          UnitAddTorus.mFourier (-representativeFrequency p) x) := by
  have h := Modes.ofReal_sqrtTwo_mul_im
    (UnitAddTorus.mFourier (representativeFrequency p) x)
  simpa only [realFourierMode, ↓reduceIte, Modes.mFourier_star_at] using h
/-- Each real trigonometric mode is continuous on the quotient torus. -/
theorem realFourierMode_continuous (N : ℕ) (a : RealFourierIndex N) :
    Continuous (realFourierMode N a) := by
  cases a with
  | none => exact continuous_const
  | some q =>
    rcases q with ⟨p, isSine⟩
    have hz : Continuous (UnitAddTorus.mFourier (representativeFrequency p)) :=
      (UnitAddTorus.mFourier (representativeFrequency p)).continuous
    cases isSine
    · change Continuous (fun x => Real.sqrt 2 *
        (UnitAddTorus.mFourier (representativeFrequency p) x).re)
      exact continuous_const.mul (Complex.continuous_re.comp hz)
    · change Continuous (fun x => Real.sqrt 2 *
        (UnitAddTorus.mFourier (representativeFrequency p) x).im)
      exact continuous_const.mul (Complex.continuous_im.comp hz)
/-- The corresponding smooth periodic function on Euclidean representatives. -/
def realFourierModeAmbient (N : ℕ) (a : RealFourierIndex N) (x : Homogenization.Vec 2) : ℝ :=
  match a with
  | none => 1
  | some (p, isSine) =>
    let z := AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p) x
    if isSine then Real.sqrt 2 * z.im else Real.sqrt 2 * z.re
theorem representativeFrequency_ne_zero {N : ℕ}
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    representativeFrequency p ≠ 0 := by
  intro hz
  have hzero : pairFrequency (0, 0) = 0 := by
    funext i
    fin_cases i <;> simp [pairFrequency]
  have hp : pairFrequency p.1 = pairFrequency (0, 0) := by
    calc
      pairFrequency p.1 = 0 := hz
      _ = pairFrequency (0, 0) := hzero.symm
  have hp0 : p.1 = (0, 0) := Modes.pairFrequency_injective hp
  exact positiveFrequencyPair_ne_zero
    (mem_positiveFrequencyRepresentatives p.2).2 hp0
theorem realFourierMode_eq_periodicToTorus (N : ℕ) (a : RealFourierIndex N) :
    realFourierMode N a =
      AVenhance.Infra.Torus.periodicToTorus (realFourierModeAmbient N a) := by
  funext x
  cases a with
  | none => rfl
  | some q =>
    rcases q with ⟨p, isSine⟩
    simp only [realFourierMode, realFourierModeAmbient,
      AVenhance.Infra.Torus.periodicToTorus,
      AVenhance.Infra.Torus.torusCharacter]
    rw [neg_neg]
    rw [AVenhance.Infra.Torus.toUnitTorus_unitTorusRepresentative]
/-- The Euclidean real modes are smooth, including every derivative order. -/
theorem realFourierModeAmbient_contDiff (N : ℕ) (a : RealFourierIndex N) :
    ContDiff ℝ ⊤ (realFourierModeAmbient N a) := by
  cases a with
  | none => exact contDiff_const
  | some q =>
    rcases q with ⟨p, isSine⟩
    let χ := AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p)
    have hχ : ContDiff ℝ ⊤ χ :=
      AVenhance.Infra.Torus.torusCharacter_contDiff (-representativeFrequency p)
    have hre : ContDiff ℝ ⊤ (fun x => (χ x).re) := by
      convert Complex.reCLM.contDiff.comp hχ using 1
      funext x
      exact Complex.reCLM_apply (χ x)
    have him : ContDiff ℝ ⊤ (fun x => (χ x).im) := by
      convert Complex.imCLM.contDiff.comp hχ using 1
      funext x
      exact Complex.imCLM_apply (χ x)
    cases isSine
    · change ContDiff ℝ ⊤ (fun x => Real.sqrt 2 * (χ x).re)
      exact contDiff_const.mul hre
    · change ContDiff ℝ ⊤ (fun x => Real.sqrt 2 * (χ x).im)
      exact contDiff_const.mul him
/-- The Euclidean real modes are periodic in the lattice convention. -/
theorem realFourierModeAmbient_periodic (N : ℕ) (a : RealFourierIndex N) :
    AVenhance.IsZ2Periodic (realFourierModeAmbient N a) := by
  cases a with
  | none => intro k x; rfl
  | some q =>
    rcases q with ⟨p, isSine⟩
    intro k x
    have hχ := AVenhance.Infra.Torus.torusCharacter_periodic
      (-representativeFrequency p) k x
    have hshift : AVenhance.latticeShift k = AVenhance.Infra.Torus.intVector k := rfl
    cases isSine
    · change Real.sqrt 2 *
        (AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p)
          (x + AVenhance.latticeShift k)).re =
        Real.sqrt 2 *
          (AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p) x).re
      rw [hshift, hχ]
    · change Real.sqrt 2 *
        (AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p)
          (x + AVenhance.latticeShift k)).im =
        Real.sqrt 2 *
          (AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p) x).im
      rw [hshift, hχ]
theorem realFourierMode_cos_fourierCoeff (N : ℕ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N})
    (l : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun y => (realFourierMode N (some (p, false)) y : ℂ)) l =
      (Real.sqrt 2 / 2 : ℝ) * (if l = representativeFrequency p then 1 else 0) +
        (Real.sqrt 2 / 2 : ℝ) * (if l = -representativeFrequency p then 1 else 0) := by
  let d : ℂ := (Real.sqrt 2 / 2 : ℝ)
  let k := representativeFrequency p
  have hfun : (fun y => (realFourierMode N (some (p, false)) y : ℂ)) =
      fun y => d * UnitAddTorus.mFourier k y + d * UnitAddTorus.mFourier (-k) y := by
    funext y
    calc
      _ = d * (UnitAddTorus.mFourier (representativeFrequency p) y +
          UnitAddTorus.mFourier (-representativeFrequency p) y) := by
        simpa [d] using realFourierMode_cos_complexExpansion N p y
      _ = d * UnitAddTorus.mFourier k y + d * UnitAddTorus.mFourier (-k) y := by
        simp [k, mul_add]
  have hlin := Modes.mFourierCoeff_add_of_continuous
    (f := fun y => d * UnitAddTorus.mFourier k y)
    (g := fun y => d * UnitAddTorus.mFourier (-k) y)
    (continuous_const.mul (UnitAddTorus.mFourier k).continuous)
    (continuous_const.mul (UnitAddTorus.mFourier (-k)).continuous) l
  calc
    _ = UnitAddTorus.mFourierCoeff
        (fun y => d * UnitAddTorus.mFourier k y +
          d * UnitAddTorus.mFourier (-k) y) l := by rw [hfun]
    _ = UnitAddTorus.mFourierCoeff (fun y => d * UnitAddTorus.mFourier k y) l +
        UnitAddTorus.mFourierCoeff (fun y => d * UnitAddTorus.mFourier (-k) y) l := hlin
    _ = d * (if l = k then 1 else 0) + d * (if l = -k then 1 else 0) := by
      rw [Modes.mFourierCoeff_const_mul, Modes.mFourierCoeff_mFourier l k,
        Modes.mFourierCoeff_const_mul, Modes.mFourierCoeff_mFourier l (-k)]
    _ = _ := by simp [d, k]
/-- Complex Fourier coefficients of a real sine mode are supported on its two opposite
characters, with the imaginary signs fixed by the Fourier convention. -/
theorem realFourierMode_sin_fourierCoeff (N : ℕ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N})
    (l : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun y => (realFourierMode N (some (p, true)) y : ℂ)) l =
      ((Real.sqrt 2 / 2 : ℝ) * (-Complex.I)) *
          (if l = representativeFrequency p then 1 else 0) -
        ((Real.sqrt 2 / 2 : ℝ) * (-Complex.I)) *
          (if l = -representativeFrequency p then 1 else 0) := by
  let d : ℂ := (Real.sqrt 2 / 2 : ℝ) * (-Complex.I)
  let k := representativeFrequency p
  have hfun : (fun y => (realFourierMode N (some (p, true)) y : ℂ)) =
      fun y => d * UnitAddTorus.mFourier k y + (-d) * UnitAddTorus.mFourier (-k) y := by
    funext y
    calc
      _ = d * (UnitAddTorus.mFourier (representativeFrequency p) y -
          UnitAddTorus.mFourier (-representativeFrequency p) y) := by
        simpa [d] using realFourierMode_sin_complexExpansion N p y
      _ = d * UnitAddTorus.mFourier k y + (-d) * UnitAddTorus.mFourier (-k) y := by
        simp [k]
        ring
  have hlin := Modes.mFourierCoeff_add_of_continuous
    (f := fun y => d * UnitAddTorus.mFourier k y)
    (g := fun y => (-d) * UnitAddTorus.mFourier (-k) y)
    (continuous_const.mul (UnitAddTorus.mFourier k).continuous)
    (continuous_const.mul (UnitAddTorus.mFourier (-k)).continuous) l
  calc
    _ = UnitAddTorus.mFourierCoeff
        (fun y => d * UnitAddTorus.mFourier k y +
          (-d) * UnitAddTorus.mFourier (-k) y) l := by rw [hfun]
    _ = UnitAddTorus.mFourierCoeff (fun y => d * UnitAddTorus.mFourier k y) l +
        UnitAddTorus.mFourierCoeff (fun y => (-d) * UnitAddTorus.mFourier (-k) y) l := hlin
    _ = d * (if l = k then 1 else 0) + (-d) * (if l = -k then 1 else 0) := by
      rw [Modes.mFourierCoeff_const_mul, Modes.mFourierCoeff_mFourier l k,
        Modes.mFourierCoeff_const_mul, Modes.mFourierCoeff_mFourier l (-k)]
    _ = _ := by
      simp only [d, k]
      split_ifs <;> push_cast <;> ring
/-- The constant real mode has only its zero Fourier coefficient. -/
theorem realFourierMode_const_fourierCoeff (N : ℕ) (l : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun y => (realFourierMode N none y : ℂ)) l =
      if l = 0 then 1 else 0 := by
  have hconst : (fun y : Torus => (realFourierMode N none y : ℂ)) =
      UnitAddTorus.mFourier (0 : Fin 2 → ℤ) := by
    funext y
    have h0 := congrArg (fun f : C(Torus, ℂ) => f y) UnitAddTorus.mFourier_zero
    simpa [realFourierMode] using h0.symm
  rw [hconst]
  exact Modes.mFourierCoeff_mFourier l 0
end AVenhance.Infra.Parabolic.FourierGalerkin
end
