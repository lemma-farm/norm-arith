module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.PSeries

-- ==== Examples.loefflerd__KN_scratch.Examples.Example_bed694a2c629672fe2f8_Thm_MTT_cusp_log_weighted_square_summable ====
/-
Based on Prove2Me node MTT.cusp_log_weighted_square_summable
(2c6274cd-4b5e-49cd-9daa-d45e670e9fdf) by davidloeffler (2026-09-06).

Proof based on Prove2Me submission 348a3168-5ea6-4fbc-bde4-d85c13179cfb
by cbirkbeck (2026-09-07); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/
set_option autoImplicit false
/-!
# Logarithmically weighted square summability of cusp-form coefficients

Theorem statement: `MTT.cusp_log_weighted_square_summable` (`2c6274cd-4b5e-49cd-9daa-d45e670e9fdf`),
by davidloeffler, 2026-09-06.

Proof: submission `348a3168-5ea6-4fbc-bde4-d85c13179cfb`, by cbirkbeck, 2026-09-07 (ACCEPTED);
locally adapted.

For a weight-$k$ cusp form $f$ on $\Gamma_1(N)$, with $N>0$ and $k\ge2$, its width-one Fourier
coefficients satisfy

$$\sum_{m\ge1}\frac{|a_m(f)|^2\log m}{m^{k+1}}<\infty.$$

This includes weight 2. The term at $m=0$ in the Lean sum is zero by the totalized logarithm and
division conventions. The coefficients are the actual coefficients of the analytic q-expansion.

## Explanation of the source proof

We prove that for a cusp form $f$ of weight $k \ge 2$ on $\Gamma_1(N)$, $N \ge 1$, with width-one
Fourier coefficients $a_m$,

$$\sum_{m \ge 1} \frac{|a_m|^2 \log m}{m^{k+1}} < \infty .$$

(The term $m = 0$ vanishes by the conventions $\log 0 = 0$ and $0/0 = 0$.)

**Idea.** The pointwise Hecke bound $|a_m| \ll m^{k/2}$ is not sufficient: it only produces the
divergent majorant $\log m / m$. Following Rudnick, *Modular forms 2019: Petersson's formula*, §1,
we instead use the mean-square bound $\sum_{m < M} |a_m|^2 \le D\, M^k$, which follows from
Parseval's identity on the horizontal line $\operatorname{Im} \tau = 1/M$, and then sum dyadically.

**Step 1 (Hecke's pointwise bound, Rudnick Lemma 1.1(b)).** Since $\Gamma_1(N)$ has finite index in
$\mathrm{SL}_2(\mathbb Z)$, $f$ is a cusp form for an arithmetic subgroup, and Mathlib's
`CuspFormClass.exists_bound` provides $C \ge 0$ with

$$|f(x+iy)|^2\, y^{k} \le C \qquad (x + iy \in \mathbb H).$$

**Step 2 (Parseval on a horizontal line).** Fix $y > 0$ and let $g(x) = f(x+iy)$, a continuous
function on $\mathbb R$. Since $T \in \Gamma_1(N)$, $1$ is a strict period of $f$, and the
coefficient formula `qExpansion_coeff_eq_intervalIntegral` gives, for every $n \ge 0$,

$$a_n = \int_0^1 q(x+iy)^{-n} f(x+iy)\, dx = e^{2\pi n y} c_n, \qquad c_n = \int_0^1 e^{-2\pi i n x}
g(x)\, dx,$$

where $c_n$ is the $n$-th Fourier coefficient of $g$ on $[0,1]$. Parseval's identity for $g \in
L^2(0,1]$ (`hasSum_sq_fourierCoeffOn`) gives $\sum_{n \in \mathbb Z} |c_n|^2 = \int_0^1 |g|^2$;
dropping the nonnegative terms with $n < 0$ or $n \ge M$ yields Bessel's inequality

$$\sum_{n < M} |a_n|^2 e^{-4\pi n y} \le \int_0^1 |f(x+iy)|^2\, dx .$$

**Step 3 (mean-square bound, inequality (1) in the proof of Rudnick's Theorem 1.2).** Take $y = 1/M$
with $M \ge 1$. By Step 1 the integrand is at most $C M^{k}$, and for $n < M$ we have $e^{-4\pi n/M}
\ge e^{-4\pi}$. Hence

$$\sum_{n < M} |a_n|^2 \le e^{4\pi} \sum_{n < M} |a_n|^2 e^{-4\pi n / M} \le e^{4\pi} C\, M^k =: D\,
M^k ,$$

and the case $M = 0$ is trivial.

**Step 4 (dyadic summation).** This is a general fact about nonnegative sequences: if $b_n \ge 0$
and $\sum_{n < M} b_n \le D M^k$ for all $M$, then $\sum_n b_n \log n / n^{k+1} < \infty$. On the
block $2^j \le n < 2^{j+1}$ one has $\log n \le (j+1) \log 2$ and $n^{k+1} \ge 2^{j(k+1)}$, so

$$\sum_{2^j \le n < 2^{j+1}} \frac{b_n \log n}{n^{k+1}} \le \frac{(j+1) \log 2}{2^{j(k+1)}} \sum_{n
< 2^{j+1}} b_n \le D\, 2^k \log 2 \cdot \frac{j+1}{2^j} .$$

Since $\sum_{j < J} (j+1)/2^j = 4 - 2(J+2)/2^J \le 4$, the partial sums up to $2^J$ are bounded by
$4 D\, 2^k \log 2$. All terms are nonnegative and $M \le 2^M$, so every partial sum is bounded by
this constant, and the series converges (`summable_of_sum_range_le`).

Applying Step 4 with $b_n = |a_n|^2$ and the constant $D$ of Step 3 proves the theorem. The
hypothesis $k \ge 2$ is not used: the argument works for every weight $k \ge 0$.

**Correspondence with the Lean proof.** Step 1 is `MTT.exists_norm_sq_mul_im_pow_le`; Step 2 is
`MTT.qExpansion_coeff_eq_exp_mul_fourierCoeffOn` (the identity $a_n = e^{2\pi n y} c_n$) and
`MTT.sum_range_norm_sq_qExpansion_coeff_mul_exp_le` (Bessel's inequality), with
`MTT.one_mem_strictPeriods_gammaOne` supplying the period; Step 3 is
`MTT.exists_sum_range_norm_sq_qExpansion_coeff_le`; Step 4 is
`MTT.summable_mul_log_div_pow_of_sum_range_le`, built from the block bound
`MTT.sum_Ico_two_pow_mul_log_div_pow_le` and the geometric estimate
`MTT.sum_range_succ_div_two_pow_le`.

<!-- Generated by add_prove2me_provenance.py -->
-/
section privateSection
/-!
# Log-weighted square summability of the Fourier coefficients of a cusp form

For a cusp form `f` of weight `k ≥ 2` on `Γ₁(N)` with width-one Fourier coefficients `a n`, we
prove
`∑ n, ‖a n‖ ^ 2 * log n / n ^ (k + 1) < ∞`.

The argument follows Rudnick, *Modular forms 2019: Petersson's formula*, §1: Hecke's pointwise
bound `y ^ k * ‖f (x + i y)‖ ^ 2 ≤ C` (Lemma 1.1(b), available in Mathlib as
`CuspFormClass.exists_bound`) together with Parseval's identity on the horizontal line
`Im τ = 1 / n` gives the mean-square estimate `∑_{m < n} ‖a m‖ ^ 2 ≤ D * n ^ k` (the inequality
(1) in the proof of Theorem 1.2); dyadic summation then yields the stated convergence.
-/
noncomputable section
open scoped BigOperators

open UpperHalfPlane hiding I
open Complex Finset MeasureTheory
open scoped Real ModularForm MatrixGroups Manifold Topology
namespace MTT
/-! ### Dyadic summation -/


set_option linter.unusedVariables false in
/-- **Bessel's inequality on a horizontal line.** The truncated sum
`∑_{n < M} ‖a n‖ ^ 2 * exp (-4 π n y)` is bounded by `∫₀¹ ‖f (x + i y)‖ ^ 2 dx`. -/
theorem sum_range_norm_sq_qExpansion_coeff_mul_exp_le {f : ℍ → ℂ}
    (hfper : Function.Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) {y : ℝ} (hy : 0 < y) (M : ℕ) 
    (h_MTT_qExpansion_coeff_eq_exp_mul_fourierCoeffOn : ∀ {f : UpperHalfPlane → ℂ},
      Function.Periodic (f ∘ (↑UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) 1 →
        MDiff f →
          UpperHalfPlane.IsBoundedAtImInfty f →
            ∀ {y : ℝ} (hy : 0 < y) (n : ℕ),
              (PowerSeries.coeff n : PowerSeries ℂ → ℂ) (UpperHalfPlane.qExpansion 1 f) =
                (↑(Real.exp (2 * Real.pi * (↑n : ℝ) * y)) : ℂ) *
                  fourierCoeffOn zero_lt_one
                    (fun (x : ℝ) ↦
                      f
                        { coe := (↑x : ℂ) + (↑y : ℂ) * Complex.I,
                          coe_im_pos :=
                            Eq.mpr
                              (id
                                (congrArg (LT.lt 0)
                                  (Eq.trans
                                    (congrArg (HAdd.hAdd 0)
                                      (Eq.trans (Complex.mul_im (↑y : ℂ) Complex.I)
                                        (Eq.trans
                                          (congr (congrArg HAdd.hAdd (mul_one y))
                                            (MulZeroClass.mul_zero 0))
                                          (add_zero y))))
                                    (zero_add y))))
                              hy })
                    (↑n : ℤ))
    (h_MTT_continuous_horizontal_slice : ∀ {f : UpperHalfPlane → ℂ},
      Continuous f →
        ∀ {y : ℝ} (hy : 0 < y),
          Continuous fun (x : ℝ) ↦
            f
              { coe := (↑x : ℂ) + (↑y : ℂ) * Complex.I,
                coe_im_pos :=
                  Eq.mpr
                    (id
                      (congrArg (LT.lt 0)
                        (Eq.trans
                          (congrArg (HAdd.hAdd 0)
                            (Eq.trans (Complex.mul_im (↑y : ℂ) Complex.I)
                              (Eq.trans
                                (congr (congrArg HAdd.hAdd (mul_one y)) (MulZeroClass.mul_zero 0))
                                (add_zero y))))
                          (zero_add y))))
                    hy })
    (h_MTT_memLp_two_restrict_Ioc_of_continuous : ∀ {g : ℝ → ℂ},
      Continuous g →
        ∀ (a b : ℝ), MeasureTheory.MemLp g 2 (MeasureTheory.MeasureSpace.volume.restrict (Set.Ioc a b)))
    :
    ∑ n ∈ range M, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) ≤
      ∫ x in (0 : ℝ)..1, ‖f ⟨x + y * I, by simpa using hy⟩‖ ^ 2 := by
  set g : ℝ → ℂ := fun x ↦ f ⟨x + y * I, by simpa using hy⟩ with hg_def
  have hg : Continuous g := h_MTT_continuous_horizontal_slice hfhol.continuous hy
  -- Parseval for the slice, indexed by `ℤ`
  have hP := hasSum_sq_fourierCoeffOn zero_lt_one (h_MTT_memLp_two_restrict_Ioc_of_continuous hg 0 1)
  simp only [sub_zero, inv_one, one_smul] at hP
  -- termwise: `‖a n‖ ^ 2 * exp (-4 π n y) = ‖c n‖ ^ 2`
  have hterm : ∀ n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) =
      ‖fourierCoeffOn zero_lt_one g n‖ ^ 2 := by
    intro n
    have h1 : Real.exp (2 * π * n * y) ^ 2 * Real.exp (-(4 * π * n * y)) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]
      congr 1
      push_cast
      ring
    rw [h_MTT_qExpansion_coeff_eq_exp_mul_fourierCoeffOn hfper hfhol hfbdd hy n, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    linear_combination ‖fourierCoeffOn zero_lt_one g n‖ ^ 2 * h1
  rw [Finset.sum_congr rfl fun n _ ↦ hterm n,
    ← Finset.sum_image (f := fun i : ℤ ↦ ‖fourierCoeffOn zero_lt_one g i‖ ^ 2)
      (Nat.cast_injective.injOn (s := (range M : Set ℕ)))]
  exact sum_le_hasSum _ (fun i _ ↦ by positivity) hP
/-! ### The mean-square bound for cusp forms -/
variable {N k : ℕ}
end MTT
end
end privateSection
public section publicSection
noncomputable section
open scoped BigOperators

end
end publicSection
