/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module
public import Examples.rwst__Subspace_Theorems.Dependencies.v3438b5948dc0.ArithmeticHeights.BombieriVaalerEntries
public import Examples.rwst__Subspace_Theorems.Dependencies.v3438b5948dc0.ArithmeticHeights.Gelfond
public import Examples.rwst__Subspace_Theorems.Dependencies.v3438b5948dc0.DiophantineApproximation.MonomialDeviation
public import Examples.rwst__Subspace_Theorems.Dependencies.v3438b5948dc0.DiophantineApproximation.PolynomialDeterminantHeight
public import Examples.rwst__Subspace_Theorems.Dependencies.v3438b5948dc0.DiophantineApproximation.MultiHomogeneous
public import Examples.rwst__Subspace_Theorems.Dependencies.v3438b5948dc0.DiophantineApproximation.MvHasseDerivHeight
set_option autoImplicit false
set_option linter.deprecated false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# The multihomogeneous auxiliary polynomial

Step I of the proof of the Subspace Theorem builds one polynomial in `m` blocks of `n + 1`
variables that vanishes, to high order in every block, along every one of the finitely many
systems of linear forms in play. This file is that construction: Bombieri–Gubler's (7.5.14) and
Lemma 7.5.15.

The space of candidates is the multihomogeneous polynomials of a fixed multidegree `d : κ → ℕ`,
whose monomials are `MvPolynomial.multiMons d` (`DiophantineApproximation.MultiHomogeneous`). For
one invertible matrix `A` the polynomial read in the coordinates `A · X h` is
`MvPolynomial.blockSubst A⁻¹ P`, and the expansion coefficients of the Hasse derivatives that
Lemma 7.5.15 is about are the coefficients of `blockSubst A⁻¹ (hasseDeriv I P)`.

Three things have to be supplied. *That enough coefficients may be killed*: the monomials whose
exponent of one variable is far below its mean `∑ h, d h / (n + 1)` are exponentially few
(`DiophantineApproximation.MonomialDeviation`), so the conditions are at most half as many as the
unknowns and Siegel's lemma applies. *That the height stays linear in `∑ h, d h`*: the height of
the condition matrix and of a substituted Hasse derivative are controlled here from the local
factors, the only inputs being the number of monomials, the number of variables in a block, and
one reference tuple collecting the entries of all the matrices. *That killing those coefficients
kills the others*: the vanishing propagates from order `0` to order `I` by the chain rule, which
is `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero`.

## Main results

* `Height.mulHeight_le_pow_mul_mul_pow` and `Height.mulHeight_le_pow_mul_pow`: **transport from
  local factors to the height** — a tuple whose local factor is at most `C` times a product of a
  local factor of `z` and a `D`-th power of one of `y` at the archimedean absolute values, and at
  most that product at the nonarchimedean ones, has height at most
  `C ^ totalWeight K * H z * H y ^ D`.
* `MvPolynomial.iSup_coeff_blockSubst_le` and
  `MvPolynomial.iSup_coeff_blockSubst_le_of_isNonarchimedean`: **the local factor of a substituted
  polynomial**, with `#support · (#ι · ‖A‖_v) ^ D` at an archimedean absolute value and
  `‖A‖_v ^ D` at a nonarchimedean one (Gauss's lemma).
* `MvPolynomial.mulHeight_blockSubst_hasseDeriv_le` and its logarithmic form
  `MvPolynomial.logHeight_blockSubst_hasseDeriv_le`: **the height of a substituted Hasse
  derivative**.
* `MvPolynomial.mulHeight_matrix_blockSubst_monomial_le`: **the height of the condition matrix**,
  which does not depend on the number of rows or columns.
* `MvPolynomial.mulHeight_eq_mulHeight_coeff_multiMons` and
  `MvPolynomial.absMulHeight_coeff_multiMons`: the dictionary between the vector Siegel's lemma
  produces and the polynomial the milestone is about.
* `MvPolynomial.exists_ne_zero_isMultiHomogeneous_coeff_blockSubst_eq_zero`: **Siegel's lemma in
  the multihomogeneous setting** — at most half as many linear conditions as monomials give a
  nonzero multihomogeneous solution of logarithmic height `O (∑ h, d h)`.
* `MvPolynomial.exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_hasseDeriv_eq_zero`:
  **the milestone**, Lemma 7.5.15.

## Implementation notes

⚠ **The chain rule is the whole content of the vanishing statement.** The expansion coefficient
`a(L v; J; I)` is *not* `binom (J + I) I · a(L v; J + I; 0)`: Bombieri–Gubler differentiate in the
original coordinates and expand in the transformed ones, so a coefficient of `∂_I P` is a
combination, over all orders with the same block degrees, of coefficients of `P` read in the
transformed coordinates. `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero` proves exactly what is
needed by induction on the order and never names that combination. It needs characteristic zero,
because `hasseDeriv_comp` produces a positive integer factor that has to be inverted.

⚠ **The conditions imposed are at order `0` only, and they are indexed by the monomial.** For each
form, that is each row `i` of some `A v` up to equality, and each monomial `N` of multidegree `d`
with `∑ h, N (h, i) / d h ≤ m/(n+1) − m η`, the condition is `(blockSubst (A v)⁻¹ P).coeff N = 0`.
That
this implies the vanishing at every order `I` with `∑ h, (∑ i, I (h, i)) / d h ≤ m η` and every
`J` with `∑ h, J (h, i) / d h ≤ m/(n+1) − 2 m η` is exactly where the factor `2` in the book's
`2 m η` is spent: `N = J + I'` moves the threshold by at most `m η`.

⚠ **The conditions are counted by forms, not by places** (Evertse–Schlickewei's construction from
the distinct forms). Whether all monomials of `P` read in the coordinates `A v` have large
exponent along the row `i` depends on that row alone: another system with the same form in row
`i'` differs by a substitution whose row `i'` is a unit vector
(`MvPolynomial.blockSubst_coeff_mem_of_row`). So one family of conditions per distinct form `F`
suffices, and the count is `2 #F` where Bombieri–Gubler have `2 (n + 1) |S|`.

⚠ **The upper half of the book's interval is free.** A Hasse derivative of a multihomogeneous
polynomial is multihomogeneous (`MvPolynomial.IsMultiHomogeneous.hasseDeriv`), so a nonzero
coefficient has `∑ i, ∑ h, J (h, i) / d h = m − ∑ h, (∑ i, I (h, i)) / d h`. If one exponent
exceeds `m/(n+1) + 2 n m η`, the remaining `n` of them average below `m/(n+1) − 2 m η`, and the
lower half applies to one of those. This is why `n ≥ 1` is needed a second time.

⚠ **The hypothesis on `m` is strict here.** Bombieri–Gubler ask
`m ≥ 4 log (2 (n+1) |S|) / ((n+1)(n+2) η²)` (here `4 log (2 #F) / ((n+1)(n+2) η²)`), which
leaves no room for the error term `(η (n+1)(n+2)/2)² / (2(n+1)) · ∑ h, 1/d h` of the Chernoff
bound; that term is positive for every `d` and tends to `0` only as `d → ∞`. The strict
inequality creates a positive slack, and `D₀` is chosen to make the error term smaller than it.
Replacing `2 #F` by `4 #F` and keeping `≥` would do the same.

⚠ **`C₂` and `C₃` are allowed to depend on `m`, `S` and `η`.** The book claims they depend only on
`K` and the forms. That is true — the `m`-dependence sits in `log #multiMons d`, which is
`O (log d)` and could be absorbed into `D₀` — but Layer 5.6 fixes `m` before it uses `C₂`, so
nothing downstream needs the stronger form, and the crude bound
`log #multiMons d ≤ #ι · ∑ h, d h` keeps the proof linear.

⚠ **Mathlib's finiteness of the nonarchimedean local factors is private.** `Height.mulHeight` is
built from a `finprod` over the nonarchimedean absolute values, and the fact that the local factors
of a nonzero tuple differ from `1` at only finitely many of them is proved in Mathlib as a
`private lemma`. It is reproved here as `Height.hasFiniteMulSupport_iSup`; `fun_prop` cannot be
used for it across the module boundary, because it would have to name the private lemma.

⚠ **Only the `≤` direction of the height transport is available.** Mathlib's
`Finsupp.mulHeight_le_of_forall_iSup_le` needs *equality* of the local factors at the
nonarchimedean absolute values. The archimedean product and the nonarchimedean `finprod` are
therefore compared separately here (`finprod_le_finprod₀`, `finprod_pow`, `finprod_mul_distrib`).

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
(7.5.14), Lemma 7.5.15 and (7.20)–(7.25).

This is Layer 5.2 of the `DiophantineApproximation` roadmap.
-/
@[expose] public section
open Finset Height AdmissibleAbsValues Real
namespace Height
variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ρ : Type*} [Finite ι] [Finite ρ]
/-- The local factors of a nonzero tuple differ from `1` at only finitely many nonarchimedean
absolute values. Mathlib proves this, but privately. -/
theorem hasFiniteMulSupport_iSup {x : ι → K} (hx : x ≠ 0) :
    (fun v : nonarchAbsVal (K := K) ↦ ⨆ i, v.val (x i)).HasFiniteMulSupport := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := ⟨i₀⟩
  have hsub : Function.mulSupport (fun v : nonarchAbsVal (K := K) ↦ ⨆ i, v.val (x i))
      ⊆ ⋃ i ∈ {i : ι | x i ≠ 0},
        (fun v : nonarchAbsVal (K := K) ↦ v.val (x i)) ⁻¹' {y | y ≠ 1} := by
    intro v hv
    by_contra hc
    refine hv ?_
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq, not_exists] at hc
    have hall : ∀ i, v.val (x i) ≤ 1 := by
      intro i
      rcases eq_or_ne (x i) 0 with h | h
      · rw [h, map_zero]; exact zero_le_one
      · exact le_of_eq (not_not.mp (fun hne ↦ hc i h hne))
    have h1 : v.val (x i₀) = 1 := not_not.mp (fun hne ↦ hc i₀ hi₀ hne)
    refine le_antisymm (Real.iSup_le hall zero_le_one) ?_
    rw [← h1]
    exact Finite.le_ciSup_of_le i₀ le_rfl
  exact Set.Finite.subset
    (Set.Finite.biUnion (Set.toFinite _) fun i hi ↦ AdmissibleAbsValues.hasFiniteMulSupport hi)
    hsub
/-- **Transport from local factors to the height.** A tuple whose local factor is at most `C`
times the local factor of `z` and the `D`-th power of that of `y` at every archimedean absolute
value, and at most that product at every nonarchimedean one, has height at most
`C ^ totalWeight K * H(z) * H(y) ^ D`. -/
theorem mulHeight_le_pow_mul_mul_pow {τ : Type*} [Finite τ] {x : ι → K} {z : τ → K} {y : ρ → K}
    {C : ℝ} {D : ℕ} (hC : 1 ≤ C) (hz : z ≠ 0) (hy : y ≠ 0)
    (harch : ∀ v ∈ archAbsVal (K := K),
      (⨆ i, v (x i)) ≤ C * ((⨆ t, v (z t)) * (⨆ r, v (y r)) ^ D))
    (hnon : ∀ v ∈ nonarchAbsVal (K := K),
      (⨆ i, v (x i)) ≤ (⨆ t, v (z t)) * (⨆ r, v (y r)) ^ D) :
    mulHeight x ≤ C ^ totalWeight K * (mulHeight z * mulHeight y ^ D) := by
  have hCtw : (1 : ℝ) ≤ C ^ totalWeight K := one_le_pow₀ hC
  have hyD : (1 : ℝ) ≤ mulHeight y ^ D := one_le_pow₀ (one_le_mulHeight y)
  have hz1 : (1 : ℝ) ≤ mulHeight z := one_le_mulHeight z
  rcases eq_or_ne x 0 with rfl | hx
  · rw [mulHeight_zero]
    calc (1 : ℝ) = 1 * (1 * 1) := by ring
      _ ≤ C ^ totalWeight K * (mulHeight z * mulHeight y ^ D) := by gcongr
  rw [mulHeight_eq hx, mulHeight_eq hy, mulHeight_eq hz, mul_pow]
  set az : Multiset ℝ := archAbsVal.map fun v : AbsoluteValue K ℝ ↦ ⨆ t, v (z t) with hazdef
  set ay : Multiset ℝ := archAbsVal.map fun v : AbsoluteValue K ℝ ↦ ⨆ r, v (y r) with haydef
  have hnnz : (0 : ℝ) ≤ az.prod := by
    refine Multiset.prod_nonneg fun a ha ↦ ?_
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ha
    exact Real.iSup_nonneg fun _ ↦ v.nonneg _
  have hnny : (0 : ℝ) ≤ ay.prod := by
    refine Multiset.prod_nonneg fun a ha ↦ ?_
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ha
    exact Real.iSup_nonneg fun _ ↦ v.nonneg _
  have harch' : (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod
      ≤ C ^ totalWeight K * (az.prod * ay.prod ^ D) := by
    calc (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod
        ≤ (archAbsVal.map fun v : AbsoluteValue K ℝ ↦
            C * ((⨆ t, v (z t)) * (⨆ r, v (y r)) ^ D)).prod :=
          Multiset.prod_map_le_prod_map₀ _ _
            (fun v _ ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _) harch
      _ = (archAbsVal.map fun _ : AbsoluteValue K ℝ ↦ C).prod
            * (archAbsVal.map fun v : AbsoluteValue K ℝ ↦
                (⨆ t, v (z t)) * (⨆ r, v (y r)) ^ D).prod := Multiset.prod_map_mul
      _ = C ^ totalWeight K * (az.prod * (archAbsVal.map fun v : AbsoluteValue K ℝ ↦
                (⨆ r, v (y r)) ^ D).prod) := by
          rw [Multiset.map_const', Multiset.prod_replicate, Multiset.prod_map_mul, hazdef]
          rfl
      _ = C ^ totalWeight K * (az.prod * ay.prod ^ D) := by
          rw [haydef, ← Multiset.prod_map_pow]
  have hnon' : ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i, v.val (x i)
      ≤ (∏ᶠ v : nonarchAbsVal (K := K), ⨆ t, v.val (z t))
        * (∏ᶠ v : nonarchAbsVal (K := K), ⨆ r, v.val (y r)) ^ D := by
    have hfy : Function.HasFiniteMulSupport
        (fun v : nonarchAbsVal (K := K) ↦ ⨆ r, v.val (y r)) := hasFiniteMulSupport_iSup hy
    have hfz : Function.HasFiniteMulSupport
        (fun v : nonarchAbsVal (K := K) ↦ ⨆ t, v.val (z t)) := hasFiniteMulSupport_iSup hz
    have hfx : Function.HasFiniteMulSupport
        (fun v : nonarchAbsVal (K := K) ↦ ⨆ i, v.val (x i)) := hasFiniteMulSupport_iSup hx
    have hfyD : Function.HasFiniteMulSupport
        (fun v : nonarchAbsVal (K := K) ↦ (⨆ r, v.val (y r)) ^ D) :=
      Set.Finite.subset hfy fun v hv ↦ by
        simp only [Function.mem_mulSupport] at hv ⊢
        exact fun hc ↦ hv (by rw [hc, one_pow])
    have hfzy : Function.HasFiniteMulSupport
        (fun v : nonarchAbsVal (K := K) ↦ (⨆ t, v.val (z t)) * (⨆ r, v.val (y r)) ^ D) :=
      Set.Finite.subset (Set.Finite.union hfz hfyD) (Function.mulSupport_mul _ _)
    rw [finprod_pow hfy D, ← finprod_mul_distrib hfz hfyD]
    exact finprod_le_finprod₀ hfx (fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _)
      hfzy fun v ↦ hnon v.val v.prop
  have hnn1 : (0 : ℝ) ≤ ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i, v.val (x i) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _
  have hnnfz : (0 : ℝ) ≤ ∏ᶠ v : nonarchAbsVal (K := K), ⨆ t, v.val (z t) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _
  have hnnfy : (0 : ℝ) ≤ ∏ᶠ v : nonarchAbsVal (K := K), ⨆ r, v.val (y r) :=
    finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ v.val.nonneg _
  calc (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod
        * ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i, v.val (x i)
      ≤ (C ^ totalWeight K * (az.prod * ay.prod ^ D))
          * ((∏ᶠ v : nonarchAbsVal (K := K), ⨆ t, v.val (z t))
            * (∏ᶠ v : nonarchAbsVal (K := K), ⨆ r, v.val (y r)) ^ D) := by
        refine mul_le_mul harch' hnon' hnn1 ?_
        have : (0 : ℝ) ≤ C ^ totalWeight K := by positivity
        positivity
    _ = C ^ totalWeight K * ((az.prod * ∏ᶠ v : nonarchAbsVal (K := K), ⨆ t, v.val (z t))
          * (ay.prod ^ D * (∏ᶠ v : nonarchAbsVal (K := K), ⨆ r, v.val (y r)) ^ D)) := by ring
/-- **Transport from local factors to the height, with a power.** -/
theorem mulHeight_le_pow_mul_pow {x : ι → K} {y : ρ → K} {C : ℝ} {D : ℕ}
    (hC : 1 ≤ C) (hy : y ≠ 0)
    (harch : ∀ v ∈ archAbsVal (K := K), (⨆ i, v (x i)) ≤ C * (⨆ r, v (y r)) ^ D)
    (hnon : ∀ v ∈ nonarchAbsVal (K := K), (⨆ i, v (x i)) ≤ (⨆ r, v (y r)) ^ D) :
    mulHeight x ≤ C ^ totalWeight K * mulHeight y ^ D := by
  have hone : ∀ v : AbsoluteValue K ℝ, (⨆ _ : Unit, v ((1 : Unit → K) ())) = 1 := by
    intro v
    rw [ciSup_unique]
    simp
  have hz : (1 : Unit → K) ≠ 0 := by
    intro hc
    exact one_ne_zero (congrFun hc ())
  have := mulHeight_le_pow_mul_mul_pow (x := x) (z := (1 : Unit → K)) (y := y) hC hz hy
    (fun v hv ↦ by rw [hone v, one_mul]; exact harch v hv)
    (fun v hv ↦ by rw [hone v, one_mul]; exact hnon v hv)
  rwa [mulHeight_one, one_mul] at this
end Height
namespace MvPolynomial
variable {K : Type*} [Field K] {κ ι : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- A substituted variable has at most `#ι` monomials. -/
theorem card_support_blockSubst_X_le (A : Matrix ι ι K) (h : κ) (j : ι) :
    #(blockSubst A (X ((h, j) : κ × ι))).support ≤ Fintype.card ι := by
  classical
  have hsub : (blockSubst A (X ((h, j) : κ × ι))).support
      ⊆ Finset.univ.image fun l : ι ↦ Finsupp.single ((h, l) : κ × ι) 1 := by
    rw [blockSubst_X]
    refine (MvPolynomial.support_sum).trans (Finset.biUnion_subset.mpr fun l _ ↦ ?_)
    rw [C_mul_X_eq_monomial]
    refine (MvPolynomial.support_monomial_subset).trans ?_
    simp only [Finset.singleton_subset_iff, Finset.mem_image]
    exact ⟨l, Finset.mem_univ l, rfl⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans (le_of_eq Finset.card_univ))
omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem coeff_blockSubst_X_apply (A : Matrix ι ι K) (h : κ) (j : ι) (m : κ × ι →₀ ℕ) :
    (blockSubst A (X ((h, j) : κ × ι))).coeff m
      = ∑ l, A j l * ((X ((h, l) : κ × ι) : MvPolynomial (κ × ι) K)).coeff m := by
  rw [blockSubst_X, MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun l _ ↦ by rw [coeff_C_mul]
omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- **The local factor of a substituted variable** is at most the largest local factor of the
matrix, or `1`. -/
theorem iSup_coeff_blockSubst_X_le (v : AbsoluteValue K ℝ) (A : Matrix ι ι K) (h : κ) (j : ι) :
    (⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (X ((h, j) : κ × ι))).coeff m))
      ≤ (⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1 := by
  classical
  have hbd : ∀ p : ι × ι, v (A p.1 p.2) ≤ (⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1 := fun p ↦
    le_sup_of_le_left
      (le_ciSup (f := fun q : ι × ι ↦ v (A q.1 q.2)) (Finite.bddAbove_range _) p)
  refine Real.iSup_le (fun m ↦ ?_) (le_sup_of_le_right zero_le_one)
  rw [coeff_blockSubst_X_apply]
  by_cases hm : ∃ l : ι, m = Finsupp.single ((h, l) : κ × ι) 1
  · obtain ⟨l₀, rfl⟩ := hm
    rw [Finset.sum_eq_single l₀]
    · simp only [coeff_X, ↓reduceIte, mul_one]
      exact hbd (j, l₀)
    · intro l _ hl
      have hne : Finsupp.single ((h, l) : κ × ι) 1 ≠ Finsupp.single ((h, l₀) : κ × ι) 1 := by
        intro hc
        exact hl (Prod.ext_iff.mp
          (Finsupp.single_left_injective (b := (1 : ℕ)) one_ne_zero hc)).2
      rw [coeff_X, ite_eq_right hne, mul_zero]
    · intro hl; exact absurd (Finset.mem_univ l₀) hl
  · rw [Finset.sum_eq_zero, map_zero]
    · exact le_sup_of_le_right zero_le_one
    · intro l _
      have hne : Finsupp.single ((h, l) : κ × ι) 1 ≠ m := fun hc ↦ hm ⟨l, hc.symm⟩
      rw [coeff_X, ite_eq_right hne, mul_zero]
omit [DecidableEq ι] [DecidableEq κ] in
/-- **The local factor of a monomial in the substituted variables**, with a multiplicativity
constant `c` supplied by the caller: `#ι` at an archimedean absolute value, `1` at a
nonarchimedean one. -/
theorem iSup_coeff_blockSubst_monomial_le_of (v : AbsoluteValue K ℝ) (A : Matrix ι ι K)
    {c : ℝ} (hc : 1 ≤ c)
    (hmul : ∀ (p : MvPolynomial (κ × ι) K) (t : κ × ι),
      (⨆ m : κ × ι →₀ ℕ, v ((p * blockSubst A (X t)).coeff m))
        ≤ c * ((⨆ m : κ × ι →₀ ℕ, v (p.coeff m))
            * ⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (X t)).coeff m))) :
    ∀ (N : ℕ) (ν : κ × ι →₀ ℕ), ∑ t, ν t = N →
      (⨆ J : κ × ι →₀ ℕ, v ((blockSubst A (monomial ν (1 : K))).coeff J))
        ≤ (c * ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1)) ^ N := by
  have hB : (1 : ℝ) ≤ (⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1 := le_sup_right
  intro N
  induction N with
  | zero =>
      intro ν hν
      have hν0 : ν = 0 := by
        ext t
        have := Finset.sum_eq_zero_iff.mp hν t (Finset.mem_univ t)
        simpa using this
      subst hν0
      rw [show (monomial (0 : κ × ι →₀ ℕ) (1 : K)) = 1 by simp, map_one, iSup_coeff_one, pow_zero]
  | succ N ih =>
      intro ν hν
      have hν0 : ν ≠ 0 := by
        rintro rfl
        simp at hν
      obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr hν0
      obtain ⟨h₀, j₀⟩ := t
      set ν' : κ × ι →₀ ℕ := ν - Finsupp.single ((h₀, j₀) : κ × ι) 1 with hν'def
      have hνs : 1 ≤ ν (h₀, j₀) := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp ht)
      have hνeq : ν' + Finsupp.single ((h₀, j₀) : κ × ι) 1 = ν := by
        ext u
        rcases eq_or_ne u ((h₀, j₀) : κ × ι) with rfl | hu
        · simp only [hν'def, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · simp [hν'def, Ne.symm hu]
      have hsingle : ∑ u : κ × ι, (Finsupp.single ((h₀, j₀) : κ × ι) 1) u = 1 := by
        rw [Finset.sum_eq_single ((h₀, j₀) : κ × ι)]
        · simp
        · intro u _ hu
          simp [Ne.symm hu]
        · intro hu; exact absurd (Finset.mem_univ ((h₀, j₀) : κ × ι)) hu
      have hν'sum : ∑ u, ν' u = N := by
        have := congrArg (fun f : κ × ι →₀ ℕ ↦ ∑ u, f u) hνeq
        simp only [Finsupp.add_apply, Finset.sum_add_distrib, hsingle] at this
        omega
      have hfac : blockSubst A (monomial ν (1 : K))
          = blockSubst A (monomial ν' (1 : K)) * blockSubst A (X ((h₀, j₀) : κ × ι)) := by
        rw [← map_mul, ← hνeq, monomial_add_single, pow_one]
      have hX := iSup_coeff_blockSubst_X_le v A h₀ j₀
      have hnnX : (0 : ℝ) ≤ ⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (X ((h₀, j₀) : κ × ι))).coeff m) :=
        Real.iSup_nonneg fun _ ↦ v.nonneg _
      calc (⨆ J : κ × ι →₀ ℕ, v ((blockSubst A (monomial ν (1 : K))).coeff J))
          ≤ c * ((⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (monomial ν' (1 : K))).coeff m))
              * ⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (X ((h₀, j₀) : κ × ι))).coeff m)) := by
            rw [hfac]; exact hmul _ _
        _ ≤ c * ((c * ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1)) ^ N
              * ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1)) := by
            gcongr
            exact ih ν' hν'sum
        _ = (c * ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1)) ^ (N + 1) := by ring
/-! ### The local factor of a substituted polynomial -/
omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem blockSubst_eq_sum (M : Matrix ι ι K) (R : MvPolynomial (κ × ι) K) :
    blockSubst M R
      = ∑ ν ∈ R.support, C (R.coeff ν) * blockSubst M (monomial ν (1 : K)) := by
  conv_lhs => rw [R.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  have h1 : blockSubst M (monomial ν (R.coeff ν))
      = blockSubst M (C (R.coeff ν) * monomial ν (1 : K)) := by
    rw [C_mul_monomial, mul_one]
  rw [h1, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem iSup_coeff_C_mul_le (v : AbsoluteValue K ℝ) (a : K) (Q : MvPolynomial (κ × ι) K) :
    (⨆ m : κ × ι →₀ ℕ, v ((C a * Q).coeff m)) ≤ v a * ⨆ m : κ × ι →₀ ℕ, v (Q.coeff m) := by
  refine Real.iSup_le (fun m ↦ ?_)
    (mul_nonneg (v.nonneg a) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
  rw [coeff_C_mul, map_mul]
  exact mul_le_mul_of_nonneg_left
    (le_ciSup (Finsupp.bddAbove_range_apply Q.coeff v) m) (v.nonneg a)
omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Multiplying by a substituted variable multiplies the local factor by at most `#ι`. -/
theorem iSup_coeff_mul_blockSubst_X_le (v : AbsoluteValue K ℝ) (A : Matrix ι ι K)
    (p : MvPolynomial (κ × ι) K) (t : κ × ι) :
    (⨆ m : κ × ι →₀ ℕ, v ((p * blockSubst A (X t)).coeff m))
      ≤ (Fintype.card ι : ℝ) * ((⨆ m : κ × ι →₀ ℕ, v (p.coeff m))
          * ⨆ m : κ × ι →₀ ℕ, v ((blockSubst A (X t)).coeff m)) := by
  obtain ⟨h, j⟩ := t
  refine (iSup_coeff_mul_le_card_support v p _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    (Real.iSup_nonneg fun _ ↦ v.nonneg _))
  exact_mod_cast (min_le_right _ _).trans (card_support_blockSubst_X_le A h j)
omit [DecidableEq ι] [DecidableEq κ] in
/-- **The local factor of a substituted monomial of degree `D`**, archimedean form. -/
theorem iSup_coeff_blockSubst_monomial_le [Nonempty ι] (v : AbsoluteValue K ℝ)
    (A : Matrix ι ι K) {ν : κ × ι →₀ ℕ} {D : ℕ} (hν : ∑ t, ν t = D) :
    (⨆ J : κ × ι →₀ ℕ, v ((blockSubst A (monomial ν (1 : K))).coeff J))
      ≤ ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1)) ^ D := by
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  exact iSup_coeff_blockSubst_monomial_le_of v A hcard
    (iSup_coeff_mul_blockSubst_X_le (κ := κ) v A) D ν hν
omit [DecidableEq ι] [DecidableEq κ] in
/-- **The local factor of a substituted monomial of degree `D`**, nonarchimedean form: the
number of variables drops out. -/
theorem iSup_coeff_blockSubst_monomial_le_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (A : Matrix ι ι K) {ν : κ × ι →₀ ℕ} {D : ℕ} (hν : ∑ t, ν t = D) :
    (⨆ J : κ × ι →₀ ℕ, v ((blockSubst A (monomial ν (1 : K))).coeff J))
      ≤ ((⨆ p : ι × ι, v (A p.1 p.2)) ⊔ 1) ^ D := by
  have h := iSup_coeff_blockSubst_monomial_le_of v A le_rfl
    (fun p t ↦ by rw [one_mul, MvPolynomial.iSup_coeff_mul hv]) D ν hν
  rwa [one_mul] at h
omit [DecidableEq ι] [DecidableEq κ] in
/-- **The local factor of a substituted polynomial**, archimedean form: the number of monomials,
the number of variables in a block raised to the degree, and the largest entry of the matrix. -/
theorem iSup_coeff_blockSubst_le [Nonempty ι] (v : AbsoluteValue K ℝ) (M : Matrix ι ι K)
    {R : MvPolynomial (κ × ι) K} {D : ℕ} (hR : ∀ ν ∈ R.support, ∑ t, ν t ≤ D) :
    (⨆ m : κ × ι →₀ ℕ, v ((blockSubst M R).coeff m))
      ≤ (#R.support : ℝ) * ((⨆ m : κ × ι →₀ ℕ, v (R.coeff m))
        * ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1)) ^ D) := by
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hB1 : (1 : ℝ) ≤ (⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1 := le_sup_right
  have hB : (1 : ℝ) ≤ (Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) := by
    nlinarith
  have hmul := iSup_coeff_mul_blockSubst_X_le (κ := κ) v M
  have hmono : ∀ ν ∈ R.support,
      (⨆ m : κ × ι →₀ ℕ, v ((C (R.coeff ν) * blockSubst M (monomial ν (1 : K))).coeff m))
        ≤ (⨆ m : κ × ι →₀ ℕ, v (R.coeff m))
          * ((Fintype.card ι : ℝ) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1)) ^ D := by
    intro ν hν
    refine (iSup_coeff_C_mul_le v _ _).trans ?_
    refine mul_le_mul (le_ciSup (Finsupp.bddAbove_range_apply R.coeff v) ν) ?_
      (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    exact (iSup_coeff_blockSubst_monomial_le_of v M hcard hmul (∑ t, ν t) ν rfl).trans
      (pow_le_pow_right₀ hB (hR ν hν))
  rw [blockSubst_eq_sum]
  exact iSup_coeff_sum_le R.support _
    (mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (pow_nonneg (by linarith) D)) hmono
omit [DecidableEq ι] [DecidableEq κ] in
/-- **The local factor of a substituted polynomial**, nonarchimedean form: neither the number of
monomials nor the number of variables appears. -/
theorem iSup_coeff_blockSubst_le_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (M : Matrix ι ι K)
    {R : MvPolynomial (κ × ι) K} {D : ℕ} (hR : ∀ ν ∈ R.support, ∑ t, ν t ≤ D) :
    (⨆ m : κ × ι →₀ ℕ, v ((blockSubst M R).coeff m))
      ≤ (⨆ m : κ × ι →₀ ℕ, v (R.coeff m)) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) ^ D := by
  have hB1 : (1 : ℝ) ≤ (⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1 := le_sup_right
  have hmul : ∀ (p : MvPolynomial (κ × ι) K) (t : κ × ι),
      (⨆ m : κ × ι →₀ ℕ, v ((p * blockSubst M (X t)).coeff m))
        ≤ 1 * ((⨆ m : κ × ι →₀ ℕ, v (p.coeff m))
            * ⨆ m : κ × ι →₀ ℕ, v ((blockSubst M (X t)).coeff m)) := by
    intro p t
    rw [one_mul, MvPolynomial.iSup_coeff_mul hv]
  have hmono : ∀ ν ∈ R.support,
      (⨆ m : κ × ι →₀ ℕ, v ((C (R.coeff ν) * blockSubst M (monomial ν (1 : K))).coeff m))
        ≤ (⨆ m : κ × ι →₀ ℕ, v (R.coeff m)) * ((⨆ p : ι × ι, v (M p.1 p.2)) ⊔ 1) ^ D := by
    intro ν hν
    refine (iSup_coeff_C_mul_le v _ _).trans ?_
    refine mul_le_mul (le_ciSup (Finsupp.bddAbove_range_apply R.coeff v) ν) ?_
      (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    have hmon := iSup_coeff_blockSubst_monomial_le_of v M le_rfl hmul (∑ t, ν t) ν rfl
    rw [one_mul] at hmon
    exact hmon.trans (pow_le_pow_right₀ hB1 (hR ν hν))
  rw [blockSubst_eq_sum]
  exact iSup_coeff_sum_le_of_isNonarchimedean hv R.support _
    (mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (pow_nonneg (by linarith) D)) hmono
/-! ### From local factors to the height of a polynomial -/
section Heights
end Heights
section Dictionary
end Dictionary
section Absolute
end Absolute
section Siegel
end Siegel
section Counting
end Counting
section Milestone
end Milestone
section Acceptance
end Acceptance
end MvPolynomial
