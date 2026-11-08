import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.RamareIdentity
/-!
# Track C: typical factorization — the [mrt] 𝒮-set (Track R, A.2 leg, A2-I)

The set `𝒮` of integers with at least one prime factor in each of a
family of prime blocks `[P_j, Q_j]` — the typical-factorization
restriction of [MR]/[mrt, Appendix A], in the idiom of the Ramaré
`𝒰`-machinery: a level is a `Finset ℕ` of primes, a family is a
`List (Finset ℕ)` (the slot `RamareIdentity.uBound` recurses over),
and membership at one level is the `𝒰`-filter's
`0 < (P.filter (· ∣ n)).card`.
-/
namespace MoltResearch
/-- `n` has at least one divisor in every level of the family.  (For
prime levels: at least one prime factor in each block — the [mrt]
`𝒮`-membership.) -/
def HasFactorInAll (levels : List (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ P ∈ levels, 0 < (P.filter (· ∣ n)).card
instance (levels : List (Finset ℕ)) (n : ℕ) :
    Decidable (HasFactorInAll levels n) :=
  List.decidableBAll _ levels
theorem hasFactorInAll_cons {P : Finset ℕ} {rest : List (Finset ℕ)}
    {n : ℕ} :
    HasFactorInAll (P :: rest) n
      ↔ 0 < (P.filter (· ∣ n)).card ∧ HasFactorInAll rest n := by
  constructor
  · intro h
    exact ⟨h P (List.mem_cons_self ..), fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)⟩
  · rintro ⟨h1, h2⟩ Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ'
    · exact h1
    · exact h2 Q hQ'
def typicalS (a b : ℕ) (levels : List (Finset ℕ)) : Finset ℕ :=
  (Finset.Ioc a b).filter (HasFactorInAll levels)
@[simp] theorem mem_typicalS {a b n : ℕ} {levels : List (Finset ℕ)} :
    n ∈ typicalS a b levels
      ↔ (a < n ∧ n ≤ b) ∧ HasFactorInAll levels n := by
  simp [typicalS, Finset.mem_filter, Finset.mem_Ioc]
theorem typicalS_cons (a b : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) :
    typicalS a b (P :: rest)
      = (typicalS a b rest).filter
          (fun n => 0 < (P.filter (· ∣ n)).card) := by
  ext n
  simp only [mem_typicalS, Finset.mem_filter, hasFactorInAll_cons]
  tauto
theorem char_mul (p m : ℕ) (hp : 0 < p) (hm : 0 < m) (ξ : ℝ) :
    ((Real.fourierChar (-(Real.log (p*m : ℕ) * ξ)) : Circle) : ℂ)
      = ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
  have hp0 : ((p:ℝ)) ≠ 0 := by exact_mod_cast hp.ne'
  have hm0 : ((m:ℝ)) ≠ 0 := by exact_mod_cast hm.ne'
  have hlog : Real.log ((p:ℝ)*(m:ℝ)) = Real.log p + Real.log m :=
    Real.log_mul hp0 hm0
  rw [Real.fourierChar_apply, Real.fourierChar_apply,
    Real.fourierChar_apply, ← Complex.exp_add]
  congr 1
  push_cast
  rw [hlog]
  push_cast
  ring
open Finset in
/-- **The typical band polynomial splits main + collision** (Track R,
A2-III, N3-f): peeling one `𝒰`-level, the `1/n`-normalized phase
polynomial over `typicalS (P :: rest)` factors — each main fibre is
the prime phase `(g p/p)·e(−ξ log p)` times the `1/(ω_P+1)`-weighted
quotient polynomial, and the collision term keeps its raw
`1/ω_P`-weight.  `subset_sum_omega_pos_eq_main_add_coll` through
`typicalS_cons`, with complete multiplicativity and `char_mul`
factoring the fibres. -/
theorem typicalS_phase_main_add_coll (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) (A Δ : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (rest : List (Finset ℕ)) (ξ : ℝ) :
    ∑ m ∈ typicalS A (A+Δ) (P :: rest),
        (g m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
      = (∑ p ∈ P, (g p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)
            * ∑ m' ∈ (((typicalS A (A+Δ) rest).filter
                  (fun n => p ∣ n)).image (· / p)).filter
                (fun m' => ¬ p ∣ m'),
              ((g m'/(m':ℂ))
                  * ((Real.fourierChar (-(Real.log m' * ξ)) : Circle) : ℂ))
                / (((P.filter (· ∣ m')).card : ℂ) + 1))
        + ∑ p ∈ P, ∑ m' ∈ (((typicalS A (A+Δ) rest).filter
              (fun n => p ∣ n)).image (· / p)).filter (fun m' => p ∣ m'),
            ((g (p*m')/((p*m' : ℕ):ℂ))
                * ((Real.fourierChar (-(Real.log (p*m' : ℕ) * ξ))
                  : Circle) : ℂ))
              / (((P.filter (· ∣ (p*m'))).card : ℂ)) := by
  classical
  have hkey := subset_sum_omega_pos_eq_main_add_coll
    (typicalS A (A+Δ) rest) P hP
    (fun m => (g m/(m:ℂ))
      * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
  rw [typicalS_cons, hkey]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp2 : 2 ≤ p := (hP p hp).two_le
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  rw [Finset.mem_filter, Finset.mem_image] at hm'
  obtain ⟨⟨n, hn, rfl⟩, hnd⟩ := hm'
  rw [Finset.mem_filter] at hn
  have hnA : A < n := by
    have := (mem_typicalS.mp hn.1).1
    exact this.1
  have hn0 : 0 < n := by omega
  have hm'0 : 0 < n / p :=
    Nat.div_pos (Nat.le_of_dvd hn0 hn.2) (by omega)
  have hgm : g (p * (n/p)) = g p * g (n/p) :=
    hcm p (n/p) (by omega) hm'0.ne'
  have hcast : ((p * (n/p) : ℕ) : ℂ) = (p:ℂ) * ((n/p : ℕ):ℂ) := by
    push_cast
    ring
  have hchar := char_mul p (n/p) (by omega) hm'0 ξ
  rw [hgm, hcast, hchar]
  ring
noncomputable def eadicCell (P : Finset ℕ) (N v : ℕ) : Finset ℕ :=
  P.filter (fun p => ⌊(N:ℝ) * Real.log p⌋₊ = v)
@[simp] theorem mem_eadicCell {P : Finset ℕ} {N v p : ℕ} :
    p ∈ eadicCell P N v ↔ p ∈ P ∧ ⌊(N:ℝ) * Real.log p⌋₊ = v := by
  simp [eadicCell, Finset.mem_filter]
/-- Distinct cells are disjoint — immediate from the defining
equation. -/
theorem eadicCell_disjoint (P : Finset ℕ) (N : ℕ) {v w : ℕ} (hvw : v ≠ w) :
    Disjoint (eadicCell P N v) (eadicCell P N w) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [mem_eadicCell] at hp hp'
  exact hvw (hp.2.symm.trans hp'.2)
end MoltResearch
