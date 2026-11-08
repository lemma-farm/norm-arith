import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.RamareIdentity
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
def typicalS (a b : ℕ) (levels : List (Finset ℕ)) : Finset ℕ :=
  (Finset.Ioc a b).filter (HasFactorInAll levels)
noncomputable def eadicCell (P : Finset ℕ) (N v : ℕ) : Finset ℕ :=
  P.filter (fun p => ⌊(N:ℝ) * Real.log p⌋₊ = v)
@[simp] theorem mem_eadicCell {P : Finset ℕ} {N v p : ℕ} :
    p ∈ eadicCell P N v ↔ p ∈ P ∧ ⌊(N:ℝ) * Real.log p⌋₊ = v := by
  simp [eadicCell, Finset.mem_filter]
theorem eadicCell_bounds {P : Finset ℕ} {N v p : ℕ} (hN : 0 < N)
    (hp : p ∈ eadicCell P N v) (hp1 : 1 ≤ p) :
    Real.exp ((v:ℝ)/N) ≤ (p:ℝ) ∧ (p:ℝ) < Real.exp (((v:ℝ)+1)/N) := by
  rw [mem_eadicCell] at hp
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp1
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp1)
  have hfl : ((v:ℝ)) ≤ (N:ℝ) * Real.log p ∧
      (N:ℝ) * Real.log p < (v:ℝ) + 1 := by
    have hnn : (0:ℝ) ≤ (N:ℝ) * Real.log p := by positivity
    have := Nat.floor_eq_iff hnn |>.mp hp.2
    exact ⟨this.1, this.2⟩
  constructor
  · rw [← Real.exp_log hp0]
    refine Real.exp_le_exp.2 ?_
    rw [div_le_iff₀ hN0]
    linarith [hfl.1]
  · rw [← Real.exp_log hp0]
    refine Real.exp_lt_exp.2 ?_
    rw [lt_div_iff₀ hN0]
    linarith [hfl.2]
/-- **Two primes of one cell give quotient windows within a collar**
(Track R, A2-III, II-2b): if `q ≤ p` and `N·p ≤ (N+1)·q` — the primes
sit within a factor `1 + 1/N` of each other — then the two quotient
windows start within

  `A/q ≤ A/p + A/(N·p) + 1`

of each other.  The `+1` is the cost of the two `ℕ`-division floors; the
main term `A/(N·p)` is the `1/N`-fraction of the window `A/p` that the
`[MR]` telescoping pays as a collar.

Everything here is `ℕ`-division: `A/p` is `⌊A/p⌋`, and the statement is
exactly the input `sum_Ioc_eq_sum_Ioc_add_collars` needs to know its
collars are short. -/
theorem div_le_div_add_div_add_one (A N p q : ℕ) (hN : 0 < N) (hq : 0 < q)
    (hqp : q ≤ p) (hratio : N * p ≤ (N+1) * q) :
    A / q ≤ A / p + A / (N * p) + 1 := by
  have hp : 0 < p := lt_of_lt_of_le hq hqp
  have hQ0 : (0:ℝ) < q := by exact_mod_cast hq
  have hP0 : (0:ℝ) < p := by exact_mod_cast hp
  have hn0 : (0:ℝ) < N := by exact_mod_cast hN
  have hA0 : (0:ℝ) ≤ A := Nat.cast_nonneg A
  have hr : ((N:ℝ)) * p ≤ ((N:ℝ)+1) * q := by exact_mod_cast hratio
  -- the real inequality: `a/q = (a/p)·(p/q) ≤ (a/p)·(1 + 1/N)`
  have hkey : (A:ℝ)/(q:ℝ) ≤ (A:ℝ)/(p:ℝ) + (A:ℝ)/((N:ℝ)*(p:ℝ)) := by
    rw [div_add_div _ _ (ne_of_gt hP0) (by positivity),
      div_le_div_iff₀ hQ0 (by positivity)]
    have hexp : (A:ℝ) * ((p:ℝ) * ((N:ℝ) * (p:ℝ)))
        = ((A:ℝ) * (p:ℝ)) * ((N:ℝ) * (p:ℝ)) := by ring
    nlinarith [mul_nonneg hA0 (le_of_lt hP0), mul_pos hP0 hn0,
      mul_le_mul_of_nonneg_left hr (mul_nonneg hA0 (le_of_lt hP0))]
  -- floor bridges
  have hAq : ((A/q : ℕ):ℝ) ≤ (A:ℝ)/(q:ℝ) := Nat.cast_div_le
  have hfloor : ∀ m : ℕ, 0 < m → (A:ℝ)/(m:ℝ) < ((A/m : ℕ):ℝ) + 1 := by
    intro m hm
    have hM0 : (0:ℝ) < m := by exact_mod_cast hm
    have hmod : A < m * (A/m) + m := by
      have := Nat.div_add_mod A m
      have hlt := Nat.mod_lt A hm
      omega
    have hcast : (A:ℝ) < (m:ℝ) * ((A/m : ℕ):ℝ) + (m:ℝ) := by exact_mod_cast hmod
    rw [div_lt_iff₀ hM0]
    linarith
  have hAp := hfloor p hp
  have hANp := hfloor (N*p) (Nat.mul_pos hN hp)
  have hcastNp : (((N*p : ℕ)):ℝ) = (N:ℝ)*(p:ℝ) := by push_cast; ring
  rw [hcastNp] at hANp
  have hfin : ((A/q : ℕ):ℝ) < ((A/p : ℕ):ℝ) + ((A/(N*p) : ℕ):ℝ) + 2 := by
    linarith
  have : A/q < A/p + A/(N*p) + 2 := by exact_mod_cast hfin
  omega
/-- **Primes of one cell are within a factor `1 + 1/N`** (Track R,
A2-III, II-2b): the e-adic cell at resolution `2N` has multiplicative
width `e^{1/(2N)} ≤ 1 + 1/N`, so any two of its members satisfy the
purely arithmetic ratio bound `N·p ≤ (N+1)·q`.

The doubled resolution is what makes the bound *arithmetic*: at
resolution `N` the cell width is `e^{1/N}`, which exceeds `1 + 1/N`, and
no `ℕ`-inequality of this shape would hold.  Halving the cell buys the
slack, and costs only a factor `2` in the number of cells. -/
theorem eadicCell_ratio_le {P : Finset ℕ} {N v p q : ℕ} (hN : 0 < N)
    (hp : p ∈ eadicCell P (2*N) v) (hq : q ∈ eadicCell P (2*N) v)
    (hp1 : 1 ≤ p) (hq1 : 1 ≤ q) :
    N * p ≤ (N+1) * q := by
  have hN2 : 0 < 2*N := by omega
  obtain ⟨-, hpub⟩ := eadicCell_bounds hN2 hp hp1
  obtain ⟨hqlb, -⟩ := eadicCell_bounds hN2 hq hq1
  have hn0 : (0:ℝ) < N := by exact_mod_cast hN
  have hcast : ((2*N : ℕ):ℝ) = 2*(N:ℝ) := by push_cast; ring
  rw [hcast] at hpub hqlb
  -- `e^{(v+1)/(2N)} = e^{v/(2N)}·e^{1/(2N)}`
  have hsplit : ((v:ℝ)+1)/(2*(N:ℝ)) = (v:ℝ)/(2*(N:ℝ)) + 1/(2*(N:ℝ)) := by
    field_simp
  -- `e^{1/(2N)} ≤ 1 + 1/N`
  have hx0 : (0:ℝ) < 1/(2*(N:ℝ)) := by positivity
  have hx1 : |1/(2*(N:ℝ))| ≤ 1 := by
    rw [abs_of_pos hx0]
    rw [div_le_one (by positivity)]
    have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have hexp : Real.exp (1/(2*(N:ℝ))) ≤ 1 + 1/(N:ℝ) := by
    have habs := Real.abs_exp_sub_one_le hx1
    have h1 := (abs_le.mp habs).2
    rw [abs_of_pos hx0] at h1
    have : (2:ℝ) * (1/(2*(N:ℝ))) = 1/(N:ℝ) := by field_simp
    linarith
  have hexpq : Real.exp ((v:ℝ)/(2*(N:ℝ))) ≤ (q:ℝ) := hqlb
  have hexppos : (0:ℝ) < Real.exp ((v:ℝ)/(2*(N:ℝ))) := Real.exp_pos _
  have hchain : (p:ℝ) < (q:ℝ) * (1 + 1/(N:ℝ)) := by
    calc (p:ℝ) < Real.exp (((v:ℝ)+1)/(2*(N:ℝ))) := hpub
      _ = Real.exp ((v:ℝ)/(2*(N:ℝ))) * Real.exp (1/(2*(N:ℝ))) := by
          rw [hsplit, Real.exp_add]
      _ ≤ (q:ℝ) * (1 + 1/(N:ℝ)) := by
          refine mul_le_mul hexpq hexp (le_of_lt (by positivity)) ?_
          exact le_trans (le_of_lt hexppos) hexpq
  have hfinal : (N:ℝ) * (p:ℝ) < ((N:ℝ)+1) * (q:ℝ) := by
    have hq0 : (0:ℝ) < q := by exact_mod_cast hq1
    have := mul_lt_mul_of_pos_left hchain hn0
    calc (N:ℝ) * (p:ℝ) < (N:ℝ) * ((q:ℝ) * (1 + 1/(N:ℝ))) := this
      _ = ((N:ℝ)+1) * (q:ℝ) := by field_simp
  have : N * p < (N+1) * q := by exact_mod_cast hfinal
  omega
end MoltResearch
