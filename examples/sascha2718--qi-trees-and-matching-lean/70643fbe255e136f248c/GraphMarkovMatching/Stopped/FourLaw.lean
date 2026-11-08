module

/-
The four-law contraction of `arbitrary_offspring_matching.tex`
(`thm:four-law-contraction`): for two source laws
`ρ₁, ρ₂` and two target laws `τ₁, τ₂` whose eight restricted directed potentials are
at most `M`, whose eight zero masses are at most `z`, and whose four weighted zero
integrals are at most `e`,

    P(ρ₁ × ρ₂, τ₁ × τ₂; R^□) ≤ a M + b M² + (γ + 4αM) z + 4 (1 + αM) e

with `a = 2 (L + K)`, `b = C_α(u)` and `γ = 2 + 2β`. The bound parameters `z` and `e`
are the paper's `δ₁` and `δ₂`, respectively. The proof integrates over the
doubly-positive set with the cancellation of the mean bad degrees between the source-row
terms and the target-overlap terms (`eq:four-law-rows`, `eq:four-law-overlaps`), and
handles the source pairs with a zero child degree by the resolved normalisation.

The scalar parameters `L`, `K`, `L0` enter as hypotheses, so that the exact maxima
`Lfun`, `Kfun` and rational surrogates are both admissible.

Organisation of the proof:

* `row_real`, `row_pt_gen`: the pointwise row estimate with the `s ≤ u` / `s > u`
  split (`eq:four-law-denominators`, the chord `chord_gen`, `eq:four-law-weight`);
* `main_pt`: the pointwise bound on a doubly-positive source pair
  (`eq:four-law-numerator` divided by `(r^□)^α`);
* `resPsi_pt`, `tsum_resPsi_le`: the product bound `eq:four-law-product` integrated
  over the positive set, carrying the mean bad degrees;
* `tsum_qE_sq_le`, `overlap_two_le`: the overlap estimate with the reversed potentials,
  `eq:four-law-square` and the `(1-β) z` term;
* `failureD_symm`, `failureD_le_resQ`: the identity behind the cancellation of `Q`;
* `PhiDres_square_split`: the pairs with a zero child degree, by the resolved
  normalisation;
* `fourLaw_contraction`: the assembly.
-/
public import GraphMarkovMatching.Stopped.Scalar
public import GraphMarkovMatching.Potential.Restricted

@[expose] public section

namespace GraphMarkovMatching.Stopped

open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical

                                                                                        
                                     
                                                                                         
                                                          

                               

                                                   
lemma qE_eq_ofReal_q {X : Type} (τ : PMF X) (R : X → X → Prop) (x : X) :
    qE τ R x = ENNReal.ofReal (q τ R x) := by
  rw [q, ENNReal.ofReal_toReal qE_ne_top]

                                                                 
                               
                                                                
                                   
                          

                                                               
                                                            
                                                                       
                        
               

                                     

                                                                                  
                                                                                    
                                                                                    
                           

                                                                        

                                                                                   
lemma row_real {α u a b d e rsq : ℝ} (hα : 1 ≤ α) (hu0 : 0 < u) (hu1 : u < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hd0 : 0 ≤ d) (hd1 : d < 1) (he0 : 0 ≤ e) (he1 : e < 1)
    (h1 : (1 - a) * (1 - e) ≤ rsq)
    (h2 : (1 - a) * (1 - e) + (1 - b) * (1 - d) - (1 - a) * (1 - b) ≤ rsq) :
    a * b * rsq ^ (-α)
      ≤ phi α (a * b) * (1 + chordSlope α u * (d + e))
        + phi α a * ((1 / u + α) * (phi α d + phi α e)) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1e : (0 : ℝ) < 1 - e := by linarith
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hab1 : a * b < 1 := by nlinarith
  have h1ab : (0 : ℝ) < 1 - a * b := by linarith
  have hφab : 0 ≤ phi α (a * b) := phi_nonneg hab0 hab1
  have hφa : 0 ≤ phi α a := phi_nonneg ha0 ha1
  have hφd : 0 ≤ phi α d := phi_nonneg hd0 hd1
  have hφe : 0 ≤ phi α e := phi_nonneg he0 he1
  have hc : 0 ≤ chordSlope α u := chordSlope_nonneg hα0 hu0 hu1
  have hcu : (0 : ℝ) ≤ 1 / u + α := by positivity
  have hpos : 0 < (1 - a) * (1 - e) := mul_pos h1a h1e
  have hrsq : 0 < rsq := lt_of_lt_of_le hpos h1
  by_cases hs : d + e ≤ u
  · -- the chord case `s ≤ u`
    have h1s : (0 : ℝ) < 1 - (d + e) := by linarith
    have hlow : (1 - (d + e)) * (1 - a * b) ≤ rsq := by
      nlinarith [h2, mul_nonneg (mul_nonneg ha0 he0) (sub_nonneg.2 hb1.le),
        mul_nonneg (mul_nonneg hb0 hd0) (sub_nonneg.2 ha1.le)]
    have hmono : rsq ^ (-α) ≤ ((1 - (d + e)) * (1 - a * b)) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos h1s h1ab) hlow (by linarith)
    have hsplit : ((1 - (d + e)) * (1 - a * b)) ^ (-α)
        = (1 - (d + e)) ^ (-α) * (1 - a * b) ^ (-α) :=
      Real.mul_rpow h1s.le h1ab.le
    have hchord : (1 - (d + e)) ^ (-α) ≤ 1 + chordSlope α u * (d + e) :=
      chord_gen hα0 hu0 hu1 (by linarith) hs
    have hphi : phi α (a * b) = a * b * (1 - a * b) ^ (-α) := by
      rw [phi, Real.rpow_neg h1ab.le, div_eq_mul_inv]
    have hW0 : 0 ≤ (1 - a * b) ^ (-α) := Real.rpow_nonneg h1ab.le _
    calc a * b * rsq ^ (-α)
        ≤ a * b * ((1 - (d + e)) ^ (-α) * (1 - a * b) ^ (-α)) := by
          rw [← hsplit]; exact mul_le_mul_of_nonneg_left hmono hab0
      _ = phi α (a * b) * (1 - (d + e)) ^ (-α) := by rw [hphi]; ring
      _ ≤ phi α (a * b) * (1 + chordSlope α u * (d + e)) :=
          mul_le_mul_of_nonneg_left hchord hφab
      _ ≤ phi α (a * b) * (1 + chordSlope α u * (d + e))
            + phi α a * ((1 / u + α) * (phi α d + phi α e)) :=
          le_add_of_nonneg_right (by positivity)
  · -- the weight case `s > u`
    push Not at hs
    have hmono : rsq ^ (-α) ≤ ((1 - a) * (1 - e)) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hpos h1 (by linarith)
    have hsplit : ((1 - a) * (1 - e)) ^ (-α) = (1 - a) ^ (-α) * (1 - e) ^ (-α) :=
      Real.mul_rpow h1a.le h1e.le
    have hphia : phi α a = a * (1 - a) ^ (-α) := by
      rw [phi, Real.rpow_neg h1a.le, div_eq_mul_inv]
    have hW : (1 - e) ^ (-α) ≤ 1 + α * phi α e := rpow_neg_alpha_le hα he1
    have hind : 1 ≤ (d + e) / u := by rw [le_div_iff₀ hu0]; linarith
    have hde : d ≤ phi α d := le_phi hα0 hd0 hd1
    have hee : e ≤ phi α e := le_phi hα0 he0 he1
    have hWa : 0 ≤ (1 - a) ^ (-α) := Real.rpow_nonneg h1a.le _
    have hWe : 0 ≤ (1 - e) ^ (-α) := Real.rpow_nonneg h1e.le _
    have hbound : (1 - e) ^ (-α) ≤ (1 / u + α) * (phi α d + phi α e) := by
      calc (1 - e) ^ (-α) ≤ 1 + α * phi α e := hW
        _ ≤ (d + e) / u + α * phi α e := by linarith
        _ ≤ (phi α d + phi α e) / u + α * (phi α d + phi α e) := by
            have h1 : (d + e) / u ≤ (phi α d + phi α e) / u :=
              div_le_div_of_nonneg_right (by linarith) hu0.le
            have h2 : α * phi α e ≤ α * (phi α d + phi α e) :=
              mul_le_mul_of_nonneg_left (by linarith) hα0
            linarith
        _ = (1 / u + α) * (phi α d + phi α e) := by ring
    calc a * b * rsq ^ (-α)
        ≤ a * 1 * ((1 - a) ^ (-α) * (1 - e) ^ (-α)) := by
          rw [← hsplit]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb1.le ha0) hmono
            (Real.rpow_nonneg hrsq.le _) (by linarith)
      _ = phi α a * (1 - e) ^ (-α) := by rw [hphia]; ring
      _ ≤ phi α a * ((1 / u + α) * (phi α d + phi α e)) :=
          mul_le_mul_of_nonneg_left hbound hφa
      _ ≤ phi α (a * b) * (1 + chordSlope α u * (d + e))
            + phi α a * ((1 / u + α) * (phi α d + phi α e)) :=
          le_add_of_nonneg_left (by positivity)

/-- The row estimate in `ℝ≥0∞`, for an abstract pair good degree `rsq`. -/
lemma row_pt_gen {α u a b d e : ℝ} {rsq : ℝ≥0∞} (hα : 1 ≤ α) (hu0 : 0 < u) (hu1 : u < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hd0 : 0 ≤ d) (hd1 : d < 1) (he0 : 0 ≤ e) (he1 : e < 1) (hrsq : rsq ≠ ⊤)
    (h1 : (1 - a) * (1 - e) ≤ rsq.toReal)
    (h2 : (1 - a) * (1 - e) + (1 - b) * (1 - d) - (1 - a) * (1 - b) ≤ rsq.toReal) :
    ENNReal.ofReal a * ENNReal.ofReal b * rsq ^ (-α)
      ≤ ENNReal.ofReal (phi α (a * b))
          * (1 + ENNReal.ofReal (chordSlope α u) * (ENNReal.ofReal d + ENNReal.ofReal e))
        + ENNReal.ofReal (phi α a)
          * ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (ENNReal.ofReal (phi α d) + ENNReal.ofReal (phi α e))) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hreal := row_real hα hu0 hu1 ha0 ha1 hb0 hb1 hd0 hd1 he0 he1 h1 h2
  have hpos : 0 < rsq.toReal :=
    lt_of_lt_of_le (mul_pos (by linarith) (by linarith)) h1
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hab1 : a * b < 1 := by nlinarith
  have hφab : 0 ≤ phi α (a * b) := phi_nonneg hab0 hab1
  have hφa : 0 ≤ phi α a := phi_nonneg ha0 ha1
  have hφd : 0 ≤ phi α d := phi_nonneg hd0 hd1
  have hφe : 0 ≤ phi α e := phi_nonneg he0 he1
  have hc : 0 ≤ chordSlope α u := chordSlope_nonneg hα0 hu0 hu1
  have hu' : (0 : ℝ) ≤ 1 / u := by positivity
  have hrsq_eq : rsq = ENNReal.ofReal rsq.toReal := (ENNReal.ofReal_toReal hrsq).symm
  rw [hrsq_eq, ENNReal.ofReal_rpow_of_pos hpos, ← ENNReal.ofReal_mul ha0,
    ← ENNReal.ofReal_mul hab0]
  refine le_trans (ENNReal.ofReal_le_ofReal hreal) (le_of_eq ?_)
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hφab,
    ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_mul hc, ENNReal.ofReal_add hd0 he0, ENNReal.ofReal_mul hφa,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hu' hα0,
    ENNReal.ofReal_add hφd hφe]

/-- **The pointwise bound on a doubly-positive pair** (`thm:four-law-contraction`):
`eq:four-law-numerator` divided by `(r^□)^α`, the two row terms estimated by
`row_pt_gen` and the two overlap terms by `eq:four-law-denominators`. -/
lemma main_pt {X : Type} {α u : ℝ} (hα : 1 ≤ α) (hu0 : 0 < u) (hu1 : u < 1)
    (τ₁ τ₂ : PMF X) (R : X → X → Prop) (x₁ x₂ : X)
    (h11 : rE τ₁ R x₁ ≠ 0) (h12 : rE τ₂ R x₁ ≠ 0)
    (h21 : rE τ₁ R x₂ ≠ 0) (h22 : rE τ₂ R x₂ ≠ 0) :
    phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) (x₁, x₂))
      ≤ phiE α (q τ₁ R x₁ * q τ₂ R x₁)
          * (1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₂ + qE τ₂ R x₂))
        + phiE α (q τ₁ R x₁)
          * ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (phiE α (q τ₁ R x₂) + phiE α (q τ₂ R x₂)))
        + (1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₁ + qE τ₂ R x₁))
          * phiE α (q τ₁ R x₂ * q τ₂ R x₂)
        + ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (phiE α (q τ₁ R x₁) + phiE α (q τ₂ R x₁)))
          * phiE α (q τ₂ R x₂)
        + cOverlap τ₁ R x₁ x₂ * (WresD α τ₁ R x₁ * WresD α τ₂ R x₂)
        + cOverlap τ₂ R x₁ x₂ * (WresD α τ₂ R x₁ * WresD α τ₁ R x₂) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hαpos : (0 : ℝ) < α := by linarith
  have hq11 : q τ₁ R x₁ < 1 := q_lt_one_of_rE_ne_zero h11
  have hq12 : q τ₂ R x₁ < 1 := q_lt_one_of_rE_ne_zero h12
  have hq21 : q τ₁ R x₂ < 1 := q_lt_one_of_rE_ne_zero h21
  have hq22 : q τ₂ R x₂ < 1 := q_lt_one_of_rE_ne_zero h22
  have hn11 : 0 ≤ q τ₁ R x₁ := q_nonneg
  have hn12 : 0 ≤ q τ₂ R x₁ := q_nonneg
  have hn21 : 0 ≤ q τ₁ R x₂ := q_nonneg
  have hn22 : 0 ≤ q τ₂ R x₂ := q_nonneg
  have hp1 : q τ₁ R x₁ * q τ₂ R x₁ < 1 := by nlinarith
  have hp2 : q τ₁ R x₂ * q τ₂ R x₂ < 1 := by nlinarith
  -- the straight and crossed minorants, and inclusion–exclusion
  have hstrE := straight_le_rE_square τ₁ τ₂ R x₁ x₂
  have hcrE := crossed_le_rE_square τ₁ τ₂ R x₁ x₂
  have hie := rE_square_two_toReal τ₁ τ₂ R x₁ x₂
  have htop : rE (prodPMF τ₁ τ₂) (SquareRel R) (x₁, x₂) ≠ ⊤ := rE_ne_top
  have ha1l : (aOverlap τ₁ R x₁ x₂).toReal ≤ 1 - q τ₁ R x₁ := by
    have := ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_left τ₁ R x₁ x₂)
    rwa [toReal_rE_eq] at this
  have ha1r : (aOverlap τ₁ R x₁ x₂).toReal ≤ 1 - q τ₁ R x₂ := by
    have := ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_right τ₁ R x₁ x₂)
    rwa [toReal_rE_eq] at this
  have ha2l : (aOverlap τ₂ R x₁ x₂).toReal ≤ 1 - q τ₂ R x₁ := by
    have := ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_left τ₂ R x₁ x₂)
    rwa [toReal_rE_eq] at this
  have ha2r : (aOverlap τ₂ R x₁ x₂).toReal ≤ 1 - q τ₂ R x₂ := by
    have := ENNReal.toReal_mono rE_ne_top (aOverlap_le_rE_right τ₂ R x₁ x₂)
    rwa [toReal_rE_eq] at this
  have ha1n : 0 ≤ (aOverlap τ₁ R x₁ x₂).toReal := ENNReal.toReal_nonneg
  have ha2n : 0 ≤ (aOverlap τ₂ R x₁ x₂).toReal := ENNReal.toReal_nonneg
  rw [phiE_eq_qE_mul_rpow α (SquareRel R) (prodPMF τ₁ τ₂) hαpos (x₁, x₂)]
  rw [toReal_rE_eq τ₁ R x₁, toReal_rE_eq τ₂ R x₂, toReal_rE_eq τ₂ R x₁,
    toReal_rE_eq τ₁ R x₂] at hie
  generalize hrsq : rE (prodPMF τ₁ τ₂) (SquareRel R) (x₁, x₂) = rsq at hstrE hcrE hie htop ⊢
  have hstr : (1 - q τ₁ R x₁) * (1 - q τ₂ R x₂) ≤ rsq.toReal := by
    have h := ENNReal.toReal_mono htop hstrE
    rwa [ENNReal.toReal_mul, toReal_rE_eq, toReal_rE_eq] at h
  -- the first row term
  have hrow1 := row_pt_gen (a := q τ₁ R x₁) (b := q τ₂ R x₁) (d := q τ₁ R x₂)
    (e := q τ₂ R x₂) (rsq := rsq) hα hu0 hu1 hn11 hq11 hn12 hq12 hn21 hq21 hn22 hq22 htop
    hstr (by
      have hp : (aOverlap τ₁ R x₁ x₂).toReal * (aOverlap τ₂ R x₁ x₂).toReal
          ≤ (1 - q τ₁ R x₁) * (1 - q τ₂ R x₁) :=
        mul_le_mul ha1l ha2l ha2n (by linarith)
      nlinarith [hie, hp])
  have hrow1' : qE τ₁ R x₁ * qE τ₂ R x₁ * rsq ^ (-α)
      ≤ phiE α (q τ₁ R x₁ * q τ₂ R x₁)
          * (1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₂ + qE τ₂ R x₂))
        + phiE α (q τ₁ R x₁)
          * ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (phiE α (q τ₁ R x₂) + phiE α (q τ₂ R x₂))) := by
    rw [qE_eq_ofReal_q, qE_eq_ofReal_q, qE_eq_ofReal_q, qE_eq_ofReal_q, phiE_of_lt hp1,
      phiE_of_lt hq11, phiE_of_lt hq21, phiE_of_lt hq22]
    exact hrow1
  -- the second row term, with the source rows exchanged
  have hrow2 := row_pt_gen (a := q τ₂ R x₂) (b := q τ₁ R x₂) (d := q τ₂ R x₁)
    (e := q τ₁ R x₁) (rsq := rsq) hα hu0 hu1 hn22 hq22 hn21 hq21 hn12 hq12 hn11 hq11 htop
    (by rw [mul_comm]; exact hstr) (by
      have hp : (aOverlap τ₁ R x₁ x₂).toReal * (aOverlap τ₂ R x₁ x₂).toReal
          ≤ (1 - q τ₁ R x₂) * (1 - q τ₂ R x₂) :=
        mul_le_mul ha1r ha2r ha2n (by linarith)
      nlinarith [hie, hp])
  have hrow2' : qE τ₁ R x₂ * qE τ₂ R x₂ * rsq ^ (-α)
      ≤ (1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₁ + qE τ₂ R x₁))
          * phiE α (q τ₁ R x₂ * q τ₂ R x₂)
        + ((ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
            * (phiE α (q τ₁ R x₁) + phiE α (q τ₂ R x₁)))
          * phiE α (q τ₂ R x₂) := by
    rw [qE_eq_ofReal_q, qE_eq_ofReal_q, qE_eq_ofReal_q, qE_eq_ofReal_q, phiE_of_lt hp2,
      phiE_of_lt hq11, phiE_of_lt hq12, phiE_of_lt hq22]
    rw [mul_comm (q τ₂ R x₂) (q τ₁ R x₂), add_comm (ENNReal.ofReal (q τ₂ R x₁)),
      add_comm (ENNReal.ofReal (phi α (q τ₂ R x₁)))] at hrow2
    calc ENNReal.ofReal (q τ₁ R x₂) * ENNReal.ofReal (q τ₂ R x₂) * rsq ^ (-α)
        = ENNReal.ofReal (q τ₂ R x₂) * ENNReal.ofReal (q τ₁ R x₂) * rsq ^ (-α) := by ring
      _ ≤ _ := hrow2
      _ = _ := by ring
  -- the overlap terms
  have hov1 : cOverlap τ₁ R x₁ x₂ * rsq ^ (-α)
      ≤ cOverlap τ₁ R x₁ x₂ * (WresD α τ₁ R x₁ * WresD α τ₂ R x₂) := by
    refine mul_le_mul_right ?_ _
    calc rsq ^ (-α) ≤ (rE τ₁ R x₁ * rE τ₂ R x₂) ^ (-α) := rpow_neg_antitone hα0 hstrE
      _ = (rE τ₁ R x₁) ^ (-α) * (rE τ₂ R x₂) ^ (-α) :=
          ENNReal.mul_rpow_of_ne_zero h11 h22 (-α)
      _ = WresD α τ₁ R x₁ * WresD α τ₂ R x₂ := by
          rw [rE_rpow_neg_eq_WresD τ₁ R x₁ h11, rE_rpow_neg_eq_WresD τ₂ R x₂ h22]
  have hov2 : cOverlap τ₂ R x₁ x₂ * rsq ^ (-α)
      ≤ cOverlap τ₂ R x₁ x₂ * (WresD α τ₂ R x₁ * WresD α τ₁ R x₂) := by
    refine mul_le_mul_right ?_ _
    calc rsq ^ (-α) ≤ (rE τ₁ R x₂ * rE τ₂ R x₁) ^ (-α) := rpow_neg_antitone hα0 hcrE
      _ = (rE τ₁ R x₂) ^ (-α) * (rE τ₂ R x₁) ^ (-α) :=
          ENNReal.mul_rpow_of_ne_zero h21 h12 (-α)
      _ = WresD α τ₂ R x₁ * WresD α τ₁ R x₂ := by
          rw [rE_rpow_neg_eq_WresD τ₁ R x₂ h21, rE_rpow_neg_eq_WresD τ₂ R x₁ h12, mul_comm]
  calc qE (prodPMF τ₁ τ₂) (SquareRel R) (x₁, x₂) * rsq ^ (-α)
      ≤ (qE τ₁ R x₁ * qE τ₂ R x₁ + qE τ₁ R x₂ * qE τ₂ R x₂
          + cOverlap τ₁ R x₁ x₂ + cOverlap τ₂ R x₁ x₂) * rsq ^ (-α) :=
        mul_le_mul_left (qE_square_two τ₁ τ₂ R x₁ x₂) _
    _ = qE τ₁ R x₁ * qE τ₂ R x₁ * rsq ^ (-α) + qE τ₁ R x₂ * qE τ₂ R x₂ * rsq ^ (-α)
          + cOverlap τ₁ R x₁ x₂ * rsq ^ (-α) + cOverlap τ₂ R x₁ x₂ * rsq ^ (-α) := by ring
    _ ≤ _ := by
        refine le_trans (add_le_add (add_le_add (add_le_add hrow1' hrow2') hov1) hov2)
          (le_of_eq ?_)
        ring

/-! ### The restricted summands -/

/-- The indicator of the doubly-positive set `F = {r_{τ₁} > 0, r_{τ₂} > 0}`. -/
private noncomputable def dpInd {X : Type} (τ₁ τ₂ : PMF X) (R : X → X → Prop) (x : X) :
    ℝ≥0∞ :=
  if rE τ₁ R x = 0 ∨ rE τ₂ R x = 0 then 0 else 1

/-- The restricted potential summand `𝟙[r_τ > 0] φ(q_τ)`. -/
private noncomputable def resPhi {X : Type} (α : ℝ) (τ : PMF X) (R : X → X → Prop) (x : X) :
    ℝ≥0∞ :=
  if rE τ R x = 0 then 0 else phiE α (q τ R x)

/-- The restricted product summand `𝟙_F φ(q_{τ₁} q_{τ₂})` of `I_i`. -/
private noncomputable def resPsi {X : Type} (α : ℝ) (τ₁ τ₂ : PMF X) (R : X → X → Prop)
    (x : X) : ℝ≥0∞ :=
  dpInd τ₁ τ₂ R x * phiE α (q τ₁ R x * q τ₂ R x)

/-- The restricted bad degree `𝟙_F q_τ`. -/
private noncomputable def resQ {X : Type} (τ₁ τ₂ τ : PMF X) (R : X → X → Prop) (x : X) :
    ℝ≥0∞ :=
  dpInd τ₁ τ₂ R x * qE τ R x

/-- The chord factor `1 + c (q_{τ₁} + q_{τ₂})` on `F`. -/
private noncomputable def chordFac {X : Type} (cb : ℝ≥0∞) (τ₁ τ₂ : PMF X) (R : X → X → Prop)
    (x : X) : ℝ≥0∞ :=
  1 + cb * (resQ τ₁ τ₂ τ₁ R x + resQ τ₁ τ₂ τ₂ R x)

/-- The weight factor `(u⁻¹ + α)(φ(q_{τ₁}) + φ(q_{τ₂}))` on the positive sets. -/
private noncomputable def weightFac {X : Type} (k : ℝ≥0∞) (α : ℝ) (τ₁ τ₂ : PMF X)
    (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  k * (resPhi α τ₁ R x + resPhi α τ₂ R x)

/-- The restricted potential is the integral of `resPhi` (`thm:four-law-contraction`). -/
private lemma PhiDres_eq_resPhi {X : Type} (α : ℝ) (ρ τ : PMF X) (R : X → X → Prop) :
    PhiDres α ρ τ R = ∑' x, ρ x * resPhi α τ R x := rfl

                                           
                                                                                  
                             
                                  

                                                        
                                                                                      
                                                   
                                           

                                                        
                                                                                       
                                                   
                                           

                                   
private lemma dpInd_eq_one {X : Type} {τ₁ τ₂ : PMF X} {R : X → X → Prop} {x : X}
    (h₁ : rE τ₁ R x ≠ 0) (h₂ : rE τ₂ R x ≠ 0) : dpInd τ₁ τ₂ R x = 1 := by
  unfold dpInd; rw [ite_eq_right (not_or.mpr ⟨h₁, h₂⟩)]

                                                  
                                                                                      
                                                                       
                                                        
              
                                                            
                           
                                              
                             
                                                     
                                                    
                               
                                
                                                                        

                        
                                                                                  
                                          
                                                         
                                                                  
                 
                                                  
                                                            
                            
                    

                                                                    
                                                                         
                                                                        
                                                                                     
             
                                                                                       
                                                                    
                                            
                                                                        
                                                              
                 
                 
                        
                                                       
                                                        
                                                        
                                       
                                       
                                                     
                                                         
                                                         
                                                                                    
                                                      
                                                          
                                                                                   
                                                                                      
                                                         
                                                                                      
                                                         
                                              
                                                                 
                                                                    
                                                             
                                                                       
                                                
                          
                                                                                           
                                                                 

                                             
                                                              
                                                                             
                                                                                         
                                        
                          
                                                                             
                                                                      
                                           
                                               
                          
                                                                             
                                             
                                                                                         
                                                       
                                                                                            
                                                                                      
                                                       
            
                                         
                                        
                                     
                                                                                
                                     
                                                                                  
                                                                         
                            
                                                                                     

                                                                              
                                                                                         
                                     
                                                                                        
                                                          
                                                                              
                            
                                                                            

                                                               
                                                                            
                        
                                                                                         
                                           
                                                          
                                                                   
                             
                                            

                               

                                                                     
                                                                 
                                                               
                                                                          
                                                    
             
                 
                      
                                                   
                                                                    
                                                                    
                     
                                                                               
                                                                   
                                                  
                                     
                                    
                                                      
                            
                     
                                                        

                                                                             
                                                           
                                                                                  
                  
                                                                          
                                                                     
                                         
                                            
                       
                                 
                                                                   
                            
                                              
                                 
                                                                   
                            
                            
                 
                                            
                                       

                                                                    
                                                                                  
             
                                                                                           
                                                                       
                        
                            
                                                                              
                                                    
                                               
                                                                                 
                                                                    
                                         
                           
                                 
                             
                               
                                          
                                                    
                                                          
                                                                           
                                                                     
                                                     
                                     
                                                     
                                             
                                                               
                                           
                                                                     
                                                             
                                                                     
                                                                     
                                                                         
                                                           
              

                                                                           
                                                                       
                                                                                         
                                                                                            
                                                                                 
                                                                  
                                                             
                                                             
                                                       
                                                           
                                
                                                                
                                        
                                                                     
                                                
                                       
                                                                                  
                                       
                                                                                        
                                                                                  
                                       
                                                                                        
                                                                     
                                                 
                                                                        
                                                      
           
                                                            
                                                                        
                                                                  
                                                            
                                                       
                                                         
                
                       
                       
                      
                                                  
                                                  
                                       
                                                                           
                                       
                                                                           
                                                              
                                                                    
                                  
                                                        
                                                                        
                                                                             
                                                                 
                                                                        
                                                
                                                                                        
                                                                                             
                                                                  
                                       
                                                                    
                                       
                                                        
                                                
              
                                                                                   
                                     
                                                                                   
                                     
                    

                                             

                                                                                       
                                                                                   
                                                                   
                                                                                        
                        
                                                           
                                                                               
                                                          
                                                             
                                                             
                                                             
                                                                   
                                         
                                                         
                                                          
                                                                
                                                         
                         
                                                                                  
                         
                                                                                  
                         
                                                                                  
                         
                                                                                        
                   
                                                                
                                    
                   
                           
                                                                                     
                                    
                                                                                    
                                                             
                                                                                     
                                                     
                                                                             
                                                                                 
                           
                                                               
                                                                                   
                            
                                                                                    
                                                             
                                                                                     
                                                     
                                                                     
                                                                                       
                                                               
                                                               
                            
                                                                                    
                                                             
                                                                                     
                                                     
                                                                     
                                                                                       
                                                               
                                           
                            
                                                                                    
                                                             
                                                                                     
                                                     
                                                                             
                                                                                 
                           
                                                                           
                            
                      
                                             
                                     
                                                                                 
                                                                             
                                          
                                                                                
                                                            
                                                                               
                    
                                          
                                                                                
                                                            
                                                                               
                    
                                          
                                                                                
                                                              
                                       
                                                            
                                          
                                                                                
                                                              
                                       
                                                            
                                                              
                                                                               
                                                         
                         
                                                                                  
                         
                                                                                  
                         
                                                                                  
                         
                                                                                         
                    
                                      
               
                                                                                   
                             

                                                    

/-- **Rows and overlaps** (`thm:four-law-contraction`): the integral of the square
potential over `F₁ × F₂` is at most the four row products of `eq:four-law-rows` and the
two overlap integrals `∫ H₁¹ H₂² dτ₁`, `∫ H₁² H₂¹ dτ₂` (`fubini_swap_two_res`). -/
private lemma main_sum_le {X : Type} {α u : ℝ} (hα : 1 ≤ α) (hu0 : 0 < u) (hu1 : u < 1)
    (ρ₁ ρ₂ τ₁ τ₂ : PMF X) (R : X → X → Prop) :
    ∑' p : X × X, prodPMF ρ₁ ρ₂ p * (dpInd τ₁ τ₂ R p.1 * dpInd τ₁ τ₂ R p.2
        * phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) p))
      ≤ (∑' x, ρ₁ x * resPsi α τ₁ τ₂ R x)
          * (∑' x, ρ₂ x * chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x)
        + PhiDres α ρ₁ τ₁ R
          * (∑' x, ρ₂ x
              * weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x)
        + (∑' x, ρ₁ x * chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x)
          * (∑' x, ρ₂ x * resPsi α τ₁ τ₂ R x)
        + (∑' x, ρ₁ x
              * weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x)
          * PhiDres α ρ₂ τ₂ R
        + (∑' y, τ₁ y * (HresD α ρ₁ τ₁ R y * HresD α ρ₂ τ₂ R y))
        + (∑' y, τ₂ y * (HresD α ρ₁ τ₂ R y * HresD α ρ₂ τ₁ R y)) := by
  have hpt : ∀ p : X × X, prodPMF ρ₁ ρ₂ p * (dpInd τ₁ τ₂ R p.1 * dpInd τ₁ τ₂ R p.2
        * phiE α (q (prodPMF τ₁ τ₂) (SquareRel R) p))
      ≤ prodPMF ρ₁ ρ₂ p * (resPsi α τ₁ τ₂ R p.1
            * chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p * (resPhi α τ₁ R p.1
            * weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p * (chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R p.1
            * resPsi α τ₁ τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p
          * (weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R p.1
            * resPhi α τ₂ R p.2)
        + prodPMF ρ₁ ρ₂ p
          * (cOverlap τ₁ R p.1 p.2 * (WresD α τ₁ R p.1 * WresD α τ₂ R p.2))
        + prodPMF ρ₁ ρ₂ p
          * (cOverlap τ₂ R p.1 p.2 * (WresD α τ₂ R p.1 * WresD α τ₁ R p.2)) := by
    rintro ⟨x₁, x₂⟩
    by_cases h1 : rE τ₁ R x₁ = 0 ∨ rE τ₂ R x₁ = 0
    · have h0 : dpInd τ₁ τ₂ R x₁ = 0 := by unfold dpInd; rw [ite_eq_left h1]
      simp only [h0, zero_mul, mul_zero]
      exact zero_le
    by_cases h2 : rE τ₁ R x₂ = 0 ∨ rE τ₂ R x₂ = 0
    · have h0 : dpInd τ₁ τ₂ R x₂ = 0 := by unfold dpInd; rw [ite_eq_left h2]
      simp only [h0, zero_mul, mul_zero]
      exact zero_le
    push Not at h1 h2
    obtain ⟨h11, h12⟩ := h1
    obtain ⟨h21, h22⟩ := h2
    have e1 : dpInd τ₁ τ₂ R x₁ = 1 := dpInd_eq_one h11 h12
    have e2 : dpInd τ₁ τ₂ R x₂ = 1 := dpInd_eq_one h21 h22
    have hmain := main_pt hα hu0 hu1 τ₁ τ₂ R x₁ x₂ h11 h12 h21 h22
    have f1 : resPsi α τ₁ τ₂ R x₁ = phiE α (q τ₁ R x₁ * q τ₂ R x₁) := by
      rw [resPsi, e1, one_mul]
    have f2 : resPsi α τ₁ τ₂ R x₂ = phiE α (q τ₁ R x₂ * q τ₂ R x₂) := by
      rw [resPsi, e2, one_mul]
    have g1 : chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x₁
        = 1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₁ + qE τ₂ R x₁) := by
      rw [chordFac, resQ, resQ, e1, one_mul, one_mul]
    have g2 : chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R x₂
        = 1 + ENNReal.ofReal (chordSlope α u) * (qE τ₁ R x₂ + qE τ₂ R x₂) := by
      rw [chordFac, resQ, resQ, e2, one_mul, one_mul]
    have p11 : resPhi α τ₁ R x₁ = phiE α (q τ₁ R x₁) := by rw [resPhi, ite_eq_right h11]
    have p12 : resPhi α τ₂ R x₁ = phiE α (q τ₂ R x₁) := by rw [resPhi, ite_eq_right h12]
    have p21 : resPhi α τ₁ R x₂ = phiE α (q τ₁ R x₂) := by rw [resPhi, ite_eq_right h21]
    have p22 : resPhi α τ₂ R x₂ = phiE α (q τ₂ R x₂) := by rw [resPhi, ite_eq_right h22]
    have w1 : weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x₁
        = (ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
          * (phiE α (q τ₁ R x₁) + phiE α (q τ₂ R x₁)) := by
      rw [weightFac, p11, p12]
    have w2 : weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R x₂
        = (ENNReal.ofReal (1 / u) + ENNReal.ofReal α)
          * (phiE α (q τ₁ R x₂) + phiE α (q τ₂ R x₂)) := by
      rw [weightFac, p21, p22]
    simp only [e1, e2, one_mul, f1, f2, g1, g2, p11, p22, w1, w2]
    refine le_trans (mul_le_mul_right hmain _) (le_of_eq ?_)
    ring
  have hov1 : ∑' p : X × X, prodPMF ρ₁ ρ₂ p
        * (cOverlap τ₁ R p.1 p.2 * (WresD α τ₁ R p.1 * WresD α τ₂ R p.2))
      = ∑' y, τ₁ y * (HresD α ρ₁ τ₁ R y * HresD α ρ₂ τ₂ R y) := by
    rw [← fubini_swap_two_res]
    exact tsum_congr fun p => by rw [prodPMF_apply]
  have hov2 : ∑' p : X × X, prodPMF ρ₁ ρ₂ p
        * (cOverlap τ₂ R p.1 p.2 * (WresD α τ₂ R p.1 * WresD α τ₁ R p.2))
      = ∑' y, τ₂ y * (HresD α ρ₁ τ₂ R y * HresD α ρ₂ τ₁ R y) := by
    rw [← fubini_swap_two_res]
    exact tsum_congr fun p => by rw [prodPMF_apply]
  refine le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ?_)
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add,
    ENNReal.tsum_add, hov1, hov2,
    tsum_mass_prod ρ₁ ρ₂ (resPsi α τ₁ τ₂ R)
      (chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R),
    tsum_mass_prod ρ₁ ρ₂ (resPhi α τ₁ R)
      (weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R),
    tsum_mass_prod ρ₁ ρ₂ (chordFac (ENNReal.ofReal (chordSlope α u)) τ₁ τ₂ R)
      (resPsi α τ₁ τ₂ R),
    tsum_mass_prod ρ₁ ρ₂
      (weightFac (ENNReal.ofReal (1 / u) + ENNReal.ofReal α) α τ₁ τ₂ R)
      (resPhi α τ₂ R),
    ← PhiDres_eq_resPhi, ← PhiDres_eq_resPhi]

/-! ### The assembly -/

                                                                                     
                                                                                
                                                                                    
                                             
                                                  
                                                         
                                                    
                                                                           
                   
                                                                 
                                                                 
                                                                   
                                                                   
                                                         
                                                         
                                                           
                                                           
                                                                     
                                                                       
                                                           
                                                                                 
                                                                      
                                                   
                                       
                                         
                                                     
                                               
                                         
                                                                
                                             
                               
                                                                                          
                                                                                           
                                        
                                                               
                                                                                            
                                                                                           
                                  
                                                      
                                                                       
                                                                               
                             
                                                                             
                                                                 
                                                                 
                                                                 
                                                                         
                                                                                         
                                                               
                                                         
                                                                         
                                                                       
                                                                                           
                           
                                                                
                                                                                        
                         
                                                                                               
                                                          
                                                                                           
                                                       
               
                                                         
                                                       
                                                          
                                             
                                                          
                                             
                                                                              
                                                              
                                               
                                                     
                                                                                     
                                  
                                                                          
                                                                              
                                                              
                                               
                                                     
                                                                                     
                                  
                                                                          
                                                    
                                                                                      
                                                    
                                                                                       
                                                    
                                                                                      
                                                    
                                                                                       
                                             
                                             
                                             
                                             
                                                                              
                                                             
                      
                                                                       
                                                                              
                                                             
                      
                                                                       
                                                                                           
                                                                     
                       
                                                 
                                                                                           
                                                                     
                       
                                                 
                                                                                        
               
                                                                                        
               
                                                                                 
                                    
                                                
                                                                         
                                                                                 
                                    
                                                
                                                                         
                                                                                 
                                    
                                                
                                                                         
                                                                                 
                                    
                                                
                                                                         
                                                                
                                          
                                                      
                                                   
                                                                
                                          
                                                      
                                                   
                                                                
                                          
                                                 
                                                        
                                                                
                                          
                                                 
                                                        
                  
                                   
                                     
                                     
                                        
                                                    
                                           
                                     
                                           
                                                                          
                                                                                 
                                                         
                                                    
                                                    
                                                       
                                                       
                                                                
                                                                
                                                     
                                                     
                                                     
                                                     
                                                                         
                                                                         
                                                                        
                                                                        
                                                                        
                                                                        
                                       
                                       
                                       
                                       
                                        
                                        
                            
                                                  
                                            
                                                                         
                                                                   
                                                 
                                                                                      
                                                                      
                                            
                                             
                                                                                 
                                                                                       
                                                       
                                                                       
                                                                                  
                                                                                        
                                                
                
                                                                   
                                                                               
                                             
                                         
                                                                         
                                                                           
                                                    
                                                                           
                                                    
                                        
                
                                         
                                                                         
                                                                                  
                                                                     
                                                                                  
                                                                     
                                        
                
                      
                                                
                                                            
                                                                     
                                            
                                                                                      
                 
                    
              

end GraphMarkovMatching.Stopped
