/-
Copyright (c) 2026 A. Fiori. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: A. Fiori
-/
import Mathlib
import ZerosInShortIntervals.Common.RealLogBounds
import ZerosInShortIntervals.Background.ExternalFacts

/-! # Shared Phragmén–Lindelöf building blocks (`\S sec:background`)

This file collects the reusable pieces needed to instantiate `fiori_phragmenLindelof`
(Fiori's Theorem 7, doi:10.1016/j.jmaa.2026.130404, available here as
`ExternalFacts.fiori_phragmenLindelof`, a theorem reading the `LiteratureInputs` field of the same
name) for the four `interpolated_bound_*` propositions in `BackgroundZetaBounds.lean`.

**Why the decomposition has the shape it does.** The paper's own worked "Third example" (§4.3) is
the direct source for `interpolated_bound_1a`, but its displayed formula
`|ζ(σ+it)| ≤ (66.7|σ+it|^{27/164})^{w_a}·(1.546|σ+it|^{1/14}|G(σ+it)|)^{w_b}` (with
`G(s)=(1/2)(log(4e+s)+log(4e+2-s))`, `w_a=(b-σ)/(b-a)`, `w_b=(σ-a)/(b-a)`) is *not* literally an
instance of `fiori_phragmenLindelof`'s conclusion for a single `r=1` function `G`: matching the
exact displayed constants forces an **`r=3`** decomposition, which reproduces
`interpolated_bound_1a`'s stated coefficients `47/123-107/246σ` and `14/3(σ-1/2)` exactly (the
resulting linear system is solved and checked in `sympy`):
* `G₁(s) = 66.7^(164/27) · s`, exponents `(α₁,β₁) = (27/164, 0)` — carries *both* the sub-Weyl
  power growth and the `66.7` constant, contributing only at the `σ=1/2` boundary (its `β₁=0`
  kills it at `σ=5/7`). Needs `|G₁|` increasing in `σ` (holds: `α₁>β₁`, `|C·s|` increasing on
  `Re s>0`).
* `G₂(s) = 1.546^14 · (Q'-s)` for any fixed `Q' > 5/7` (e.g. `Q'=1`), exponents
  `(α₂,β₂) = (0, 1/14)` — the mirror image, carrying the Yang power growth and the `1.546`
  constant, contributing only at `σ=5/7`. Needs `|G₂|` decreasing in `σ` (holds: `β₂>α₂`, `|Q'-s|`
  decreasing on `Re s<Q'`).
* `G₃ = GPL 4e`, exponents `(α₃,β₃) = (0,1)` — the log-type function, contributing only at
  `σ=5/7` (matching `log|G(σ+it)|`, i.e. `loglog|t|`, in the target).

A single `G₀ = s` with *both* `(α₀,β₀) = (27/164,1/14)` nonzero (no split) is algebraically
equivalent and reproduces the same `log|t|` coefficient; the split exists *only* to also match the
two separate boundary constants `66.7`,`1.546`, which a single scaled `s` cannot do simultaneously
at both ends, since a single scalar multiple contaminates both exponents.

`interpolated_bound_1b` reuses `G₂,G₃` verbatim but replaces `G₁` (new constant, exponent `1/6`)
and switches `G₃`'s exponents to `(α₃,β₃)=(1,1)` (**equal**, Corollary 3 / Remark 4's device for a
`G` that is not monotone in `σ`, here used deliberately: `|GPL|` is *not* known to be monotone
with the exponent pattern `1b` needs, but equal exponents make `hG_mono` hold vacuously — see
`fiori_phragmenLindelof`'s `hG_mono`, whose two implications are vacuous when `α i = β i`) — which
is also why `1b`'s `loglog|T|` coefficient is the constant `1` (`= w_a+w_b`) rather than `1a`'s
`σ`-dependent `14/3(σ-1/2)` (`= w_b·1`, since `1a` uses `α₃=0`). `interpolated_bound_1c` keeps
`G₂,G₃` as well, but its `σ=1/2` boundary bound is affine in `log|t|`, so its `G₁` is the affine
`G1shift` rather than a scaled `s`, and `G₃` keeps `(α₃,β₃)=(0,1)` with the monotonicity supplied
outright by `GPL_anti_of_large_t`; its `loglog|T|` coefficient is again the flat `1`, this time
because `G₁`'s own `log` contributes `w_a` and `G₃`'s contributes `w_b`. That case has its own
`r=4` family — see the `### Case (1c)` section below.

`interpolated_bound_2` (general `k≥4`, interpolating Yang's bound at consecutive `k,k+1`) uses the
exact same *shape*: `G₁` carries `1.546^(2^k-2)·s` with exponent `1/(2^k-2)` (only at `σ=a_k`),
`G₂` carries `1.546^(2^{k+1}-2)·(Q'-s)` with exponent `1/(2^{k+1}-2)` (only at `σ=b_k`), and
`G₃ = GPL e` with equal exponents `(1,1)`. Solving for the exponents that make the interpolation
match the stated `(1-σ)/(k-1+2^{1-k}) - 1/(2^k(k-1)+2)` coefficient exactly (matching value at
`σ=a_k` and `σ=b_k`) confirms — via `sympy`, checked at `k=4,5,6,7` — that the needed exponents
are `1/(2^k-2)` and `1/(2^{k+1}-2)`, i.e. **exactly** `ExternalFacts.yang_critical_strip_bound`'s
own *exponent* at `k` and at `k+1` respectively — not the `k/(2^k-2)` that appears in the same
statement as the abscissa `σ_k = 1 - k/(2^k-2)`.

**Proved outright here** (so that every `interpolated_bound_*` proof gets them for free):
holomorphy and conjugate symmetry of all three `G` shapes; strict monotonicity in `σ` of the two
*linear* shapes; uniform positive lower bounds for all three on the strip
(`linG_lower_const`/`linGRefl_lower_const`/`GPL_lower_const`); the reduction
`envelope_of_const_lower`, which turns "each `‖Gᵢ‖ ≥` a positive constant" plus "`f` has *some*
two-exponential envelope" into the *shared* `(C1,C2,C3)` envelope `fiori_phragmenLindelof`
demands, and its packaged form `exists_shared_envelope`; the window lemmas
`abs_log_sub_log_le'`/`abs_log_sub_log_le` and `twenty_lt_log`; the reflection
`zeta_norm_abs_im`; the Yang-interval arithmetic (`add_two_lt_two_pow`, `two_lt_two_pow`,
`half_le_sigmaYang`, `sigmaYang_mem_Ioo`, `sigmaYang_lt_succ`) and the coefficient identity
`yang_interp_coeff_eq`; and — the workhorses downstream — the `log`-form bridges
`log_bound_of_interp`, `log_bound_of_interp_1c` and `log_bound_of_interp_self`, which take the
multiplicative conclusion of `fiori_zeta_interpolation`/`fiori_zeta_interpolation_1c` to the
additive, `3/T`-slack form the four `interpolated_bound_*` propositions are stated in.

**This file contains no `sorry` and no `axiom`.** Both facts the source verifies only numerically
are proved outright — the `|t|>T0` monotonicity in `σ` of `‖GPL Q‖` (`GPL_anti_of_large_t`, which
also *corrects* the threshold from `|t|>3` to `|t|>Q+1` and restricts the range to `σ ≤ 1`) and
its `≥ log|t|` lower bound (`GPL_ge_log`, which needs no hypotheses on `σ` or `Q` at all). The
double-exponential envelope for `(s-1)ζ(s)` on each strip (`zeta_envelope`), the remaining input
to the growth hypothesis of `fiori_phragmenLindelof`, is proved too. Downstream, the compact-range
(`|t| ≤ T0`) numeric check each `interpolated_bound_*` needs is a hypothesis rather than a proof:
a field of `BackgroundZetaBounds.InterpolationCertificates` (cases 1a, 1b, 1c) or of
`BackgroundZetaBounds.Hcompact2Certificates` (case 2), each certified outside Lean by ball
arithmetic in `Code/`.

**Why `hG_conj` is scoped to the strip.** `fiori_phragmenLindelof` asks for
`Gᵢ(s̄) = conj(Gᵢ(s))` only for `s.re ∈ Set.Icc a b`, and that restriction is essential for the
log-type `G` the source's own §4 examples use: for `GPL Q` the unrestricted `∀ s : ℂ` form is
false at real `s ≤ -Q`, where `Q+s` sits on `Complex.log`'s branch cut
(`Complex.log(Q+s) = log|Q+s| + iπ`, so a `+iπ/2` term appears which cannot be
conjugation-symmetric at a point where `conj s = s`). The source scopes the condition the same way
(Theorem 1: "… holomorphic for `Re(s) ∈ [a,b]`, have `Gᵢ(s̄) = conj(Gᵢ(s))`"), and its proof of
Lemma 5 only ever evaluates `Gᵢ` inside the strip. The restriction is symmetric in `s` and
`conj s`, since `(conj s).re = s.re`, and `GPL_conj` below discharges it outright. -/

noncomputable section

open Complex

/- The half-line and critical-strip bounds this file instantiates are hypotheses, collected in the
classes `LiteratureInputs` (`ZerosInShortIntervals/Hypotheses.lean`) and `BrentStirlingInputs`
(`Background/ExternalFacts.lean`); nothing here is an `axiom`.

Lean automatically includes an instance-implicit section variable in every *theorem* in scope,
whether or not that theorem's proof reaches it (definitions are not affected).  So the
binders below appear on more statements than strictly need them; each such statement is still
true, merely stated under a hypothesis it does not use.  Precision is recovered where it matters,
on the headline results: see `ZerosInShortIntervals/AllHypotheses.lean`.  The linter that reports
the unused ones is silenced here rather than answered with hundreds of `omit` clauses. -/
set_option linter.unusedSectionVars false

variable [LiteratureInputs] [BrentStirlingInputs]

/-- `linG C Q s = C*(Q+s)`: Fiori's "standard choice (2)" `G(s)=(Q+s)` (page 2), scaled by a
positive real constant `C` so that its value at a chosen boundary point can match an arbitrary
target constant.

### Summary of Proof
Entire, hence holomorphic everywhere; `‖linG C Q‖` is strictly increasing in `Re s` on `Re s > -Q`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `exists_shared_envelope`, `fiori_zeta_interpolation`,
`fiori_zeta_interpolation_tight`, `interpG`, `interpG1c`, `interpG1c_prod_α`, `interpG1c_prod_β`,
`interpG_prod_α`, `interpG_prod_β`, `linG_conj`, `linG_holomorphicOn`, `linG_lower_const`,
`linG_mono_of_pos`. -/
def linG (C Q : ℝ) : ℂ → ℂ := fun s => (C : ℂ) * ((Q : ℂ) + s)

/-- `linGRefl C Q s = C*(Q-s)`: the mirror image of `linG`, per **Remark 6 / §2's first bullet of
Fiori's Phragmén–Lindelöf paper** (`\cite[Remark 6]{Fiori2026}`, "replace `G(s)` with `G(Q'-s)`") —
NOT this project's tex — used where a *decreasing* (in `σ`) linear `G` is needed instead.

### Summary of Proof
`‖linGRefl C Q‖` is strictly decreasing in `Re s` on `Re s < Q`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `linGRefl_holomorphicOn`, `linGRefl_conj`, `linGRefl_anti_of_pos`,
`linGRefl_lower_const`, `interpG`, `interpG1c`, and the four `fiori_zeta_interpolation*`. -/
def linGRefl (C Q : ℝ) : ℂ → ℂ := fun s => (C : ℂ) * ((Q : ℂ) - s)

/-- `GPL Q s = (1/2)(log(Q+s) + log(Q+2-s))`: the log-type function used in Fiori's "Second" (`Q=e`)
and "Third" (`Q=4e`) worked examples.

### Summary of Proof
A definition, not a theorem. `GPL Q` is the log-type auxiliary function of Fiori's worked examples,
symmetric about `σ = 1`: the two logarithms `log(Q+s)` and `log(Q+2-s)` swap when `s ↦ 2-s`. That
symmetry is what makes `‖GPL‖` monotone in `σ` away from the centre, which is the hypothesis
Phragmén–Lindelöf needs. The source uses `Q = e` in its "Second example" and `Q = 4e` in its
"Third"; this project instantiates at `Q = 4e` (cases 1a and 1c), `Q = 16` (case 1b, chosen large
enough that `GPL 16` clears that case's compact-range check) and `Q = e` (case 2).

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `G1shift`, `G1shift_conj`, `G1shift_ge`, `G1shift_holomorphicOn`, `G1shift_le`,
`G1shift_le_tight`, `G1shift_lower_const`, `G1shift_mono_of_large_t`, `GPL_anti_of_large_t`,
`GPL_conj`, `GPL_ge_log`, `GPL_holomorphicOn`, `GPL_im_eq`, `GPL_le_log`, `GPL_le_log_tight`,
`GPL_lower_const`, `GPL_mono_of_large_t`, `GPL_reSq_lt_of_large_t`, `GPL_re_eq`,
`GPL_re_mono_of_large_t`, `exists_shared_envelope`, `fiori_zeta_interpolation`,
`fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`,
`fiori_zeta_interpolation_tight`, `interpG`, `interpG1c`, `interpG_prod_α`, `interpG_prod_β`. -/
def GPL (Q : ℝ) : ℂ → ℂ :=
  fun s => (1 / 2) * (Complex.log ((Q : ℂ) + s) + Complex.log ((Q : ℂ) + 2 - s))

                                                                     

                    
                                                                                        
                                                                                                 
                                                                                              

              
                   

                
                       
                                                              
                                          
                                                                 
                                                                                                    

                                                                         

                    
                                                                                                
                                                                                              
            

              
                   

                
                           
                                                              
                                              
                                                                     
                                
                                                                       

                                                                                        

                    
                                                                                                  
                                                                                                  
                                                                                                
                                                                                         
                                                                                                   
                                                                                         
                                

              
                   

                
                      
                                                                              
                                                                               
                                                                 
            
                                                  
                                                                  
                                                                      
                                                                                
                                             
                  
                                                                                    
                                             
                  
                                                          

                                                                       

                    
                                                                                                   
                                                                                            
                                                                                                  
                                     

              
                   

                
                       
                                                              
                                     
                                                                 
                               

                                                                           

                    
                                                                                          
                                                                                       
                                    

              
                   

                
                           
                                                              
                                         
                                                                         
                                   

                                                                                               
                                                                                             
                                                                                          
                                                               

                    
                                                                                             
                                                                                                  
                                                                                               
                                                                                                   
                                                                                           

              
                   

                
                      
                                                                                       
                                                                         
                                                                                              
                                                           
                                                                         
                  
                                                                                 
                                      
                                                       
                                      
                     
                                                           
                                      
                     
                                                          
                                     
                                                               
                                                    
                                                                                               
                                                                                          

/-- `σ ↦ ‖linG C Q (σ+it)‖` is strictly increasing on `[a,b]`, for `C > 0` and `-Q < a`.

### Summary of Proof
This is the monotonicity `fiori_phragmenLindelof` (`\cite[Theorem 7]{Fiori2026}`) requires of each
`Gᵢ` along the real direction — it is what makes the interpolated bound decrease across the strip.
**Proof.** Write `linG C Q (σ+it) = C(Q+σ) + (Ct)i`, so `‖·‖ = √((C(Q+σ))² + (Ct)²)` with the
imaginary part `Ct` independent of `σ`. The hypotheses give `C(Q+σ) ≥ 0` on `[a,b]` and strict
monotonicity of `σ ↦ C(Q+σ)`, so `gcongr` closes it. No tex counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `linG`.
**Used by:** the four `fiori_zeta_interpolation*` theorems. -/
theorem linG_mono_of_pos (C Q a b : ℝ) (hC : 0 < C) (ha : -Q < a) (t : ℝ) :
    StrictMonoOn (fun σ : ℝ => ‖linG C Q (σ + t * Complex.I)‖) (Set.Icc a b) := by
  intro x hx y hy hxy
  have hx' : -Q < x := lt_of_lt_of_le ha hx.1
  have key : ∀ σ : ℝ,
      linG C Q (σ + t * Complex.I) = (C * (Q + σ) : ℝ) + (C * t : ℝ) * Complex.I := by
    intro σ
    simp only [linG]
    push_cast
    ring
  simp only [key, Complex.norm_add_mul_I]
  have h0 : 0 ≤ C * (Q + x) := by nlinarith
  have h1 : C * (Q + x) < C * (Q + y) := by nlinarith
  gcongr

/-- `σ ↦ ‖linGRefl C Q (σ+it)‖` is strictly *decreasing* on `[a,b]`, for `C > 0` and `b < Q`.

### Summary of Proof
The mirror of `linG_mono_of_pos`, and the reason `linGRefl` exists: `fiori_phragmenLindelof`
(`\cite[Theorem 7]{Fiori2026}`) is applied with a family of `Gᵢ` of *both* monotonicity senses, so
that the interpolation can be pinned at either end of the strip. **Proof.** Same shape as
`linG_mono_of_pos`: `linGRefl C Q (σ+it) = C(Q-σ) + (-Ct)i`, the imaginary part is `σ`-independent,
and `hb : b < Q` gives `C(Q-σ) ≥ 0` on `[a,b]` with `σ ↦ C(Q-σ)` strictly decreasing. No tex
counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `linGRefl`.
**Used by:** the four `fiori_zeta_interpolation*` theorems. -/
theorem linGRefl_anti_of_pos (C Q a b : ℝ) (hC : 0 < C) (hb : b < Q) (t : ℝ) :
    StrictAntiOn (fun σ : ℝ => ‖linGRefl C Q (σ + t * Complex.I)‖) (Set.Icc a b) := by
  intro x hx y hy hxy
  have hy' : y < Q := lt_of_le_of_lt hy.2 hb
  have key : ∀ σ : ℝ,
      linGRefl C Q (σ + t * Complex.I) = (C * (Q - σ) : ℝ) + (-(C * t) : ℝ) * Complex.I := by
    intro σ
    simp only [linGRefl]
    push_cast
    ring
  simp only [key, Complex.norm_add_mul_I]
  have h0 : 0 ≤ C * (Q - y) := by nlinarith
  have h1 : C * (Q - y) < C * (Q - x) := by nlinarith
  gcongr

/-! ### `Re`, `Im` and monotonicity of `GPL`

Both facts the source verifies numerically — that `‖GPL Q(σ+it)‖` decreases in `σ` for large `|t|`,
and that it is at least `log|t|` — are proved here in closed form. Writing `A = Q+σ`, `B = Q+2-σ`
(so `A+B = 2Q+2` is independent of `σ`, `AB = (Q+1)² - (1-σ)²`, and `B-A = 2(1-σ)`):

  `Re GPL Q(σ+it) = ¼(log(A²+t²) + log(B²+t²))`,
  `Im GPL Q(σ+it) = ½(arctan(t/A) - arctan(t/B))`.

`GPL_ge_log` is then immediate from `‖z‖ ≥ Re z` and `A²+t², B²+t² ≥ t²`. For
`GPL_anti_of_large_t`, both `Re` and `|Im|` are shown to decrease in `σ` on `σ ≤ 1`. -/

/-- Squaring preserves `≤` on the nonnegatives: `0 ≤ u ≤ v` gives `u² ≤ v²`.

### Summary of Proof
Discharged by `nlinarith`. No tex counterpart — arithmetic plumbing for the `GPL` monotonicity
proofs, where `Re GPL` is compared through squares of `A = Q+σ` and `B = Q+2-σ`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_anti_of_large_t`, `GPL_mono_of_large_t`. -/
private theorem sq_le_sq_of_nonneg {u v : ℝ} (h1 : 0 ≤ u) (h2 : u ≤ v) : u^2 ≤ v^2 := by nlinarith

/-- The nonpositive mirror of `sq_le_sq_of_nonneg`: `v ≤ u ≤ 0` gives `u² ≤ v²`.

### Summary of Proof
Squaring reverses the order below `0`, so the hypothesis is `v ≤ u` rather than `u ≤ v`. Both signs
are needed because `B - A = 2(1-σ)` changes sign as `σ` crosses `1`. No tex counterpart.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_anti_of_large_t`, `GPL_mono_of_large_t`. -/
private theorem sq_le_sq_of_nonpos {u v : ℝ} (h1 : u ≤ 0) (h2 : v ≤ u) : u^2 ≤ v^2 := by nlinarith

/-- `t/d ≤ t/c` for `0 ≤ t` and `0 < c ≤ d`: enlarging a positive denominator shrinks a nonnegative
quotient.

### Summary of Proof
Proved by clearing denominators with `div_le_div_iff₀`. No tex counterpart — used on the
`arctan(t/A)` arguments, where `A` grows with `σ`.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_anti_of_large_t`, `GPL_mono_of_large_t`. -/
private theorem div_antitone_of_nonneg {t c d : ℝ} (ht : 0 ≤ t) (hc : 0 < c) (hd : 0 < d)
    (h : c ≤ d) : t / d ≤ t / c := by
  rw [div_le_div_iff₀ hd hc]; nlinarith

/-- The `t ≤ 0` mirror of `div_antitone_of_nonneg`: for a nonpositive numerator the inequality
flips,
`t/c ≤ t/d`.

### Summary of Proof
Paired with it so the `Im GPL` estimates hold for both signs of `t`. No tex counterpart.
### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_anti_of_large_t`, `GPL_mono_of_large_t`. -/
private theorem div_monotone_of_nonpos {t c d : ℝ} (ht : t ≤ 0) (hc : 0 < c) (hd : 0 < d)
    (h : c ≤ d) : t / c ≤ t / d := by
  rw [div_le_div_iff₀ hc hd]; nlinarith

/-- `arg z = arctan(Im z/Re z)` in the right half-plane (from `Complex.tan_arg` and
`Real.arctan_tan`, valid because `|arg z| < π/2` there).

### Summary of Proof
In the open right half-plane `arg z` lies in `(-π/2, π/2)`, by `Complex.abs_arg_lt_pi_div_two_iff`.
On that range `arctan` inverts `tan`, so rewriting `Complex.tan_arg` and applying `Real.arctan_tan`
gives the closed form.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_im_eq`. -/
private theorem arg_eq_arctan {z : ℂ} (hz : 0 < z.re) : z.arg = Real.arctan (z.im / z.re) := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [abs_lt] at h
  rw [← Complex.tan_arg, Real.arctan_tan h.1 h.2]

/-- `‖z‖ = √((Re z)² + (Im z)²)` — the real-coordinate form of the complex modulus. Obtained by
rewriting `z` as `Re z + (Im z)i` (`Complex.re_add_im`) and applying `Complex.norm_add_mul_I`.

### Summary of Proof
Mathlib states the modulus via `Complex.abs`/`normSq`; this spelling is what the `nlinarith` calls
in the `GPL` estimates need, since they reason about `Re` and `Im` as independent reals. No tex
counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_anti_of_large_t`, `GPL_le_log_tight`, `GPL_mono_of_large_t`,
`normSq_c_mul_add_d`. -/
private theorem norm_eq_sqrt (z : ℂ) : ‖z‖ = Real.sqrt (z.re^2 + z.im^2) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.norm_add_mul_I]

/-- `Re GPL Q(σ+it) = ¼(log((Q+σ)²+t²) + log((Q+2-σ)²+t²))` — `Complex.log_re` plus `log√u = ½log
u`.

### Summary of Proof
No hypotheses: `(Complex.log z).re = log‖z‖` holds unconditionally.
### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`.
**Used by:** `G1shift_ge`, `GPL_anti_of_large_t`, `GPL_le_log`, `GPL_le_log_tight`,
`GPL_reSq_lt_of_large_t`, `GPL_re_mono_of_large_t`. -/
theorem GPL_re_eq (Q σ t : ℝ) :
    (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      = (1/4) * (Real.log ((Q+σ)^2 + t^2) + Real.log ((Q+2-σ)^2 + t^2)) := by
  have e1 : (Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I) = ((Q + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
    push_cast; ring
  have e2 : (Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)
      = ((Q + 2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hs1 : Real.log ‖((Q + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I‖
      = (1/2) * Real.log ((Q+σ)^2 + t^2) := by
    rw [Complex.norm_add_mul_I, Real.log_sqrt (by positivity)]
    ring
  have hs2 : Real.log ‖((Q + 2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I‖
      = (1/2) * Real.log ((Q+2-σ)^2 + t^2) := by
    rw [Complex.norm_add_mul_I, Real.log_sqrt (by positivity)]
    ring_nf
  simp only [GPL, Complex.mul_re, Complex.add_re, Complex.log_re]
  rw [e1, e2, hs1, hs2]
  norm_num
  ring

/-- `Im GPL Q(σ+it) = ½(arctan(t/(Q+σ)) - arctan(t/(Q+2-σ)))`, valid where both factors lie in the
right half-plane.

### Summary of Proof
Split `GPL` into its two logarithms and take imaginary parts. Writing each argument in the form `x
+ yi` with `x > 0` puts it in the right half-plane, where `arg_eq_arctan` applies; the second
logarithm's argument is `(Q+2-σ) - ti`, contributing `arctan(-t/(Q+2-σ)) = -arctan(t/(Q+2-σ))`. The
overall factor `1/2` from `GPL`'s definition gives the stated form.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `arg_eq_arctan`.
**Used by:** `GPL_anti_of_large_t`, `GPL_le_log`, `GPL_le_log_tight`, `GPL_mono_of_large_t`. -/
theorem GPL_im_eq (Q σ t : ℝ) (h1 : 0 < Q + σ) (h2 : 0 < Q + 2 - σ) :
    (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).im
      = (1/2) * (Real.arctan (t / (Q + σ)) - Real.arctan (t / (Q + 2 - σ))) := by
  have e1 : (Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I) = ((Q + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
    push_cast; ring
  have e2 : (Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)
      = ((Q + 2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have ha1 : (((Q + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I).arg = Real.arctan (t / (Q + σ)) := by
    rw [arg_eq_arctan (by simpa using h1)]
    congr 1; simp
  have ha2 : (((Q + 2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I).arg
      = Real.arctan (-(t / (Q + 2 - σ))) := by
    rw [arg_eq_arctan (by simpa using h2)]
    congr 1
    simp
    ring
  simp only [GPL, Complex.mul_im, Complex.add_im, Complex.log_im]
  rw [e1, e2, ha1, ha2, Real.arctan_neg]
  norm_num
  ring

                                                                                     
                                                                                      

                    
                                                                                            
                                                                                                  
                                                                                               
                                                                                              
                                                                                                   
                                                                                                  
                                                                                                  
                                                                                               
                                                                                                 
                                                                                             
                                                                                                   
                                                                                                
                                                                                                
                                                                                                 
                                                                                           

              
                   

                
                                                                          
                                                                                     
                                                                                             
                                 
                                                                                     
                          
                                                                                 
                           
                                         
                                
                                                   
                         
                                            
                                      
                                            
                                                                  
                                                                  
                                          
                                          
                              
                                                    
                                                                                             
                                                              
                                                     
                                                                                      
                                                                                
                                         
                                                              
                                               
                       
                                                                
                                                               
                                                       
                                                     
                                               
                                                                            
                                                                   
                                                                       
                                                     
                                                         
                                                        
                             
                              
                              
                                                         
                                                        
                                                             
                                      
                                            
                                                          
                                                    
                                                          
                                                
                                                          
                                     
                                      
                                                           
                                            
                                                             
                                                    
                                                             
                                                
                                                             
                                     
                                      
                                                           
                  
           
                                 
                                         
                                          

/-- **Shared `Re`-comparison step for `GPL_mono_of_large_t`/`GPL_re_mono_of_large_t`.** Extracted
since both the norm- and the bare-`Re`-monotonicity statements for `σ ≥ 1` need exactly this.

### Summary of Proof
The shared `Re`-comparison step behind both monotonicity lemmas. `Re GPL` is `½(log‖Q+s‖ +
log‖Q+2-s‖)`, so comparing at `x < y` reduces to comparing `((Q+x)²+t²)((Q+2-x)²+t²)` against the
same at `y`. Expanding, the difference is governed by `t²` against the `σ`-dependent quadratic
terms, so the hypothesis `Q+1 < |t|` is exactly what makes the `t²` term dominate and fixes the
sign.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_re_eq`.
**Used by:** `GPL_mono_of_large_t`, `GPL_re_mono_of_large_t`. -/
private theorem GPL_reSq_lt_of_large_t {Q a b x y t : ℝ} (hQ : 0 ≤ Q) (ha : 1 ≤ a)
    (_hQb : 0 < Q + 2 - b) (htQ : Q + 1 < |t|) (hx : x ∈ Set.Icc a b) (_hy : y ∈ Set.Icc a b)
    (hxy : x < y) :
    (GPL Q ((x:ℂ) + (t:ℂ) * Complex.I)).re ^ 2 < (GPL Q ((y:ℂ) + (t:ℂ) * Complex.I)).re ^ 2 := by
  have hQ0 : (0:ℝ) ≤ Q + 1 := by linarith
  have ht2 : (Q+1)^2 < t^2 := by
    calc (Q+1)^2 < |t|^2 := by nlinarith [htQ, hQ0]
      _ = t^2 := sq_abs t
  have hQ1 : (1:ℝ) ≤ (Q+1)^2 := by nlinarith
  have ht0 : (0:ℝ) < t^2 := by linarith
  have hx1 : (1:ℝ) ≤ x := le_trans ha hx.1
  have hy1 : (1:ℝ) < y := lt_of_le_of_lt hx1 hxy
  have hAB : (0:ℝ) < (Q+x)*(Q+2-x) - (Q+y)*(Q+2-y) := by
    nlinarith [mul_pos (show (0:ℝ) < y - x by linarith) (show (0:ℝ) < x + y - 2 by linarith)]
  have hABle : (Q+x)*(Q+2-x) + (Q+y)*(Q+2-y) - 2*t^2 < 0 := by
    nlinarith [sq_nonneg (1-x), sq_nonneg (1-y), ht2]
  have hprod : ((Q+x)^2+t^2) * ((Q+2-x)^2+t^2) < ((Q+y)^2+t^2) * ((Q+2-y)^2+t^2) := by
    have key : ((Q+y)^2+t^2) * ((Q+2-y)^2+t^2) - ((Q+x)^2+t^2) * ((Q+2-x)^2+t^2)
        = ((Q+x)*(Q+2-x) - (Q+y)*(Q+2-y))
          * (2*t^2 - ((Q+x)*(Q+2-x) + (Q+y)*(Q+2-y))) := by ring
    have hDE := mul_pos hAB (by linarith : (0:ℝ) < 2*t^2 - ((Q+x)*(Q+2-x) + (Q+y)*(Q+2-y)))
    linarith [key, hDE]
  have hne1 : ((Q+x)^2+t^2 : ℝ) ≠ 0 := by positivity
  have hne2 : ((Q+2-x)^2+t^2 : ℝ) ≠ 0 := by positivity
  have hne3 : ((Q+y)^2+t^2 : ℝ) ≠ 0 := by positivity
  have hne4 : ((Q+2-y)^2+t^2 : ℝ) ≠ 0 := by positivity
  have hlogx : Real.log ((Q+x)^2+t^2) + Real.log ((Q+2-x)^2+t^2)
      < Real.log ((Q+y)^2+t^2) + Real.log ((Q+2-y)^2+t^2) := by
    rw [← Real.log_mul hne1 hne2, ← Real.log_mul hne3 hne4]
    exact Real.log_lt_log (by positivity) hprod
  have hRexpos : 0 ≤ Real.log ((Q+x)^2+t^2) + Real.log ((Q+2-x)^2+t^2) := by
    have h1 : (1:ℝ) ≤ (Q+x)^2+t^2 := by nlinarith [sq_nonneg (Q+x)]
    have h2 : (1:ℝ) ≤ (Q+2-x)^2+t^2 := by nlinarith [sq_nonneg (Q+2-x)]
    linarith [Real.log_nonneg h1, Real.log_nonneg h2]
  rw [GPL_re_eq, GPL_re_eq]
  nlinarith [hlogx, hRexpos]

/-- **`‖GPL Q(σ+it)‖` is strictly increasing in `σ` on any `[a,b]` with `1 ≤ a`, once `|t| > Q+1`.**
The mirror of `GPL_anti_of_large_t` on the other side of the symmetry point `σ = 1`: the `Im`
comparison carries over with only the sign of the bracket flipped (it uses just that `Q+σ`
increases and `Q+2-σ` decreases in `σ`, true on both sides of `1`), while the `Re` comparison
reverses, since `AB = (Q+1)²-(1-σ)²` now *decreases* in `σ` (as `(1-σ)² = (σ-1)²` increases for
`σ ≥ 1`) instead of increasing.

### Summary of Proof
Compare the two components separately and recombine through `norm_eq_sqrt`: the squared norm is
`(Re)² + (Im)²`, so it suffices that `(Re)²` strictly increase while `(Im)²` does not decrease.
The `Re` half is `GPL_reSq_lt_of_large_t`, which is where `Q+1 < |t|` is used. The `Im` half
rewrites both sides with `GPL_im_eq` and compares the two `arctan` arguments monotonically
(`div_antitone_of_nonneg`/`div_monotone_of_nonpos` and `Real.arctan_mono`), the sign of the
bracket `arctan(t/(Q+σ)) - arctan(t/(Q+2-σ))` selecting `sq_le_sq_of_nonneg` or
`sq_le_sq_of_nonpos`; `Real.sqrt_lt_sqrt` transfers the strict inequality back to the norms.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_im_eq`, `GPL_reSq_lt_of_large_t`, `div_antitone_of_nonneg`,
`div_monotone_of_nonpos`, `norm_eq_sqrt`, `sq_le_sq_of_nonneg`, `sq_le_sq_of_nonpos`.
**Used by:** `G1shift_mono_of_large_t`. -/
theorem GPL_mono_of_large_t (Q a b : ℝ) (hQ : 0 ≤ Q) (ha : 1 ≤ a) (hQb : 0 < Q + 2 - b) :
    ∀ t : ℝ, Q + 1 < |t| →
      StrictMonoOn (fun σ : ℝ => ‖GPL Q (σ + t * Complex.I)‖) (Set.Icc a b) := by
  intro t htQ x hx y hy hxy
  have hx1 : (1:ℝ) ≤ x := le_trans ha hx.1
  have hy1 : (1:ℝ) < y := lt_of_le_of_lt hx1 hxy
  have hpx1 : 0 < Q + x := by linarith
  have hpy1 : 0 < Q + y := by linarith
  have hpx2 : 0 < Q + 2 - x := lt_of_lt_of_le hQb (by linarith [hx.2])
  have hpy2 : 0 < Q + 2 - y := lt_of_lt_of_le hQb (by linarith [hy.2])
  have hReSq := GPL_reSq_lt_of_large_t (Q := Q) (a := a) (b := b) hQ ha hQb htQ hx hy hxy
  -- ** the `Im` comparison.** The monotonicity of the two `arctan` arguments (`Q+σ` increasing,
  -- `Q+2-σ` decreasing in `σ`) is the same on both sides of `1`, but which side of `0` the
  -- bracket `arctan(t/(Q+σ))-arctan(t/(Q+2-σ))` sits on *flips* for `σ ≥ 1` versus `σ ≤ 1`
  -- (at `σ = 1` the bracket is exactly `0`; for `σ ≥ 1`, `Q+2-σ ≤ Q+σ`, the opposite ordering
  -- from the `σ ≤ 1` case), so the `t ≥ 0`/`t < 0` branches swap which `sq_le_sq_of_*` applies.
  have hImsq : ((GPL Q ((x:ℂ) + (t:ℂ) * Complex.I)).im)^2
      ≤ ((GPL Q ((y:ℂ) + (t:ℂ) * Complex.I)).im)^2 := by
    rw [GPL_im_eq Q x t hpx1 hpx2, GPL_im_eq Q y t hpy1 hpy2]
    rcases le_or_gt 0 t with htp | htn
    · have m1 : t / (Q + y) ≤ t / (Q + x) :=
        div_antitone_of_nonneg htp hpx1 hpy1 (by linarith)
      have m2 : t / (Q + 2 - x) ≤ t / (Q + 2 - y) :=
        div_antitone_of_nonneg htp hpy2 hpx2 (by linarith)
      have m3 : t / (Q + x) ≤ t / (Q + 2 - x) :=
        div_antitone_of_nonneg htp hpx2 hpx1 (by linarith [hx1])
      refine sq_le_sq_of_nonpos ?_ ?_
      · linarith [Real.arctan_mono m3]
      · linarith [Real.arctan_mono m1, Real.arctan_mono m2]
    · have m1 : t / (Q + x) ≤ t / (Q + y) :=
        div_monotone_of_nonpos htn.le hpx1 hpy1 (by linarith)
      have m2 : t / (Q + 2 - y) ≤ t / (Q + 2 - x) :=
        div_monotone_of_nonpos htn.le hpy2 hpx2 (by linarith)
      have m3 : t / (Q + 2 - x) ≤ t / (Q + x) :=
        div_monotone_of_nonpos htn.le hpx2 hpx1 (by linarith [hx1])
      refine sq_le_sq_of_nonneg ?_ ?_
      · linarith [Real.arctan_mono m3]
      · linarith [Real.arctan_mono m1, Real.arctan_mono m2]
  -- ** combine **
  simp only
  rw [norm_eq_sqrt, norm_eq_sqrt]
  apply Real.sqrt_lt_sqrt (by positivity)
  exact add_lt_add_of_lt_of_le hReSq hImsq

/-- **`‖GPL Q(σ+it)‖ ≥ log|t|` for `1 ≤ |t|`.** The source verifies this numerically; it is proved
here in closed form, and needs **no** hypotheses on `σ` or `Q` at all (the source's `0<σ<2` and
`t≥3` are both unnecessary).

### Summary of Proof
Along the author's own suggested line: `Re log z = log‖z‖`, so `‖GPL Q(σ+it)‖ ≥ Re GPL Q(σ+it) =
½(log‖(Q+σ)+it‖ + log‖(Q+2-σ)-it‖) ≥ ½(log|t| + log|t|)`, each norm being `√(·² + t²) ≥ |t|`.
### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`.
**Used by:** `interpolated_bound_1a`, `interpolated_bound_1a_tight`, `interpolated_bound_1b`,
`interpolated_bound_1b_tight`, `interpolated_bound_1c`, `interpolated_bound_1c_tight`,
`interpolated_bound_2`, `interpolated_bound_2_tight`. -/
theorem GPL_ge_log (Q a b : ℝ) (t : ℝ) (ht : 1 ≤ |t|) :
    ∀ σ ∈ Set.Icc a b, Real.log |t| ≤ ‖GPL Q (σ + t * Complex.I)‖ := by
  intro σ _
  have ht0 : (0:ℝ) < |t| := by linarith
  -- the two factors, in `x + y*I` form
  have e1 : (Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I) = ((Q + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
    push_cast; ring
  have e2 : (Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)
      = ((Q + 2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hn1 : |t| ≤ ‖(Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
    rw [e1, Complex.norm_add_mul_I]
    rw [show |t| = Real.sqrt (t^2) from (Real.sqrt_sq_eq_abs t).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (Q + σ)]
  have hn2 : |t| ≤ ‖(Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by
    rw [e2, Complex.norm_add_mul_I]
    rw [show |t| = Real.sqrt (t^2) from (Real.sqrt_sq_eq_abs t).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (Q + 2 - σ)]
  have hl1 : Real.log |t| ≤ Real.log ‖(Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I)‖ :=
    Real.log_le_log ht0 hn1
  have hl2 : Real.log |t| ≤ Real.log ‖(Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)‖ :=
    Real.log_le_log ht0 hn2
  have hre : (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      = (1/2) * (Real.log ‖(Q : ℂ) + ((σ:ℂ) + (t:ℂ) * Complex.I)‖
        + Real.log ‖(Q : ℂ) + 2 - ((σ:ℂ) + (t:ℂ) * Complex.I)‖) := by
    simp [GPL, Complex.add_re, Complex.log_re, Complex.mul_re]
  have hle := Complex.re_le_norm (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I))
  rw [hre] at hle
  linarith

/-- **`(GPL Q(σ+it)).re` is strictly increasing in `σ` on `[a,b]` with `1 ≤ a`, once `|t| > Q+1`.**
From `GPL_reSq_lt_of_large_t` (`Re²` increasing) plus positivity of `Re` there
(`Re ≥ log|t| > 0`, since `|t| > Q+1 ≥ 1`), which lets `Re²` increasing upgrade to `Re` itself
increasing.

### Summary of Proof
The real-part-only version, needed where Phragmén–Lindelöf's monotonicity hypothesis is stated on
`Re G` rather than `‖G‖`. Immediate from `GPL_reSq_lt_of_large_t` once one knows `Re GPL ≥ log|t| >
0`, since squaring is strictly monotone on the positives.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_reSq_lt_of_large_t`, `GPL_re_eq`.
**Used by:** `G1shift_mono_of_large_t`. -/
theorem GPL_re_mono_of_large_t (Q a b : ℝ) (hQ : 0 ≤ Q) (ha : 1 ≤ a) (hQb : 0 < Q + 2 - b) :
    ∀ t : ℝ, Q + 1 < |t| →
      StrictMonoOn (fun σ : ℝ => (GPL Q (σ + t * Complex.I)).re) (Set.Icc a b) := by
  intro t htQ x hx y hy hxy
  have hReSq := GPL_reSq_lt_of_large_t (Q := Q) (a := a) (b := b) hQ ha hQb htQ hx hy hxy
  have ht1 : (1:ℝ) < |t| := by linarith
  have hlogpos : (0:ℝ) < Real.log |t| := Real.log_pos ht1
  have hgre : ∀ σ : ℝ, Real.log |t| ≤ (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re := by
    intro σ
    rw [GPL_re_eq]
    have h1 : t ^ 2 ≤ (Q + σ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + σ)]
    have h2 : t ^ 2 ≤ (Q + 2 - σ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + 2 - σ)]
    have ht0 : (0:ℝ) < t ^ 2 := by nlinarith [sq_abs t]
    have hlt : Real.log (t^2) ≤ Real.log ((Q + σ) ^ 2 + t ^ 2) := Real.log_le_log ht0 h1
    have hlt2 : Real.log (t^2) ≤ Real.log ((Q + 2 - σ) ^ 2 + t ^ 2) := Real.log_le_log ht0 h2
    have he2 : Real.log (t^2) = 2 * Real.log |t| := by
      rw [← sq_abs t, Real.log_pow]; push_cast; ring
    linarith
  have hrex : 0 < (GPL Q ((x:ℂ) + (t:ℂ) * Complex.I)).re := lt_of_lt_of_le hlogpos (hgre x)
  have hrey : 0 < (GPL Q ((y:ℂ) + (t:ℂ) * Complex.I)).re := lt_of_lt_of_le hlogpos (hgre y)
  change (GPL Q ((x:ℂ) + (t:ℂ) * Complex.I)).re < (GPL Q ((y:ℂ) + (t:ℂ) * Complex.I)).re
  nlinarith [hReSq, hrex, hrey]

/-- `arctan` is `1`-Lipschitz: `|arctan x - arctan y| ≤ |x - y|`.

### Summary of Proof
**Proof.** `arctan' z = 1/(1+z²)`, whose norm is at most `1` everywhere since `z² ≥ 0`; the mean
value inequality on the (convex) whole line, in the form
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`, converts that derivative bound into the
Lipschitz estimate. No tex counterpart — Fiori's paper uses the Lipschitz property of `arctan`
implicitly. Note this naive bound is *not* enough for `GPL_le_log_tight` on its own: applied
directly to `arctan(t/A) - arctan(t/B)` it gives `|t||B-A|/(AB)`, which grows with `|t|`. It
becomes useful only after `arctan_div_swap` inverts the arguments.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_le_log`, `GPL_le_log_tight`. -/
private theorem abs_arctan_sub_arctan_le (x y : ℝ) :
    |Real.arctan x - Real.arctan y| ≤ |x - y| := by
  have hd : ∀ z ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt Real.arctan (1 / (1 + z^2)) Set.univ z :=
    fun z _ => (Real.hasDerivAt_arctan z).hasDerivWithinAt
  have hb : ∀ z ∈ (Set.univ : Set ℝ), ‖(1 : ℝ) / (1 + z^2)‖ ≤ 1 := by
    intro z _
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
    nlinarith [sq_nonneg z]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- **The argument-inversion identity that makes the `Im GPL` bound useful.**
`arctan(t/A) - arctan(t/B) = arctan(B/t) - arctan(A/t)` for `A, B > 0` and `t ≠ 0`.

### Summary of Proof
**Proof.** `t/A = (A/t)⁻¹`, and `arctan x⁻¹ = ±π/2 - arctan x` (`Real.arctan_inv_of_pos` /
`Real.arctan_inv_of_neg` according to the sign of `t`). The two `±π/2` terms cancel in the
difference, leaving the swapped form. The case split on `sign t` is exactly why both `arctan_inv`
lemmas appear. **Why it matters.** The naive Lipschitz bound on the left-hand side is
`|t||B-A|/(AB)`, which *grows* with `|t|` and so is worthless for the large-`|t|` regime the
interpolation needs. On the right-hand side the same Lipschitz bound gives `|B-A|/|t|`, which
decays. This swap is what turns the `Im` contribution into an `O(1/|t|)` error term. No tex
counterpart — the source performs the estimate without naming the step.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `GPL_le_log`, `GPL_le_log_tight`. -/
private theorem arctan_div_swap {A B t : ℝ} (hA : 0 < A) (hB : 0 < B) (ht : t ≠ 0) :
    Real.arctan (t / A) - Real.arctan (t / B)
      = Real.arctan (B / t) - Real.arctan (A / t) := by
  have hA' : t / A = (A / t)⁻¹ := by field_simp
  have hB' : t / B = (B / t)⁻¹ := by field_simp
  rcases lt_or_gt_of_ne ht with h | h
  · rw [hA', hB', Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hA h),
      Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hB h)]; ring
  · rw [hA', hB', Real.arctan_inv_of_pos (div_pos hA h),
      Real.arctan_inv_of_pos (div_pos hB h)]; ring

/-- **Upper counterpart of `GPL_ge_log`**: `‖GPL Q(σ+it)‖ ≤ log|t| + (A²+B²)/(4t²) + |B-A|/(2|t|)`
for `|t| ≥ 1`, where `A = Q+σ`, `B = Q+2-σ`. This is the missing half of Fiori's `Cᵢ(t₀) → 1`
bookkeeping (§4.1): together with `GPL_ge_log` it pins `‖GPL Q(σ+it)‖` between `log|t|` and
`(1+ε)log|t|` with an explicit `ε = O(1/(|t|log|t|))`.

### Summary of Proof
`Re` is bounded by `log(1+x) ≤ x` applied to `(A²+t²)/t²`. For `Im` the naive Lipschitz bound
`|arctan(t/A) - arctan(t/B)| ≤ |t||B-A|/(AB)` is useless (it *grows* with `|t|`); the fix is
`arctan(t/A) - arctan(t/B) = arctan(B/t) - arctan(A/t)` (`arctan_div_swap`, from
`Real.arctan_inv_of_pos`/`_of_neg` — it holds for **both** signs of `t`), after which
1-Lipschitzness gives the correct `|B-A|/|t|`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_im_eq`, `GPL_re_eq`, `abs_arctan_sub_arctan_le`, `arctan_div_swap`.
**Used by:** `G1shift_le`, `fiori_zeta_interpolation`, `fiori_zeta_interpolation_1c`. -/
theorem GPL_le_log (Q σ t : ℝ) (h1 : 0 < Q + σ) (h2 : 0 < Q + 2 - σ) (ht : 1 ≤ |t|) :
    ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      ≤ Real.log |t| + ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2) + |2 - 2*σ| / (2 * |t|) := by
  have ht0 : (0:ℝ) < |t| := by linarith
  have htne : t ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  have ht2 : (1:ℝ) ≤ t^2 := by nlinarith [sq_abs t]
  have habs2 : |t|^2 = t^2 := sq_abs t
  -- real part
  have hre : (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      ≤ Real.log |t| + ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2) := by
    rw [GPL_re_eq]
    have key : ∀ C : ℝ, Real.log (C^2 + t^2) ≤ 2 * Real.log |t| + C^2 / t^2 := by
      intro C
      have hlog : Real.log (C^2 + t^2) = Real.log (t^2) + Real.log (1 + C^2/t^2) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
        ring
      have h2t : Real.log (t^2) = 2 * Real.log |t| := by
        rw [← habs2, Real.log_pow]
        push_cast; ring
      have hb : Real.log (1 + C^2/t^2) ≤ C^2/t^2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + C^2/t^2 by positivity)
        linarith
      rw [hlog, h2t]; linarith
    have k1 := key (Q+σ)
    have k2 := key (Q+2-σ)
    have hpos : (0:ℝ) < t^2 := by linarith
    have he : ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2)
        = (1/4) * ((Q+σ)^2/t^2 + (Q+2-σ)^2/t^2) := by field_simp
    rw [he]
    linarith [k1, k2]
  -- imaginary part
  have him : |(GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).im| ≤ |2 - 2*σ| / (2 * |t|) := by
    rw [GPL_im_eq Q σ t h1 h2, arctan_div_swap h1 h2 htne, abs_mul]
    have h := abs_arctan_sub_arctan_le ((Q+2-σ)/t) ((Q+σ)/t)
    have heq : (Q+2-σ)/t - (Q+σ)/t = (2 - 2*σ)/t := by field_simp; ring
    rw [heq, abs_div] at h
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
    have hrw : |2 - 2*σ| / (2*|t|) = (1/2) * (|2-2*σ|/|t|) := by
      rw [div_mul_eq_div_div]; ring
    rw [hrw]
    linarith [h]
  have hnorm : ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      ≤ |(GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re| + |(GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  have hrenn : 0 ≤ (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re := by
    rw [GPL_re_eq]
    have h1' : (1:ℝ) ≤ (Q+σ)^2 + t^2 := by nlinarith [sq_nonneg (Q+σ)]
    have h2' : (1:ℝ) ≤ (Q+2-σ)^2 + t^2 := by nlinarith [sq_nonneg (Q+2-σ)]
    have := Real.log_nonneg h1'
    have := Real.log_nonneg h2'
    linarith
  rw [abs_of_nonneg hrenn] at hnorm
  linarith

                                                                                                    
      

                    
                                                                                                
                                                                                                 
                                     
              
                   

                
                     
                                              
                                                                            
                                          
                                           
                                                                   
          

/-- **Tight (`O(1/t²)`) upper counterpart of `GPL_ge_log`**, matching
doi:10.1016/j.jmaa.2026.130404 pp. 7–8's own
`log|t| < |G_{Q₁,Q₂}(σ+it)| < (1+O(1/(t²\log|t|)))\log|t|`.

### Summary of Proof
The extra beneficial `1/\log|t|` factor is dropped for a simpler `C/t²` shape, using `log|t| ≥ 1`
at `|t| ≥ 3`. Unlike `GPL_le_log`, which bounds `‖z‖ ≤ |Re z| + |Im z|`
(`Complex.norm_le_abs_re_add_abs_im`, a triangle inequality that adds the `Θ(1/|t|)` imaginary
part *linearly* to the `Θ(\log|t|)` real part), this bounds the true Euclidean norm via
`√(x²+y²) ≤ x + y²/(2x)` for `x > 0` (`x = Re`, `y = Im`), so the `Θ(1/|t|)` imaginary part enters
only *quadratically* — the paper's own cancellation trick, reached by a different route (direct
`Re`/`Im` quadrature instead of its `|1+i/t|`-on-the-product formulation, since the two are
equivalent once the pieces are already in hand here).
### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`, `GPL_im_eq`, `GPL_re_eq`, `abs_arctan_sub_arctan_le`, `arctan_div_swap`,
`norm_eq_sqrt`.
**Used by:** `G1shift_le_tight`, `fiori_zeta_interpolation_1c_tight`,
`fiori_zeta_interpolation_tight`. -/
theorem GPL_le_log_tight (Q σ t : ℝ) (h1 : 0 < Q + σ) (h2 : 0 < Q + 2 - σ) (ht : (3:ℝ) ≤ |t|) :
    ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      ≤ Real.log |t| + (2 * ((Q+σ)^2 + (Q+2-σ)^2) + |2 - 2*σ|^2) / (8 * t^2) := by
  have ht0 : (0:ℝ) < |t| := by linarith
  have htne : t ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  -- `Re` upper bound, exactly `GPL_le_log`'s own `hre` block
  have hre : (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      ≤ Real.log |t| + ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2) := by
    rw [GPL_re_eq]
    have key : ∀ C : ℝ, Real.log (C^2 + t^2) ≤ 2 * Real.log |t| + C^2 / t^2 := by
      intro C
      have hlog : Real.log (C^2 + t^2) = Real.log (t^2) + Real.log (1 + C^2/t^2) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
        ring
      have h2t : Real.log (t^2) = 2 * Real.log |t| := by
        rw [← sq_abs t, Real.log_pow]; push_cast; ring
      have hb : Real.log (1 + C^2/t^2) ≤ C^2/t^2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + C^2/t^2 by positivity)
        linarith
      rw [hlog, h2t]; linarith
    have k1 := key (Q+σ)
    have k2 := key (Q+2-σ)
    have he : ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2)
        = (1/4) * ((Q+σ)^2/t^2 + (Q+2-σ)^2/t^2) := by field_simp
    rw [he]
    linarith [k1, k2]
  -- `Re` lower bound (the extra half `GPL_ge_log` doesn't expose)
  have hrelow : Real.log |t| ≤ (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re := by
    rw [GPL_re_eq]
    have h1' : t ^ 2 ≤ (Q + σ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + σ)]
    have h2' : t ^ 2 ≤ (Q + 2 - σ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + 2 - σ)]
    have ht0' : (0:ℝ) < t ^ 2 := by
      rw [← sq_abs t]; exact pow_pos (abs_pos.mpr htne) 2
    have hlt : Real.log (t^2) ≤ Real.log ((Q + σ) ^ 2 + t ^ 2) := Real.log_le_log ht0' h1'
    have hlt2 : Real.log (t^2) ≤ Real.log ((Q + 2 - σ) ^ 2 + t ^ 2) := Real.log_le_log ht0' h2'
    have he2 : Real.log (t^2) = 2 * Real.log |t| := by
      rw [← sq_abs t, Real.log_pow]; push_cast; ring
    linarith
  -- `Im` upper bound, exactly `GPL_le_log`'s own `him` block
  have him : |(GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).im| ≤ |2 - 2*σ| / (2 * |t|) := by
    rw [GPL_im_eq Q σ t h1 h2, arctan_div_swap h1 h2 htne, abs_mul]
    have h := abs_arctan_sub_arctan_le ((Q+2-σ)/t) ((Q+σ)/t)
    have heq : (Q+2-σ)/t - (Q+σ)/t = (2 - 2*σ)/t := by field_simp; ring
    rw [heq, abs_div] at h
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
    have hrw : |2 - 2*σ| / (2*|t|) = (1/2) * (|2-2*σ|/|t|) := by
      rw [div_mul_eq_div_div]; ring
    rw [hrw]
    linarith [h]
  -- `log|t| ≥ 1` at `|t| ≥ 3` (since `e < 3`)
  have hlog1 : (1:ℝ) ≤ Real.log |t| := by
    have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    have hh : Real.log (Real.exp 1) ≤ Real.log |t| :=
      Real.log_le_log (Real.exp_pos 1) (by linarith)
    rwa [Real.log_exp] at hh
  have hxge1 : (1:ℝ) ≤ (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re := hlog1.trans hrelow
  set x := (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).re with hxdef
  set y := (GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)).im with hydef
  have hxpos : (0:ℝ) < x := by linarith
  -- `√(x²+y²) ≤ x + y²/(2x)` for `x > 0`
  have hkey : Real.sqrt (x^2+y^2) ≤ x + y^2/(2*x) := by
    have hrhs_nonneg : (0:ℝ) ≤ x + y^2/(2*x) := by positivity
    rw [show x + y^2/(2*x) = Real.sqrt ((x+y^2/(2*x))^2) from (Real.sqrt_sq hrhs_nonneg).symm]
    apply Real.sqrt_le_sqrt
    have expand : (x+y^2/(2*x))^2 = x^2+y^2+(y^2/(2*x))^2 := by field_simp; ring
    rw [expand]
    linarith [sq_nonneg (y^2/(2*x))]
  -- the `y²/(2x)` correction: `y² ≤ (2-2σ)²/(4t²)` and `2x ≥ 2`, so `y²/(2x) ≤ (2-2σ)²/(8t²)`
  have hyx : y ^ 2 / (2 * x) ≤ (2 - 2 * σ) ^ 2 / (8 * t ^ 2) := by
    have hy2 : y ^ 2 ≤ (2 - 2 * σ) ^ 2 / (4 * t ^ 2) := by
      have hyy : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
      have h2 : |y| ^ 2 ≤ (|2 - 2 * σ| / (2 * |t|)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg y) him 2
      have heq : (|2 - 2 * σ| / (2 * |t|)) ^ 2 = (2 - 2 * σ) ^ 2 / (4 * t ^ 2) := by
        rw [div_pow, sq_abs, mul_pow, sq_abs]; ring_nf
      rw [hyy, ← heq]; exact h2
    calc y ^ 2 / (2 * x) ≤ ((2 - 2 * σ) ^ 2 / (4 * t ^ 2)) / (2 * x) := by gcongr
      _ ≤ ((2 - 2 * σ) ^ 2 / (4 * t ^ 2)) / 2 := by gcongr; linarith
      _ = (2 - 2 * σ) ^ 2 / (8 * t ^ 2) := by ring
  have hnormeq : ‖GPL Q ((σ:ℂ) + (t:ℂ) * Complex.I)‖ = Real.sqrt (x^2+y^2) := norm_eq_sqrt _
  rw [hnormeq]
  have hsplit : Real.log |t| + (2 * ((Q+σ)^2 + (Q+2-σ)^2) + |2 - 2*σ|^2) / (8 * t^2)
      = (Real.log |t| + ((Q+σ)^2 + (Q+2-σ)^2) / (4 * t^2)) + (2 - 2 * σ) ^ 2 / (8 * t ^ 2) := by
    rw [sq_abs]; ring
  rw [hsplit]
  linarith [hkey, hre, hyx]

                                                                                                
                          

                    
                                                                                              
                                                                                           
                                                                                    

              
                   

                
                     
                                                                          
                                                                                  
                                         
                                                                     
                                                     
                                                         
                                                      
                            

                                                                                                  
                                                                                 
                               

                    
                                                                                                  
                               
              
                   

                
                     
                                                                          
                                                                                                  
                                         
           

                                                                                                 
    
                          

                    
                                                                                                
              
                   

                
                     
                                                                          
                                                     
                                                                

                                                                                                 
     
                                                           

                    
                   
              
                   

                
                     
                                           
                                                                                       
            

                                                                                                
      
         

                    
                   
              
                   

                
                     
                                           
                                                                               
            

                                                                                                
                                                                     
                                                                                      
                             

                    
                                                                                              
                                                                                               
                                                                                                  
                                                                     

              
                   

                
                     
                                                                             
                                                                   
                                                                          
                          
                                                                        
                                                              
                                          
                                                             
                                                        
                                                        
                                                    
                                                                     
                                                               
                                                                           
                                                                        
                           
                                                                       
                                                                                            
                                       
                                                                             
                                
                                                    
                                                             
                                                                         
                                                        
                                  

                                                                                           
                                    

                    
                                                                                               
                                                                                                  
                                                                       

              
                   

                
                     
                                                                       
                                                                         
                                                                                
                                                        
                                 
                                                               
                                                             
                             
                                                  
                                                            
                                
                                                                  

                                                                                             
                                                                          

                    
                                                                                             
                        
              
                   

                
                     
                                                                       
                                                                         
                                                                                       
                                                                                               
                                        
          
                                                     
                                         
                                                                                            
                          
                                                                           
                                              
                                            
                                                  
                                                                     
                                                              
                                                      
                                                                     
                                                    
                     
                                                     
                                                                             
                                
                                                                                    
                             
                            

                                                                   

                    
                                                                                                  
                                                                                          
              
                   

                
                     
                                           
                                                                                    
                                                         
                                         
                                       
                                      
                                                                                  
                                                                                       
                            

                                                                             

                    
                                                                                                   
                                                                                                   
                                                                  
                                                                                              
                                                                                                 
              
                   

                
                     
                     
                                                                                             
                                                 
                                                                                         
                                                                                              
                                   

                                                                                          
                                                                                               
              

                    
                                              
              
                   

                
                     
                                                                       
                                                                         
                                                                                               

                                                                                          
                                 

                    
                                                                                                   
                                                                                               
                                            

              
                   

                
                     
                                                                       
                                                                         
                                                                          
                                                                   
                                       
                                                                                        
                    
                                         
                                                                                        
                               
                      
                                                          
                
                                                                     

                                                                                               
                                                                                     
                                                                                             

                    
                                                                                               
                                                                                                  
                                                                                             

              
                   

                
                     
                     
                                                                                      
                                                         
                                   
                                       
                                                                           
                                                          

                                                                                                  
                                                                                 
                                                                                         
                                                                                            
                                                                          

                    
                                                                                                
                                                                                              
                                                                                       

              
                   

                
                     
                                                                            
                                                                  
                                                                                      
                                     
                                            
                                         
             
             
                                                                           
                                                                                        
                                                           
                                                
                                           
                                                              
                      
                      
                                    
                                                                                        
                                                           
                                                
                                           
                                                              
                      
                      

                                                                                               
                            

                    
                                                                                                  
                                                                                                
                                                                                      
                              

              
                   

                
                                      
                                                                                              
                                                                                          
                                              
                                       

                                                         

                                                                                         
                                                                                              
                                                                                                
                                             

                                            

                    
                                                                                                   
                                                                                              

              
                   

                
                     
                                                      
                                                                         
         
                  
                          
                
            
                                      
                                 
                        
                     
                                                  
                   
               
               

                                                                     

                    
                                                                                               
                                                                                           
                 

              
                   

                
                                     
                                                                                       
                                                                                 
                                                                   
                                 
                                               
          

                                                                                       

                    
                                                                                                
                                                                                                
                                                                                         

              
                   

                
                     
                                    
                                                                                     
         
                  
                          
                
            
                                      
                                 
                        
                     
                                                         
                   
               
              

                                                                                            
                                                                       

                    
                                                                                        
                                                                                           
                                          

              
                   

                
                                                               
                                                                     
                                                                                              
                                                                  
                                                
                                                     
                                            
          

                                                                                        

                    
                                                                                                 
                                                                                                 
                                    

              
                   

                
                                                       
                                                                     
                                                
                                                                       
                                                                  
                                    
                                                    
            
             
                                          
                        
                                      
            
                                                     
            

                                                                                

                    
                                                                                            
                                                                                          
                                                                                                   
                                                                                                
      

              
                   

                
                                 
                                                                     
                                                
                                                                           
                                                                  
                                            
                                          
                                                                    
            
                                                      
                                                                      
                                                                            
                                      
                                                   
          

                                                                                       
                                                                                                 
                                                                                              
                                                                                     

                    
                                                                                       
                                                                                              
              
                   

                
                     
                                                                     
                                                                        
                                                   
                                                            
                                                   
                                                            
                                                               
                                     
                                    
                                        
                                   
                                     
                                             
                                    
                                         
            
                                                
                                      
                                                           
                                                          
              
        
         
            
      

                                                                                    

                                                                                          
                                                                                                   
                                                                                                 
                                                                                                   
                                                                                               
                                                                                              
                            

                                                                                                 
                                               

                    
                                                                                         
                                                                                                
                                                                                                
                                                                                               
                                                                                                  
                                                                                                   
                                                                          

              
                   

                
                       
                                                                      
                                                                            
                                                                                       
                                                                                             
                                     
                                  
                                                            
                                                
                                                                      
                                                
                                                              

                                                                                                
                                                    

                    
                                                                                     
                                                                                                  
                                                                                              
                                                                                                   
                                                                                                  
                                                                              

              
                   

                
                           
                                                                      
                                                                            
                                                                                           
                                             
                                                            
                                         
                                  
                                                            
                                     
                                       
              
                                                                      
                                                   
                                                              

/-- `‖GPL Q (σ+it)‖ ≥ ½(log(Q+a) + log(Q+2-b)) > 0` on the strip, provided `Q+a > 1` and `Q+2-b >
1`.

### Summary of Proof
Proved from `‖w‖ ≥ Re w` together with `Re (Complex.log z) = log ‖z‖ ≥ log (Re z)`.
### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`.
**Used by:** `exists_shared_envelope`, `exists_shared_envelope_1c`. -/
theorem GPL_lower_const {Q a b : ℝ} (hQa : 1 < Q + a) (hQb : 1 < Q + 2 - b) (σ : ℝ)
    (hσ : σ ∈ Set.Icc a b) (t : ℝ) :
    (Real.log (Q + a) + Real.log (Q + 2 - b)) / 2 ≤ ‖GPL Q (σ + t * Complex.I)‖ := by
  set z₁ : ℂ := (Q : ℂ) + (σ + t * Complex.I) with hz₁
  set z₂ : ℂ := (Q : ℂ) + 2 - (σ + t * Complex.I) with hz₂
  have hre₁ : z₁.re = Q + σ := by simp [hz₁]
  have hre₂ : z₂.re = Q + 2 - σ := by simp [hz₂]
  have h₁ : 0 < Q + σ := by nlinarith [hσ.1]
  have h₂ : 0 < Q + 2 - σ := by nlinarith [hσ.2]
  have hlog₁ : Real.log (Q + a) ≤ (Complex.log z₁).re := by
    rw [Complex.log_re]
    apply Real.log_le_log (by linarith)
    calc Q + a ≤ z₁.re := by rw [hre₁]; linarith [hσ.1]
      _ ≤ ‖z₁‖ := Complex.re_le_norm z₁
  have hlog₂ : Real.log (Q + 2 - b) ≤ (Complex.log z₂).re := by
    rw [Complex.log_re]
    apply Real.log_le_log (by linarith)
    calc Q + 2 - b ≤ z₂.re := by rw [hre₂]; linarith [hσ.2]
      _ ≤ ‖z₂‖ := Complex.re_le_norm z₂
  have hval : GPL Q (σ + t * Complex.I) = (1 / 2 : ℂ) * (Complex.log z₁ + Complex.log z₂) := rfl
  calc (Real.log (Q + a) + Real.log (Q + 2 - b)) / 2
      ≤ (GPL Q (σ + t * Complex.I)).re := by
        rw [hval]; simp only [Complex.mul_re, Complex.add_re]; norm_num; linarith
    _ ≤ ‖GPL Q (σ + t * Complex.I)‖ := Complex.re_le_norm _

                                                                                                 
                                                                                               
                                                                               

                    
                                                                                         
              
                   

                
                     
                                                                      
                                                                     
                        
                                                                          
                                                                           
                                   
                                     
                                                                           
                                                                       
                                       
                                                                                
                                  
                                                                                 
                                                                                            
                                               
                                                                           
                                                             
            
                                                                     
                  
                                                 
                                                                                           
                                 
                                                             
                                                           
                                                                                 
                                     
               
                                                                                     
                                                                   
                               
                              
                                                   
                                                                                                 
                
                                                 
                                                                             
                                                                            
                                        
                                                                       
                                                                                              
                             
                                                                                                
                                                                           
                                        
                                                                          
                                                                      
                                           
                                                           
                                                                          
                                                                                      
                                                                          
                                                 
                                                                                
                                                       
                                                                    
                                                         
                                                                                   

/-- `x^5/3125 ≤ exp x` for `x ≥ 0`, from `exp(x/5) ≥ x/5` — the crude polynomial-versus-
exponential step behind `zeta_envelope`.

### Summary of Proof
From `1 + u ≤ exp u` at `u = x/5`, so `x/5 ≤ exp(x/5)` for `x ≥ 0`. Raising both sides to the fifth
power — legitimate since both are nonnegative — and using `exp(x) = exp(x/5)^5` gives `x^5/3125 ≤
exp x`. The quintic is the weakest power that dominates the growth factor needed downstream.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `zeta_envelope`. -/
private theorem quintic_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ (5:ℕ) / 3125 ≤ Real.exp x := by
  have h : x / 5 ≤ Real.exp (x / 5) := by linarith [Real.add_one_le_exp (x / 5)]
  have h5 : Real.exp x = Real.exp (x / 5) ^ (5:ℕ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h5]
  calc x ^ (5:ℕ) / 3125 = (x / 5) ^ (5:ℕ) := by ring
    _ ≤ Real.exp (x / 5) ^ (5:ℕ) := by gcongr

/-- `‖(s-1)ζ(s)‖` is bounded on the compact slice `Re s ∈ [a,b]`, `|Im s| ≤ 3`, since `b < 1`
keeps `ζ`'s pole out of it.

### Summary of Proof
`(s-1)ζ(s)` is continuous on the compact rectangle `[a,b] × [-3,3]`, because the factor `(s-1)`
cancels `ζ`'s only pole and `b < 1` keeps that pole off the slice anyway. A continuous function on
a compact set is bounded, so the supremum exists; the bound is taken nonnegative without loss.
Existential rather than explicit, since only boundedness is needed to feed the growth-envelope
hypothesis.

### References
No tex counterpart.

### Dependencies
**Depends on:** none.
**Used by:** `zeta_envelope`. -/
private theorem compact_slice_bound {a b : ℝ} (hb : b < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ Set.Icc a b, ∀ t ∈ Set.Icc (-3:ℝ) 3,
      ‖((σ:ℂ) + t * Complex.I - 1) * riemannZeta ((σ:ℂ) + t * Complex.I)‖ ≤ M := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc (-3:ℝ) 3) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => ((p.1:ℂ) + p.2 * Complex.I - 1)
        * riemannZeta ((p.1:ℂ) + p.2 * Complex.I))
      (Set.Icc a b ×ˢ Set.Icc (-3:ℝ) 3) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    have hne : ((p.1:ℂ) + p.2 * Complex.I) ≠ 1 := by
      intro hc
      have := congrArg Complex.re hc
      simp at this
      have : p.1 ≤ b := (Set.mem_prod.mp hp).1.2
      linarith
    have hz : ContinuousAt riemannZeta ((p.1:ℂ) + p.2 * Complex.I) :=
      (differentiableAt_riemannZeta hne).continuousAt
    have haff : ContinuousAt (fun q : ℝ × ℝ => ((q.1:ℂ) + q.2 * Complex.I)) p := by fun_prop
    exact ContinuousAt.mul (by fun_prop)
      (ContinuousAt.comp (g := riemannZeta) (f := fun q : ℝ × ℝ => ((q.1:ℂ) + q.2 * Complex.I))
        hz haff)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun σ hσ t ht => ?_⟩
  exact le_trans (hC (σ, t) (Set.mk_mem_prod hσ ht)) (le_max_left _ _)

/-- **`ζ` admits a double-exponential envelope on any strip inside `(0,1)`.** This is the *sole*
remaining input to `fiori_phragmenLindelof`'s growth hypothesis for all four
`interpolated_bound_*`; `envelope_of_const_lower` converts it into the shared `(C1,C2,C3)` package.

### Summary of Proof
**Stated for `f(s) = (s-1)ζ(s)`, the function Phragmén–Lindelöf is actually applied to** (see
`fiori_zeta_interpolation`); the extra factor `‖s-1‖ ≤ 1 + |t|` is polynomial and so changes
nothing in the argument below. It is true with enormous room to spare and its proof needs no new
mathematics, only assembly: `ExternalFacts.bellotti_richert_bound` gives `‖ζ(σ+it)‖ ≤
70.7|t|^{4.438(1-σ)^{3/2}}(log|t|)^{2/3}` for `|t| ≥ 3` on `[1/2,1]` — polynomial in `|t|` with a
bounded exponent — while `exp (D2 · exp (D3|t|))` is doubly exponential and dominates it for any
`D2,D3 > 0` once `|t|` is large; for `|t| ≤ 3` the strip-slice `Set.Icc a b ×ℂ [-3,3]` is compact
and misses `ζ`'s only pole `s = 1` (because `b < 1`), so `‖ζ‖` is bounded there by continuity, and
`D1` can absorb that bound. The assembly is exactly the one sketched above: `D3 := π/(2(b-a))` (so
`D3 < π/(b-a)` with room), `D2 := 1`, and `D1 := 441875/D3⁵ + M + 1` where `M` bounds `‖(s-1)ζ(s)‖`
on the compact slice `[a,b] × [-3,3]` (`compact_slice_bound`). For `|t| ≥ 3`,
`bellotti_richert_bound` plus `‖s-1‖ ≤ 2|t|`, `4.438(1-σ)^{3/2} ≤ 3` and `(log|t|)^{2/3} ≤ log|t| ≤
|t|` give `‖(s-1)ζ(s)‖ ≤ 141.4|t|⁵`, while `exp(exp(D3|t|)) ≥ exp(D3|t|) ≥ (D3|t|)⁵/3125`
(`quintic_le_exp`) — and `141.4·3125 = 441875` is where `D1`'s first summand comes from. For `|t| ≤
3` the compact bound `M` beats `D1·exp(exp(·)) ≥ D1 ≥ M+1`.

### References
No tex counterpart.

### Dependencies
**Depends on:** `bellotti_richert_bound`, `compact_slice_bound`, `quintic_le_exp`.
**Used by:** `exists_shared_envelope`, `exists_shared_envelope_1c`. -/
theorem zeta_envelope {a b : ℝ} (hab : a < b) (ha : 1 / 2 ≤ a) (hb : b < 1) :
    ∃ D1 D2 D3 : ℝ, 0 < D1 ∧ 0 < D2 ∧ 0 < D3 ∧ D3 < Real.pi / (b - a) ∧
      ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
        ‖((σ : ℂ) + t * Complex.I - 1) * riemannZeta (σ + t * Complex.I)‖
          < D1 * Real.exp (D2 * Real.exp (D3 * |t|)) := by
  have hpi := Real.pi_pos
  have hba : (0:ℝ) < b - a := by linarith
  set D3 : ℝ := Real.pi / (2 * (b - a)) with hD3_def
  have hD3 : 0 < D3 := by rw [hD3_def]; positivity
  have hD3b : D3 < Real.pi / (b - a) := by
    rw [hD3_def, div_lt_div_iff₀ (by positivity) hba]; nlinarith
  obtain ⟨M, hM0, hM⟩ := compact_slice_bound (a := a) hb
  -- the polynomial bound for `|t| ≥ 3`
  have hpoly : ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, 3 ≤ |t| →
      ‖((σ:ℂ) + t * Complex.I - 1) * riemannZeta ((σ:ℂ) + t * Complex.I)‖
        ≤ 141.4 * |t| ^ (5:ℕ) := by
    intro σ hσ t ht
    have hσ1 : (1:ℝ)/2 ≤ σ := le_trans ha hσ.1
    have hσ2 : σ ≤ 1 := le_of_lt (lt_of_le_of_lt hσ.2 hb)
    have hT1 : (1:ℝ) ≤ |t| := by linarith
    have hT0 : (0:ℝ) < |t| := by linarith
    have hbr := bellotti_richert_bound (σ := σ) (t := t) ⟨hσ1, hσ2⟩ ht
    have hs1 : ‖((σ:ℂ) + t * Complex.I - 1)‖ ≤ 2 * |t| := by
      have he : ((σ:ℂ) + t * Complex.I - 1) = ((σ - 1 : ℝ):ℂ) + (t:ℝ) * Complex.I := by
        push_cast; ring
      rw [he, Complex.norm_add_mul_I,
        show (2:ℝ) * |t| = Real.sqrt ((2*|t|)^2) from (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_abs t, hT1]
    have hexp : |t| ^ (4.438 * (1 - σ) ^ (3/2:ℝ)) ≤ |t| ^ (3:ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le hT1 ?_
      have h1 : (1 - σ) ^ (3/2:ℝ) ≤ ((1:ℝ)/2) ^ (3/2:ℝ) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      have h2 : ((1:ℝ)/2) ^ (3/2:ℝ) ≤ ((1:ℝ)/2) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      rw [Real.rpow_one] at h2
      nlinarith
    have hl1 : (1:ℝ) ≤ Real.log |t| := by
      rw [Real.le_log_iff_exp_le hT0]
      linarith [Real.exp_one_lt_three]
    have hlogle : Real.log |t| ^ (2/3:ℝ) ≤ |t| := by
      have h1 : Real.log |t| ^ (2/3:ℝ) ≤ Real.log |t| ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num)
      rw [Real.rpow_one] at h1
      linarith [Real.log_le_sub_one_of_pos hT0]
    have hzpos : (0:ℝ) ≤ ‖riemannZeta ((σ:ℂ) + t * Complex.I)‖ := norm_nonneg _
    have hrp3 : (0:ℝ) ≤ |t| ^ (3:ℝ) := Real.rpow_nonneg hT0.le _
    have hz : ‖riemannZeta ((σ:ℂ) + t * Complex.I)‖ ≤ 70.7 * |t| ^ (3:ℝ) * |t| := by
      refine hbr.trans ?_
      have h1 : (70.7:ℝ) * |t| ^ (4.438 * (1 - σ) ^ (3/2:ℝ)) ≤ 70.7 * |t| ^ (3:ℝ) := by
        gcongr
      have h2 : Real.log |t| ^ (2/3:ℝ) ≤ |t| := hlogle
      have h3 : (0:ℝ) ≤ Real.log |t| ^ (2/3:ℝ) := Real.rpow_nonneg (by linarith) _
      nlinarith [h1, h2, h3, hrp3]
    rw [norm_mul]
    have hfin : (2 * |t|) * (70.7 * |t| ^ (3:ℝ) * |t|) = 141.4 * |t| ^ (5:ℕ) := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      ring
    calc ‖((σ:ℂ) + t * Complex.I - 1)‖ * ‖riemannZeta ((σ:ℂ) + t * Complex.I)‖
        ≤ (2 * |t|) * (70.7 * |t| ^ (3:ℝ) * |t|) :=
          mul_le_mul hs1 hz hzpos (by positivity)
      _ = 141.4 * |t| ^ (5:ℕ) := hfin
  refine ⟨441875 / D3 ^ (5:ℕ) + M + 1, 1, D3, by positivity, one_pos, hD3, hD3b, ?_⟩
  intro σ hσ t
  have hEpos : (0:ℝ) < Real.exp (1 * Real.exp (D3 * |t|)) := Real.exp_pos _
  rcases le_or_gt 3 |t| with ht | ht
  · -- large `|t|`: the doubly-exponential envelope beats `141.4|t|^5`
    have hx : (0:ℝ) ≤ D3 * |t| := by positivity
    have h1 : (D3 * |t|) ^ (5:ℕ) / 3125 ≤ Real.exp (D3 * |t|) := quintic_le_exp hx
    have h2 : Real.exp (D3 * |t|) ≤ Real.exp (1 * Real.exp (D3 * |t|)) := by
      rw [one_mul]
      exact Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp (D3 * |t|)])
    have hkey : 141.4 * |t| ^ (5:ℕ)
        ≤ (441875 / D3 ^ (5:ℕ)) * Real.exp (1 * Real.exp (D3 * |t|)) := by
      have he : (441875 / D3 ^ (5:ℕ)) * ((D3 * |t|) ^ (5:ℕ) / 3125) = 141.4 * |t| ^ (5:ℕ) := by
        field_simp
        ring
      calc 141.4 * |t| ^ (5:ℕ) = (441875 / D3 ^ (5:ℕ)) * ((D3 * |t|) ^ (5:ℕ) / 3125) := he.symm
        _ ≤ (441875 / D3 ^ (5:ℕ)) * Real.exp (1 * Real.exp (D3 * |t|)) := by
            apply mul_le_mul_of_nonneg_left (le_trans h1 h2) (by positivity)
    have hMnn : (0:ℝ) ≤ (M + 1) * Real.exp (1 * Real.exp (D3 * |t|)) := by positivity
    have := hpoly σ hσ t ht
    nlinarith [this, hkey, hMnn, hEpos, hM0]
  · -- small `|t|`: the compact-slice bound, against `exp(exp(·)) ≥ 1`
    have htm : t ∈ Set.Icc (-3:ℝ) 3 := by
      rw [Set.mem_Icc]; constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
    have hMb := hM σ hσ t htm
    have hE1 : (1:ℝ) ≤ Real.exp (1 * Real.exp (D3 * |t|)) := by
      have : (0:ℝ) ≤ 1 * Real.exp (D3 * |t|) := by positivity
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (1 * Real.exp (D3 * |t|)) := Real.exp_le_exp.mpr this
    have hP : (0:ℝ) ≤ 441875 / D3 ^ (5:ℕ) := by positivity
    have hME : M ≤ M * Real.exp (1 * Real.exp (D3 * |t|)) := le_mul_of_one_le_right hM0 hE1
    have hPE : (0:ℝ) ≤ (441875 / D3 ^ (5:ℕ)) * Real.exp (1 * Real.exp (D3 * |t|)) :=
      mul_nonneg hP hEpos.le
    nlinarith [hMb, hE1, hM0, hME, hPE]


                                                                                                   
                                                                                                  
                                     

                    
                                                                                                
                                                                                                 

              
                   

                
                                                                            
                                                                        
                                                                             
                                                                                            
                                                                           
                                                                       
                                       
                                                 
                                                                                           
                                  
                                                                         
                                                           
                                                                         
                                                        
                                     
                                     
                                                                      
                            
            
                                       
              
                            
                                                 
              
                            
            
                                                      
                                                          
            
                                         
                                                            
                                             
                                                                                            
                  
               
                                                                                  
                                                                    
                                            
                                                                     
                                        
                                                                                       
                       

                                                                                       

                                                                                    
                                                                                                
                                                                                                
                                                                                
                                                                                             
                                                                                               
                                                                                                
                                                                                       
                                                                                              
                                                                                                
             

/-- `G1shift Q c d s := c·GPL Q (s+1) + d`.

### Summary of Proof
A definition, not a theorem. `G1shift Q c d s = c·GPL Q(s+1) + d` is the shifted, affinely rescaled
log-type function used for case (1c)'s interpolation window, where the boundary bound is affine in
`log|t|` rather than a pure power. The `+1` shift moves `GPL`'s centre of symmetry from `σ = 1` to
`σ = 0`, so that the window `[1/2,5/7]` lies on the increasing side of it.

### References
No tex counterpart.

### Dependencies
**Depends on:** `GPL`.
**Used by:** `G1shift_conj`, `G1shift_ge`, `G1shift_holomorphicOn`, `G1shift_le`,
`G1shift_le_tight`, `G1shift_lower_const`, `G1shift_mono_of_large_t`,
`fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`, `interpG1c`,
`interpG1c_prod_α`, `interpG1c_prod_β`, `interpolated_bound_1c`. -/
noncomputable def G1shift (Q c d : ℝ) : ℂ → ℂ := fun s => (c : ℂ) * GPL Q (s + 1) + (d : ℂ)

                                                                                     
            

                    
                                                                              
                                                                                           
                                                                                                
                                                                                            
                                                                                       
                                                                  

              
                   

                
                                                      
                                                                                   
                                                                                           
                                                                         
                                                                          
                                                    
              
                                                                                      
                                                  
                                                                                       
                                                        
                                                                                              
                                                                                      
                                                                             

                                                                                         
                                                   

                    
                                                                                               
                                                                                             
                                                                                          
                                                                                                 
                                                                                                  
                                                                                               
                        
                                                                                                  
                                                       

              
                   

                
                                             
                                                                                   
                                                                      
                                       
                                                                           
                                                                          
                                                                                 
                                             
                     
                                                                       

/-- **Lower envelope for `G1shift`, a `t`-independent positive constant, valid for every `t`
(including
`t = 0`).** Unlike a reverse-triangle-inequality bound `‖c·w+d‖ ≥ c‖w‖-d` (which is useless here
since `d` dominates `c‖w‖` at the relevant `Q`), this goes via the real part: `Re(c·w+d) =
c·Re(w)+d` exactly, `Re(GPL Q(σ+1+it)) ≥ (log(Q+a+1)+log(Q+1-b))/2` on the shifted strip (mirroring
`GPL_lower_const`'s own derivation), and `‖·‖ ≥ Re(·)`.

### Summary of Proof
Needed for `fiori_phragmenLindelof`'s `hG_lower`, which quantifies over *all* `t : ℝ`, not just
`|t| ≥ 1` (where the weaker `G1shift_ge` would suffice).
### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`.
**Used by:** `exists_shared_envelope_1c`. -/
theorem G1shift_lower_const {Q c d a b : ℝ} (hc : 0 ≤ c) (_hd : 0 ≤ d) (hQa : 1 < Q + a + 1)
    (hQb : 1 < Q + 1 - b) (σ : ℝ) (hσ : σ ∈ Set.Icc a b) (t : ℝ) :
    c * ((Real.log (Q + a + 1) + Real.log (Q + 1 - b)) / 2) + d
      ≤ ‖G1shift Q c d (σ + t * Complex.I)‖ := by
  set z₁ : ℂ := (Q : ℂ) + (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) with hz₁
  set z₂ : ℂ := (Q : ℂ) + 2 - (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) with hz₂
  have hre₁ : z₁.re = Q + σ + 1 := by simp [hz₁]; ring
  have hre₂ : z₂.re = Q + 1 - σ := by simp [hz₂]; ring
  have hlog₁ : Real.log (Q + a + 1) ≤ (Complex.log z₁).re := by
    rw [Complex.log_re]
    apply Real.log_le_log (by linarith)
    calc Q + a + 1 ≤ z₁.re := by rw [hre₁]; linarith [hσ.1]
      _ ≤ ‖z₁‖ := Complex.re_le_norm z₁
  have hlog₂ : Real.log (Q + 1 - b) ≤ (Complex.log z₂).re := by
    rw [Complex.log_re]
    apply Real.log_le_log (by linarith)
    calc Q + 1 - b ≤ z₂.re := by rw [hre₂]; linarith [hσ.2]
      _ ≤ ‖z₂‖ := Complex.re_le_norm z₂
  have hval : GPL Q (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = (1 / 2 : ℂ) * (Complex.log z₁ + Complex.log z₂) := rfl
  have hReGPL : (Real.log (Q + a + 1) + Real.log (Q + 1 - b)) / 2
      ≤ (GPL Q (((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
    rw [hval]; simp only [Complex.mul_re, Complex.add_re]; norm_num; linarith
  have heq : (σ:ℂ) + t * Complex.I + 1 = ((σ + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have hval2 : G1shift Q c d (σ + t * Complex.I)
      = (c:ℂ) * GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by
    simp only [G1shift, heq]
  have hreG1 : (G1shift Q c d (σ + t * Complex.I)).re
      = c * (GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I)).re + d := by
    rw [hval2]; simp [Complex.add_re, Complex.mul_re]
  have hle := Complex.re_le_norm (G1shift Q c d (σ + t * Complex.I))
  rw [hreG1] at hle
  nlinarith [hReGPL, hc]

/-- **`G1shift` dominates `c·log|t|+d` at the boundary — the analogue of `GPL_ge_log`.** Since
`‖z‖ ≥ Re z` always and `Re(GPL Q(σ+1+it)) ≥ log|t|` (from the closed form `GPL_re_eq`, using
`(Q+σ)²+t², (Q+2-σ)²+t² ≥ t²`), `Re(G1shift Q c d(σ+it)) = c·Re(GPL Q(σ+1+it))+d ≥ c·log|t|+d`.

### Summary of Proof
The lower bound `c·log|t| + d ≤ ‖G1shift‖`. Since `‖z‖ ≥ Re z`, it suffices to bound the real part,
which is `c·Re GPL Q(σ+1+it) + d` by linearity. Then `Re GPL ≥ log|t|` — re-derived here from the
closed form `GPL_re_eq`, using `(Q+σ+1)²+t², (Q+1-σ)²+t² ≥ t²`, rather than by calling
`GPL_ge_log` — together with `c ≥ 0` gives the claim. This is the analogue of `GPL_ge_log` for the
shifted family, and supplies the boundary hypothesis Phragmén–Lindelöf needs at the affine edge.

### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`, `GPL_re_eq`.
**Used by:** `fiori_zeta_interpolation_1c`, `fiori_zeta_interpolation_1c_tight`. -/
theorem G1shift_ge (Q c d σ t : ℝ) (hc : 0 ≤ c) (_hd : 0 ≤ d) (ht : 1 ≤ |t|) :
    c * Real.log |t| + d ≤ ‖G1shift Q c d (σ + t * Complex.I)‖ := by
  have heq : (σ:ℂ) + t * Complex.I + 1 = ((σ + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have hval : G1shift Q c d (σ + t * Complex.I)
      = (c:ℂ) * GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by
    simp only [G1shift, heq]
  have hre : (G1shift Q c d (σ + t * Complex.I)).re
      = c * (GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I)).re + d := by
    rw [hval]; simp [Complex.add_re, Complex.mul_re]
  have hgre : Real.log |t| ≤ (GPL Q (((σ + 1 : ℝ):ℂ) + t * Complex.I)).re := by
    rw [GPL_re_eq]
    have h1 : t ^ 2 ≤ (Q + (σ + 1)) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + (σ + 1))]
    have h2 : t ^ 2 ≤ (Q + 2 - (σ + 1)) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (Q + 2 - (σ + 1))]
    have ht0 : (0:ℝ) < t ^ 2 := by nlinarith [sq_abs t, ht]
    have hlt : Real.log (t^2) ≤ Real.log ((Q + (σ + 1)) ^ 2 + t ^ 2) := Real.log_le_log ht0 h1
    have hlt2 : Real.log (t^2) ≤ Real.log ((Q + 2 - (σ + 1)) ^ 2 + t ^ 2) := Real.log_le_log ht0 h2
    have he2 : Real.log (t^2) = 2 * Real.log |t| := by
      rw [← sq_abs t, Real.log_pow]; push_cast; ring
    linarith
  have hle := Complex.re_le_norm (G1shift Q c d (σ + t * Complex.I))
  rw [hre] at hle
  nlinarith [hgre, hc]

                                                                                                 
                                                                                        
                                                              

                    
                                                                                                   
                                                                                                   
                                                                                               
                                  

              
                   

                
                                               
                                        
                                                                                 
                                         
                                       
                                                                                              
                                                                                              
                                               
                                                                     
                            
                                                                  
                                         
                                                       
                   
                                                                              
                     
                                          
                                                                         
                                        
                                                               
                                                                                               
                                             
                                                                                              
              

                                                                                             
                                                                                                 
                                                           

                    
                                                                                         
                                                                                                
                                                                                                 
                               

              
                   

                
                                                     
                                                    
                                                                                       
                                             
                                       
                         
                                                                          
                                                                                              
                                               
                                                                     
                            
                                                                        
                                         
                                                       
                   
                                                                              
                     
                                          
                                                                         
                                        
                                                               
                                                                                               
                                             
                                                                                          
              

/-- Expansion of the shifted modulus squared: `‖cw + d‖² = c²‖w‖² + 2cd·Re(w) + d²` for real
`c, d` and complex `w`.

### Summary of Proof
**Proof.** Rewrite both norms via `norm_eq_sqrt`, square away the square roots with `Real.sq_sqrt`,
expand the real and imaginary parts of `cw + d`, and finish with `ring`. **Why it is stated
separately.** This is the identity that makes `G1shift_mono_of_large_t` work: it exhibits
`‖G1shift‖²` as a sum of three terms, each nondecreasing in `σ` once `c > 0` and `d ≥ 0` — `c²‖w‖²`
by `GPL_mono_of_large_t`, `2cd·Re(w)` by `GPL_re_mono_of_large_t`, and the constant `d²`. Without
the expansion, monotonicity of `‖cw + d‖` does not follow from monotonicity of `‖w‖` alone, since
the shift by `d` can interact with the argument of `w`. No tex counterpart.

### References
No tex counterpart.

### Dependencies
**Depends on:** `norm_eq_sqrt`.
**Used by:** `G1shift_mono_of_large_t`. -/
private theorem normSq_c_mul_add_d (c d : ℝ) (w : ℂ) :
    ‖(c:ℂ) * w + (d:ℂ)‖ ^ 2 = c ^ 2 * ‖w‖ ^ 2 + 2 * c * d * w.re + d ^ 2 := by
  rw [norm_eq_sqrt, Real.sq_sqrt (by positivity), norm_eq_sqrt, Real.sq_sqrt (by positivity)]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- **`G1shift` is strictly increasing in `σ` on `[a,b]` with `0 ≤ a`, once `|t| > Q+1`** (and `0 ≤
Q`,
`0 < c`, `0 ≤ d`) — the shift means only `a+1 ≥ 1` is needed, matching where `GPL` itself is
increasing.

### Summary of Proof
Both `‖w‖` (`GPL_mono_of_large_t`, shifted) and `Re w` (`GPL_re_mono_of_large_t`, shifted) increase
in `σ`, where `w := GPL Q(σ+1+it)`; since `c > 0`, `d ≥ 0`, `‖G1shift‖² = c²‖w‖²+2cd·Re(w)+d²`
(`normSq_c_mul_add_d`) is then a sum of nondecreasing terms in `σ`, strictly so from the `‖w‖²`
term.
### References
No tex counterpart.

### Dependencies
**Depends on:** `G1shift`, `GPL`, `GPL_mono_of_large_t`, `GPL_re_mono_of_large_t`,
`normSq_c_mul_add_d`.
**Used by:** `interpolated_bound_1c`, `interpolated_bound_1c_tight`. -/
theorem G1shift_mono_of_large_t (Q c d a b : ℝ) (hQ : 0 ≤ Q) (hc : 0 < c) (hd : 0 ≤ d)
    (ha : 0 ≤ a) (hQb : 0 < Q + 1 - b) :
    ∀ t : ℝ, Q + 1 < |t| →
      StrictMonoOn (fun σ : ℝ => ‖G1shift Q c d (σ + t * Complex.I)‖) (Set.Icc a b) := by
  intro t ht x hx y hy hxy
  have hmapx : x + 1 ∈ Set.Icc (a + 1) (b + 1) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmapy : y + 1 ∈ Set.Icc (a + 1) (b + 1) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hnormmono := GPL_mono_of_large_t Q (a + 1) (b + 1) hQ (by linarith) (by linarith)
    t ht hmapx hmapy (by linarith)
  have hremono := GPL_re_mono_of_large_t Q (a + 1) (b + 1) hQ (by linarith) (by linarith)
    t ht hmapx hmapy (by linarith)
  have heqx : (x:ℂ) + t * Complex.I + 1 = ((x + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have heqy : (y:ℂ) + t * Complex.I + 1 = ((y + 1 : ℝ):ℂ) + t * Complex.I := by push_cast; ring
  have hvalx : G1shift Q c d (x + t * Complex.I)
      = (c:ℂ) * GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by simp only [G1shift, heqx]
  have hvaly : G1shift Q c d (y + t * Complex.I)
      = (c:ℂ) * GPL Q (((y + 1 : ℝ):ℂ) + t * Complex.I) + (d:ℂ) := by simp only [G1shift, heqy]
  have hwx_nn : (0:ℝ) ≤ ‖GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I)‖ := norm_nonneg _
  have hsq : ‖G1shift Q c d (x + t * Complex.I)‖ ^ 2 < ‖G1shift Q c d (y + t * Complex.I)‖ ^ 2 := by
    rw [hvalx, hvaly, normSq_c_mul_add_d, normSq_c_mul_add_d]
    have h1 : c ^ 2 * ‖GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I)‖ ^ 2
        < c ^ 2 * ‖GPL Q (((y + 1 : ℝ):ℂ) + t * Complex.I)‖ ^ 2 := by
      apply mul_lt_mul_of_pos_left _ (by positivity)
      exact pow_lt_pow_left₀ hnormmono hwx_nn (by norm_num)
    have h2 : 2 * c * d * (GPL Q (((x + 1 : ℝ):ℂ) + t * Complex.I)).re
        ≤ 2 * c * d * (GPL Q (((y + 1 : ℝ):ℂ) + t * Complex.I)).re := by
      rcases eq_or_lt_of_le hd with hd0 | hd0
      · simp [← hd0]
      · exact mul_le_mul_of_nonneg_left hremono.le (by positivity)
    linarith
  have hnn2 : (0:ℝ) ≤ ‖G1shift Q c d (y + t * Complex.I)‖ := norm_nonneg _
  exact lt_of_pow_lt_pow_left₀ 2 hnn2 hsq

/-! ### Fiori's Phragmén–Lindelöf theorem in the exact form applied here

`BackgroundZetaBounds`' `interpolated_bound_1a`, `_1b` and `_2` are instances of a *single*
two-point interpolation for `ζ`: a bound `A|t|^p (log|t|)^{ra}` on the line `Re s = a`, a bound
`B|t|^q (log|t|)^{rb}` on the line `Re s = b`, and the conclusion interpolating them geometrically
across the strip. Rather than re-derive that instance three times from `fiori_phragmenLindelof`
(which would mean discharging its holomorphy, conjugacy, envelope and monotonicity hypotheses
afresh each time), we record the applied form once, as `fiori_zeta_interpolation`. Case (1c)'s
boundary bound at `σ = a` has a shape this wrapper cannot express and gets its own instantiation,
`fiori_zeta_interpolation_1c`, further down. -/

                                                                 
                                                                                                  
                                                                                                
                                                                                          
                                                                                           
                                                                                   

                    
                                                                                               
                        
              
                   

                
                                          
                                                                                            
                                                                                     
                                   
                                                            
                                                                                      

                                           

                    
                                                                                              
                                                                
              
                   

                
                     
                                                                                              
                                        
                                                     

                                           

                    
                                                                                                  
                                                                                                
                                                           
              
                   

                
                     
                                                                                              
                                        
                                                 

                                                                        
                                                                                                
                                                                                            
             

                    
                                                                                             
                                                                                         
                                                                                               
                                                                                                  
                   

              
                   

                
                     
                                                                             
                                                                                   
                                                   
                                                
                                         
                          
                                                                                           
                                                          
                              
                                                                                     
                                                                                     
                                             
                                                                       
                          
                                                             

                                              

                    
                                                                                         
                                                
              
                   

                
                     
                                                                             
                                                                                          
                      
                                                   
                                                    
                                         
                                                               
                                                        
                          
                                                                                           
                                                          
                                                                                     
                                                                                     
                     
                                                                       
                                                   
                                                                          
                                              
                            
                                                                  
                                                                                    
            

                                                                                                 
                                                                                                  
                                                                                         
                                                                                                  
                                                                                               
                                                                                            
                                                                                              
                                                   

                    
                                                                                                  
                                                                                                  
                                                                                     
                                                                             
                                                                                          
                                                                                                
                                                                                                   
                                                                                           
                                                                                             
                                                                                                   
                                                                                               
                                                                                                  
                                                                                              
                                                                                                 
                                                                                                 
                                                                                             
                                                                                                 
                                                                                                  
                                                                                                   
                                                                                                
                                                                                                
                                                                                                  
                                                                                       
                                                                                             
                                                                                                  
                                                                                                  
                                                                                         
                                                                                                   
                                                                                                  
                                                                                              
                                                                                                   
                                                                                              
                                                                                                  
                                                                                                  
                                                                                               
                                                                                             
                                                                                               
                                                                                               
                                                                                                  
                                                                                            
                                                                                              
                                                                                                
                                                                        
                                                                                          
                                                                                                    
                                                                                                 
                                                                                                
                                                                                          
                                                                                                
                                                                              
                                                                                                 
                                                                                             
                                                                                       
                                                                 
                                                                                              
                                                           

                                                        
                 
                                                                                                 
                                                                                    
                                                                                                
                                                                                                  

                                                                                              
                                                                                                
                                                                                                 
                                                                     

              
                   

                
                                                                                                   
                                                                                                  
                                                                       
                                                                                
                                                             
                                               
                                                                                     
                                                                               
                                           
                                           
                                                                            
                                                  
                                                 
                                  
                                                                          
                                  
                                                                          
                                                      
                                                                       
                                                                                   
                                                                                          
                                                        
                                       
                                                                           
                                                                       
                                                                                        
                                                               
                                                                               
                                                                                          
                                  
                                                        
                                               
                                               
                                           
                                     
                                                                                 
           
               
                                      
                                          
                                                               
                                                   
                                                         
                
                                 
               
                           
                               
                                                                              
                                                                      
                                     
                                                                
                                     
                                                                
                                                                                             
                                                                   
                                                                                 
                                                                    
                                                     
                                         
                                                                               
                                               
                                                                      
                                                                                     
                                           
                   
                                                                    
                   
                                                                          
                                        
                                                       
                                                                                          
                                                                                             
                                                                 
                                                        
                                                        
                                           
                                                                            
                                           
                                                           
                                                                                              
                  
                                                                                                   
                    
                        
                         
                               
                                                                   
             
                                                      
                                                        
                                                                 
                                       
                                
                                                                   
                             
                                
                                                                   
                             
                                                                               
                                              
                                                                     
                
                                                                                           
                     
                                                           
                                          
                                                                                 
                
                               
                                                        
                      
                                                                       
                                                    
           
                                      
                                               
                                                                          
                                                                              
                   
                                                                                    
                                                                            
                                                                                              
                           
                                                     
                                                                           
                                               
               
                                                          
                                                            
                                                                             
                                                          
                                                                                     
                                             
                                                                                     
                                                         
                                                                        
                                                                                      
                                           
                                                                                           
                                                                      
                                                                           
                                                                 
                                                              
                            
                                                                                  
                                                                                            
                      
                                                                       
                                                    
           
                                      
                                                     
                                                                          
                                                                              
                                                                                             
                                      
                                                                  
                                                     
                                                                            
                                       
                                                            
                                                                                         
                                                  
                                                                   
                                                     
                                                                            
                                                              
                                                                  
                           
                                                                 
                                                         
                                                           
                                                             
                                            
                                                                           
                                           
                                                                 
                                                    
                                                              
                                                            
                                                                     
                                                                                     
                                             
                                              
                                                                      
                                                                                    
                                                                  
                                                    
                                             
                                                                              
                                                          
                               
                                                                     
                                          
                                                        
                                                     
                                                                                        
                                                     
                           
                                                                                    
                                                                       
                                                                                         
                                   
                
                                     
                                                              
                                                                 
                                     
                                                                                              
                                                                      
                                                                                     
                                                                 
                                                              
                            
                                                                                  
                                                                                            
                                                                                      
                                                                                   
                                          
                                         
                                                                                         
                                                                                             
                
               
                                                                                                 
                             
                                                                                      
                                                          
                       
                                                                                        
                                                                                            
                    
                                                                          
                                                      
                 
               
                                                                             
               
                             
                                                        
                                                              
                                                                                    
                                                          
                                                                       
                                                                   
                                                                             
                                                                                
                                          
                                                                              
                                                                                          
                                                    
                 
                         
                                         
                                 
                              
                                                 
                                                            
                                      
                                     
                                     
                                                                                
                                     
                
                                              
                                              
                                                         
                                                         
                                                                   
                                                                   
                                                                        
                                    
                                                        
                                                              
                                                                
                                      
                                      
                                                                         
                                       
                                          
                                   
                                                                        
                                                                              
                                     
                                                        
                                 
                                     
                                                 
                                                                              
                                                            
                                           
             
                                 
                                      
                                   
                                     
                                                               
                                            
                                                                                
                 
                                                                            
                                                        
                                                                                  
            
                                                  
                                                
                                                                  
                                                                                   
            
            
                               
                                                    
                                                     
                                                    
                                                     
                                         
                                                          
                                         
                                                                       
                                                                         
            
                      
                                                                               
                                         
                                                                                            
                                                            
                          
                                                                                           
                     
             
          
           
                                                     
                                
                
                                                 
                                                                              
                                   
                           
                                           
             
                                
                                
                                        
                           
                          
                                      
                                                 
                                                                              
                                                                                             
                                           
             
                                                           
                                                                                  
                                                              
                                       
                                                    
                         
                                                          
                                                          
                                                             
                                                 
                                      
                                                     
                                                                                   
                                                                               
                                                         
                                                                                            
                                    
                                                        
                                                        
                                                                 
                                                                 
                                                                          
                                         
                                         
                   
                                                                                    
                                                                                
                                                     
                                                                                   
                                     
                                                                    
                  
                                                                                                 
                                         
                                                                                        
                                                                                              
                                                     
                                                                   
                                                                         
                                            
                                                               
                                                                                         
                                                               
                                                                                         
                           
                                                                                  
                                                                   
                                                           

                                  
                                                                                                
                                                                                           
                                                                                      
                                               
                                                                                        
                                                                                           
                                                                                                
                                                                                          
                                                                            

                    
                                                                                                  
                                                                                                   
                                                                                                  
                                                                                      
                                                                                                
                                                                                                
                                                                                                 
                                                                                             
                                                                                          
                                                                                              
                                                                                                 
                                                                                  
                                                                                                  
                                                                                                  
                                                               
                                                                                           
                                                                                              
                                                                                                   
                               

              
                   

                
                                                                                                   
                                                                                               
                   
                                                                                                  
                                                                      
                                               
                                                                                     
                                                                                                
                                           
                                           
                                                                            
                                                  
                                                 
                                  
                                                                          
                                  
                                                                          
                                                      
                                                                       
                                                                                   
                                                                                        
                                                 
                                                                            
                                                                                           
                                                                                  
                                          
                                                
                                                                            
                                                                                             
                                                                                 
                               
                                                                     
                                                    
                                                        
                                               
                                               
                                           
                                     
                                                                                 
           
               
                                      
                                          
                                                               
                                                   
                                                         
                
                                 
               
                           
                               
                                                                              
                                                                      
                                     
                                                                
                                     
                                                                
                                                                   
                                                                                 
                                                                    
                                                     
                                         
                                                                               
                                               
                                                                      
                                                                                     
                                           
                   
                                                                    
                   
                                                                          
                                        
                                                       
                                                        
                                                        
                                           
                                                                            
                                           
                                                           
                                                                                              
                  
                                                                                                   
                    
                        
                         
                               
                                                                   
             
                                                      
                                                        
                                       
                                
                                                                   
                             
                                
                                                                   
                             
                                              
                                                                     
                
                                                                                           
                     
                                                           
                                          
                                                                                 
                
                               
                                                        
                      
                                                                       
                                                    
           
                                      
                                               
                                                                          
                                                                              
                   
                                                                                    
                                                                            
                                                                                              
                           
                                                     
                                                                           
                                               
               
                                                          
                                                            
                                                                             
                                                          
                                                                                     
                                             
                                                                                     
                                                         
                                                                        
                                                                                      
                                           
                                                                                           
                                                                      
                                                                           
                                                                 
                                                              
                            
                                                                                  
                                                                                            
                      
                                                                       
                                                    
           
                                      
                                                     
                                                                          
                                                                              
                                                                                             
                                      
                                                                  
                                                     
                                                                            
                                       
                                                            
                                                                                         
                                                  
                                                                   
                                                     
                                                                            
                                                              
                                                                  
                           
                                                         
                                                           
                                                             
                                            
                                                                           
                                           
                                                                 
                                                    
                                                              
                                                            
                                                                     
                                                                                     
                                             
                                              
                                                                      
                                                                                    
                                                                  
                                                    
                                             
                                                                              
                                                          
                               
                                                                     
                                          
                                                        
                                                     
                                                                                        
                                                     
                           
                                                                                    
                                                                       
                                                                                         
                                   
                
                                     
                                                              
                                                                 
                                     
                                                                                              
                                                                      
                                                                                     
                                                                 
                                                              
                            
                                                                                  
                                                                                            
                                         
                                                                                         
                                                                                             
                
               
                                                                                                 
                             
                                                                                      
                                                          
                       
                                                                                        
                                                                                            
                    
                                                                          
                                                      
                 
               
                                                                             
               
                             
                                                        
                                                          
                                                                       
                                                                   
                                                                             
                                                                                
                                          
                                                                              
                                                                                           
                     
                                 
                                   
                          
                                         
                                 
                              
                                      
                                     
                                     
                                     
                                                                          
                                              
                                              
                                                         
                                                         
                                                                   
                                                                   
                                                                        
                                                        
                                                              
                                                                
                                      
                                      
                                                                         
                                       
                                          
                                   
                         
                                           
                   
                                                                        
                                                                              
                                     
                                                        
                                 
                                     
                                                 
                                                                              
                                                            
                                           
             
                                 
                                                                                        
               
                              
                               
                        
               
                                    
              
                                     
                                                                     
                                  
                                                                       
                              
                                                                                            
                             
                      
                                                    
                                                     
                                                    
                                                     
                                         
                                                          
                                         
                                                                       
                                                                         
            
                      
                                                                               
                                         
                                                                                            
                                                            
                          
                                                                                           
                     
             
          
           
                                                     
                                
                
                                                 
                                                                              
                                   
                           
                                           
             
                                
                                
                                        
                           
                          
                                      
                                                 
                                                                              
                                                                                             
                                           
             
                                                           
                                                                                  
                                                              
                                       
                                                    
                         
                                                          
                                                          
                                                             
                                                                                            
                                                        
                                                        
                                                                 
                                                                 
                                                                          
                                         
                                         
                                                                                   
                                     
                                                                    
                  
                                                                                                 
                                         
                                                                                             
                                                                                                
                                                                                                
                                                       
                                                                                 
                                                         
                                                       
                                                                                          
                                                                                                
                                                       
                                                                     
                                                                           
                                              
                                                                 
                                                                                           
                                                                 
                      
                                                                                    
                                                                                      
                                                                            
                                  
                                                                                
                                                                                            
                            
                                                        
                               
                                        
                                                                            
                                    
                                                                            
                                                    
                                                                        
                                                     
                                                                                     
                                                                                         
                                                                                   
                          
          
                                                                             
                                                                                 
                                              
                                              
                                                                                       
                                       
                                           
                                                                              
                          
                                           
                                                                              
                          
                         
                                                 
                                                                                         
                         
                                           
                                              
                
                                    

                                                                                              

                                                                 
                                                                                   
                                                                                               
                                                                         
                                                                                                 
                                                                                              
                                                                        
                                                                
                                                                                               
                                                                                                 
                                                                                                
                                                                                           
                                                                                                  
                                                         

                                                            

                    
                          
              
                   

                
                                                     
                                                                        
                                                                            
                                    
                                                              
                                                             

                                                                                                 
                                                                                              
                                       

                    
                                                                                                 
                                                                                                
                                                                                                
                              

              
                   

                
                     
                                                                                    
                                                         
                                                      

                                                                                                  
                                      

                    
                                                                                               
                                                                                                 
                                                 

              
                   

                
                     
                                                                                    
                                                         
                                                  

                                                                                                    
                                                                                       

                    
                                                                                            
                                                                                                 
                                                                                                
             

              
                   

                
                     
                                                                                   
                                                    
                                                                                              
                         
                                                                                               
                                                                       
                                                                      
         
                                                

                                                                                                 
                                                                                              
                                                                            

                    
                                                                                                   
                                                                                               
                                                                          

              
                   

                
                     
                                                                                   
                                                                            
                                                    
                                               
                                                           
                         
                                                                                               
                                                                                 
                                                            
                                                     
                                                                   
                                                                                 
                                                                                          
                                                                          
                                                            
      

                                                                                                
                                                                                                
                                                                                              

                    
                                                                                                  
                                                                                                  
                                                                                            
                                                                                               
                                                                                                
                                                                                                 
                                                                                       

              
                   

                
                                                         
                                                                                   
                
                                                                                   
                                                                                                 
                                                        
                                                                                           
                                                                       
                                       
                                                 
                                                          
                                  
                                                                         
                                                           
                                                                         
                                     
                                                           
                                                                      
                                                           
                                                           
            
                                                                    
                                                        
                                                          
            
                                            
                                                                                
                                                
                                                                    
                                                        
                                                    
                                                                       
                            
                                                     
              
                                                                             
                                                          
                                                                   
                                                        
         
                      
                   
                                          
                                                                                      
                                                                        
                                                           
                                                                                  
                                                                                               
                                                                                  
                                                                  
                         
                                                      

                                                                                                
                                                                                             

                    
                                                                                                 
                                                                                                 
                                                                                                 
                                                              

              
                   

                
                     
                                                                                   
                                                                 
                                                                            
                          
                                                          
                                                                               
                                                             
                                                    
                                                                                              
                                                                           
                                                
                                                                       
                                                                                            
                                       
                                                                                   
                                                                                               
                                                                                          

                                                                                            
                                                                                                  
                                                                                          
                                                       

                    
                                                                                               
                                                                                              
                                                                                                 
                               

              
                   

                
                     
                                              
                                                                                         
                                                                                                  
                                                                  
                                           
                                        
                                                                                  
                                                                                       
                                                                            
                                                      
                                                                                         
                                                                      
                            

                                                                                              
                                                                                                
                                                                                     
                                                                       

                    
                                                                                           
                                                                                            
                                                               
              
                   

                
                     
                     
                                                                                     
                                   
                                                                              
                                                    
                                                                      
                                                         
                                                            
                                                                               
                                                
                                                         
            
                                                           
                                       
                                                                    
                       
                                                       
                                                           
                                                                                   
                                    

                                  
                                                                                              
                                                                                             
                                                                                      
                                                                                
                                                                                  
                                                                                          
                                                                                               
                                                                                       
                                                                                            
                                                                                              
                                        

                    
                                                                                                  
                                                                                                   
                                                                                              
                                                                                          
                         

              
                   

                
                                                                         
                                                                                       
                                                                                             
                    
                                                             
                                                            
                                               
                                                                    
                                              
                                                                                         
                                  
                                                                                    
                                 
                                                                            
                                                  
                                                 
                                  
                                                                           
                                  
                                                                     
                                                                      
                                                                                         
                                                      
                                                                       
                                                                                     
                                                                                        
                                                         
                                       
                                                                      
                                     
                                                                       
                                                      
                                                          
                                              
                                              
                                           
                                     
                                                                                 
           
               
                                      
                                                                       
                                          
                                                               
                                                   
                                                         
                
                                 
               
                           
                                                                                      
                                                                                      
                               
                                                                              
                                                                      
                                     
                                                               
                                     
                                                               
                                                                                              
                                                    
                                                            
                                                                      
                                                                                     
                                           
                   
                                                                    
                   
                                                                          
                                                                                   
                                                        
                                                        
                                           
                                                                            
                                           
                                                           
                                                                                              
                  
                                                                                                   
                    
                        
                         
                               
                                                                   
             
                                                      
                                                        
                                       
                                
                                                                   
                             
                                
                                                                   
                             
                                              
                                                                     
                
                                                                                           
                     
                                                           
                                          
                                                                                 
                
                               
                                                        
                      
                                                                       
                                                    
           
                                      
                                           
                                                                              
                   
                                                                                    
                                                                             
                                                                                              
                           
                                                     
                                                                           
                                               
               
                                                          
                                                            
                                                                                 
                                                   
                                                 
                                                                        
                                                                                     
                                                  
                                                                                      
                                 
                                                                         
                                                                                     
                                     
                                                                                            
                                                   
                                                                     
                                                                  
                                                              
                            
                                                                                  
                                                                                            
                      
                                                                       
                                                    
           
                                      
                                                 
                                                                          
                                                                              
                                                                                             
                                      
                                                                  
                                                     
                                                                            
                                       
                                                            
                                                                                         
                                                  
                                                                   
                                                     
                                                                            
                                                              
                                                                  
                           
                                                         
                                                           
                                                             
                                            
                                                                           
                                           
                                                                 
                                                    
                                                              
                                                            
                                                                     
                                                                                     
                                             
                                              
                                                                      
                                                                                    
                                                                  
                                                    
                                             
                                                                                       
                               
                                                                     
                                          
                                                        
                                                     
                                                                                   
                                                     
                           
                                                                               
                                                                       
                                                                                    
                                   
                
                                     
                                                              
                                                            
                                     
                                                                         
                                                                      
                                                                                     
                                                            
                                                              
                            
                                                                                  
                                                                                            
                                         
                                                                                         
                                                                                             
                
                                                                                               
                                                                                  
                                                                                        
                                                                               
                                                                       
                                        
                        
                                                      
                                                                                
                       
                                                          
                                                                       
                                                                   
                                                                             
                                                                                
                                          
                                                                              
                 
                         
                                         
                                 
                              
                                                  
                                                             
                                      
                                     
                                     
                                                                                         
                                     
                                              
                                              
                                                         
                                                         
                                                                   
                                                                   
                                                                        
                                                        
                                                              
                                                                
                                                                        
                                      
                                      
                                                                         
                            
                
                                           
                                                                                     
                                           
                                                                         
                                       
                                            
                                     
                                                                        
                                                                              
                                      
                                                         
                                 
                                      
                                                 
                                                                              
                                                             
                                           
             
                                 
                                      
                                   
                                     
                                                               
                                            
                                                                                
                 
                                                                            
                                                        
                                                                                  
            
                                                  
                                                
                                                                  
                                                                                   
            
            
                                        
                                     
                                                
                                   
                                             
                
             
                                                    
                                                     
                                                    
                                                     
                      
                                                                       
                                                    
                                                                                            
                                                            
                          
                                                                                           
                     
             
          
           
                                                     
                                
                
                                                 
                                                                              
                                   
                           
                                           
             
                                
                                
                                        
                           
                          
                                       
                                                 
                                                                              
                                                                                              
                                           
             
                                                           
                                                                    
                                                                            
                                                           
                         
                                                           
                                                           
                                                              
                                                     
                                                              
                                          
                                      
                                                     
                                        
                                            
                                                     
                                                             
                           
                                  
                                      
                                                      
                                    
                                      
                                                      
                                                                     
                                                                                            
                                           
                                                        
                                                                 
                                                                 
                                                         
                                                                             
                                           
                                          
                                            
                   
                                                                             
                                                                                 
                                                     
                  
                                                                                  
                                      
                                                                      
                  
                                                                               
                                        
                                          
                                                                        
                                                                   
                                                                                         
                                                                                   
                                                            
                                                              
                                                   
                                                                
                                         
              
                                                                                  
                                                                             
                                                                                  
                           
                                                                                  
                                                                             
                                          

                                  
                                                                                                
                                                                                             
                                                                      
                                                                                                
                                                                                              
                                                                                                  
                                               

                    
                                                                                                  
                                                                                              
                                                                                                   
                      

              
                   

                
                                                                         
                                                                                       
                                                                                                 
                                                                   
                                                                     
                                               
                                                                    
                                                               
                                                                                         
                                  
                                                                                    
                                 
                                                                            
                                                  
                                                 
                                  
                                                                           
                                  
                                                                     
                                                      
                                                                       
                                                                                     
                                                                                      
                                                 
                                                                            
                                                         
                                                                 
                                               
                                          
                                                
                                                                            
                                                           
                                                                   
                                              
                               
                                                                                                    
                                                                         
                                                              
                                                          
                                              
                                              
                                           
                                     
                                                                                 
           
               
                                      
                                                                       
                                          
                                                               
                                                   
                                                         
                
                                 
               
                           
                                                                                      
                                                                                      
                               
                                                                              
                                                                      
                                     
                                                               
                                     
                                                               
                                                                                              
                                                    
                                                            
                                                                      
                                                                                     
                                           
                   
                                                                    
                   
                                                                          
                                                                                   
                                                        
                                                        
                                           
                                                                            
                                           
                                                           
                                                                                              
                  
                                                                                                   
                    
                        
                         
                               
                                                                   
             
                                                      
                                                        
                                       
                                
                                                                   
                             
                                
                                                                   
                             
                                              
                                                                     
                
                                                                                           
                     
                                                           
                                          
                                                                                 
                
                               
                                                        
                      
                                                                       
                                                    
           
                                      
                                           
                                                                              
                   
                                                                                    
                                                                             
                                                                                              
                           
                                                     
                                                                           
                                               
               
                                                          
                                                            
                                                                                 
                                                   
                                                 
                                                                        
                                                                                     
                                                  
                                                                                      
                                 
                                                                         
                                                                                     
                                     
                                                                                            
                                                   
                                                                     
                                                                  
                                                              
                            
                                                                                  
                                                                                            
                      
                                                                       
                                                    
           
                                      
                                                 
                                                                          
                                                                              
                                                                                             
                                      
                                                                  
                                                     
                                                                            
                                       
                                                            
                                                                                         
                                                  
                                                                   
                                                     
                                                                            
                                                              
                                                                  
                           
                                                         
                                                           
                                                             
                                            
                                                                           
                                           
                                                                 
                                                    
                                                              
                                                            
                                                                     
                                                                                     
                                             
                                              
                                                                      
                                                                                    
                                                                  
                                                    
                                             
                                                                                       
                               
                                                                     
                                          
                                                        
                                                     
                                                                                   
                                                     
                           
                                                                               
                                                                       
                                                                                    
                                   
                
                                     
                                                              
                                                            
                                     
                                                                         
                                                                      
                                                                                     
                                                            
                                                              
                            
                                                                                  
                                                                                            
                                         
                                                                                         
                                                                                             
                
                                                                                               
                                                                                  
                                                                                        
                                                                               
                                                                       
                                        
                        
                                                      
                                                                                
                       
                                                          
                                                                       
                                                                   
                                                                             
                                                                                
                                          
                                                                              
                                                                                           
                    
                                
                                   
                         
                                         
                                 
                              
                                      
                                     
                                     
                                     
                                                                          
                                              
                                              
                                                         
                                                         
                                                                   
                                                                   
                                                                        
                                                        
                                                              
                                                                
                                                                        
                                      
                                      
                                                                         
                                       
                                          
            
                            
                
                                           
                                                                                     
                                           
                                                                         
                                       
                                            
                                     
                           
                                            
                   
                                                                        
                                                                              
                                      
                                                         
                                 
                                      
                                                 
                                                                              
                                                             
                                           
             
                                 
                                                                                        
               
                              
                               
                                                                                  
                                     
                                                                     
                                  
                                                                       
                              
                                                                                            
                             
                      
                                                                           
                                            
                                          
                          
                                                              
                                                
                                                                                   
                         
                                                                       
                                         
                                     
                                                                                 
                                    
                       
                                                    
                                                     
                                                    
                                                     
                      
                                                                       
                                                    
                                                                                            
                                                            
                          
                                                                                           
                     
             
          
           
                                                     
                                
                
                                                 
                                                                              
                                   
                           
                                           
             
                                
                                
                                        
                           
                          
                                       
                                                 
                                                                              
                                                                                              
                                           
             
                                                           
                                                                    
                                                                            
                                                           
                         
                                                           
                                                           
                                                              
                                                     
                                                              
                                                        
                                                                 
                                                                 
                                                         
                                                                       
                                           
                                          
                                            
                  
                                                                                  
                                      
                                                                      
                  
                                                                               
                                        
                                          
                                                                                              
                                                                                              
                                       
                                                       
                                                                          
                                                                       
                                                       
                                                                          
                                                                     
                                                                                           
                                                                                     
                                                              
                                                                
                                                     
                                                                  
                                           
                
                                                                                    
                                                                               
                      
                                                                             
                                                                                          
                                                                            
                                  
                                                                                              
                                                                                            
                            
                                                        
                                     
                                        
                                                                                                
                                                                                      
                                   
                                                                        
                                                     
                                                                                         
                                                                                         
                                                                                       
                          
          
                                                                             
                                                                             
                               
                                                
                                               
                                                 
                                                                                          
                                                                                 
                                             
                                                                                 
                           
                                           
                                                                               
                          
                                              
                                                                                  
                           
                               
                                                       
                                                                                   
                                                                     
                                             
                                   
                                                       
                                                                  
                
                                    

                                                                                      

                                                                                              
                                                                                               
                                                                                                  
                                                                                                  
                                                                                               
                                                                                                
                                                                                                 
                                                                                             

                                                                         

                    
                                                                                            
                                                                                                  
                                                                            
                                             
              
                   

                
                     
                                                                                             
                                                                                      
                                                        
                                    
                                                                                 
                                      
                         
                         
                                               
                                                           
          
                                                  

                                                                                             

                    
                                                                                                
                                                                                                 
                                                                    

              
                   

                
                     
                                                                                  
                                                                                         
                                                       
                                     
                                                   
                                                                            
                                  
             
                                                   
                                                
                 
                                                                
                                                           

                                                                                             
                                                                              

                    
                                                                                                
                                                                                              
                                                                                             
                          

              
                   

                
                                 
                                                                                       
                                                   
                                                                                 
                              

                                                                                               
                                                                                       

                    
                                                                                                  
                                                                                                   
                                                                                                 
                                                                                        
                                                                                                 
                                                                                               
                                                                                                  
                                                                                                  
                                                                                                 
                                   

              
                   

                
                                
                                                                 
                                                            
                                                            
                                      
                                                         
                                                                                        
                                                                    
              
                                                                                              
                                                                     
                                     
                                     
                                            
                                            
                                       
                                       
                                                 
                                                 
                                                    
                                                               
                          
                                               
                                                                                             
                          
                                                                  
                                                                         
                                          
                                                                                    
                                                                     
                                                                                           
                                                    
                                                        
                                                                          
                                                        
                                          
                                                                   
                                             
                                                        
              
                                                                                           
                                                        
                                                                               
                                                            
                                      
                                                                                    
                
                                                     
                                            
                
                                                                 
                                                        
                                            
                                                              
                                                                
                                             
                                                          
                    
                         
                                                  
                           
                                                   
                                                              
                                                
                                              
                                                                            
                                                             
                                                                                       
                                                                         
                                                                             
                
                                                                                           
                                                           
                                                  
             
              
                                 
                                       
                            
                                         
            
                                       
                                                                                
                                                                                           
                                                    
                                                  
                                                 
                                                           
                     
                                                       
             
                         

                                  
                                                                                          
                                                                                 
                             
                                                                                              
                                                                                            
                                           

                    
                                                                                                
                                                                                                   
                                                                                                
                                                                                                  
                                   
              
                   

                
                                                  
                                        
                                                                         
                                                                     
                                                                     
                                      
                                                                          
                                                          
                                                                    
                                                                            
                                   
                                                            
                                                                            
                                                                     
                                     
                                     
                                            
                                            
                                       
                                       
                  
                                                                           
                                                        
                                                
                                                
                                                               
                                                          
                                                          
                                                   
                                               
                                                                                             
                          
                                                                 
                                                                   
                                                       
                                                                                              
                                          
                                                                                           
                                                                     
                                                                                           
                                                     
                                                         
                                       
                                                    
                                                
                             
                                                          
                                                                               
                                                            
                                            
                                                                                     
                
                                                 
                                                
                             
                                                                                        
                                                                 
                                                          
                                                   
                                                                              
                    
                                                                            
                                                            
                                                                                        
                                                                    
                                                           
                                                               
                                                 
                                                         
                                                                                      
                          
                                                                                           
                                
                                                                                  
                                     
                                                                                      
                                                                           
                                                           
                  
                                                                               
                                                                    
                                                    
                                                                        
                                                                                            
                    
                           
                                                                                             
                                       
                                                        
                                                     
                                                                                
                           
                                                      
                                                           
                    
                                                              
                                               
                                                  
                               
                               
                                                                                        
                                     
                                                      
                                                                            
                                                         
                           
                                                            
                                                            
                            
                                                                         
                                                                                        
                                           
                                                 
                                                                 
                                                                           
                                             
                        
                                        
                                                                                        
                                                        
                                                                               
                                                            
                                            
                                                                                    
                
                                                     
                                                      
                                                                 
                                                        
                                            
                                                              
                                                                
                                             
                                                                     
                         
                                                                  
                                                                           
                                                       
                           
                                                                           
                                                             
                                       
                                            
                                                                  
                                                                   
                                                                   
                                                   
                                                    
                       
                                                                                                  
                                            
                                                                                                   
                                                            
                       
                                                                 
                                                                                           
                                                 
                                                                    
                                                                               
                                             
                        
                                       
                                       
                                  
                                                                        
                                                               
                                               
                         
                 
                                       
                                                                                  
                                                                                             
                                                          
                                                              
                                                    
                                                  
                                                  
                                                            
                     
                                               
                                                                           
                                                                                
                
                                                                            
                        
                                                                        
                                                                    
             
                                

                                                                                                 
                                                                                             
                                                                                                
                                                             

                    
                                                                                              
                                                                                                
                                                                              
              
                   

                
                     
                     
                                                                    
                                                                 
                                                                                        
                                                                
                                                                                         
                 
                                       
                                                  
                                              
                                                 
                                                                                
                        
                                       
                            
            
                                       
                                                            
                                                                       
                                                    
                                                  
                                                 
                                                           
                                                       
                              

                                                                                                    
  
                                                                                                  
                                                        

                    
                                                                                                  
                                                          
              
                   

                
                     
                                       
                                                                 
                                                            
                                      
                                                                                        
                                                                    
                                                                                         
                   
                                                                     
                                     
                                            
                                       
                                            
                                                 
                                                               
                                                       
             
                                                
                                                                                               
                            
                                 
                                  
                     
            
                                       
                            
                                         
            
                                       
                                                                                
                                                                                           
                                                    
                                                  
                                                 
                                                           
                       
                                                       
                          
                              
