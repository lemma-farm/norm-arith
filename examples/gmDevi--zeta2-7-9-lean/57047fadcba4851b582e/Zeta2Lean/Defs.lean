import Mathlib

/-!
# Zeta2Lean.Defs — the Volkenborn integral, the 2-adic zeta values and the Δ-calculus

The shared definitions of the development.  They come from the `{7,9,11}` repository
(https://github.com/gmDevi/zeta2-7-9-11-lean, file of the same name); the definitions of that
project's construction, which the pair does not use, are omitted here.  The pair construction is
in `Zeta2Lean/Pair/Defs.lean`.  "proof.md" is the informal proof `docs/proof.md`.

* The first six definitions, `volkenbornSum`, `HasVolkenborn`, `volkenborn`, `halfPow`, `J` and
  `zeta2`, are the **trusted definitions**: they are the only project definitions in the statement
  of the main theorem, and `Challenge.lean` contains verbatim copies of them.  They are identical
  to those of the `{7,9,11}` repository.
* `Ahalf` and `dn` are used by the pair's linear form and denominators.
* `DeltaGe`, `DeltaAll`, `IntValued` and `hcoef` are the objects of the 2-adic Δ-calculus
  (`Stmt_Delta`, `Stmt_DeltaFun` in `Zeta2Lean/Statements.lean`).
* The file ends with the basic API of the Volkenborn Riemann sums.

Conventions.
* `ℚ_[2]` is Mathlib's field of 2-adic numbers; `‖·‖` its norm (`‖2‖ = 1/2`).
* The Volkenborn integral (proof.md P1) is *not* in Mathlib.  We use Riemann sums
  `volkenbornSum f N = 2^{-N} ∑_{x<2^N} f x` and the predicate `HasVolkenborn f I`
  (`volkenbornSum f N → I`).  `volkenborn f = limUnder …` is only a name for the limit; every
  statement that uses a value comes with a `HasVolkenborn` certificate.
* `J s = ∫_{ℤ₂} (t+1/2)^{-s} dt` and `zeta2 s = J (s-1) / ((s-1) 2^s)`.  The identification of
  `zeta2 s` with the Kubota–Leopoldt value `L₂(s, ω^{1-s})` is LSZ Lemma 2.8 (cited, not
  formalised).  Irrationality is invariant under the non-zero rational factor `(s-1) 2^s`, so the
  theorem about `J 6` and `J 8` *is* the theorem about `ζ₂(7)` and `ζ₂(9)`.
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ## Volkenborn integral via Riemann sums (proof.md P1, P2) -/

/-- Riemann sum `2^{-N} ∑_{x < 2^N} f x` of the Volkenborn integral. -/
def volkenbornSum (f : ℕ → ℚ_[2]) (N : ℕ) : ℚ_[2] :=
  ((2 : ℚ_[2]) ^ N)⁻¹ * ∑ x ∈ range (2 ^ N), f x

/-- `f` is Volkenborn integrable with integral `I`: the Riemann sums converge 2-adically to `I`. -/
def HasVolkenborn (f : ℕ → ℚ_[2]) (I : ℚ_[2]) : Prop :=
  Tendsto (volkenbornSum f) atTop (𝓝 I)

                                                                                        
                                                     
                                         
                                  

                                                                                            
                                
                           

                                                      
                        
                        

                                                                                              
                                                                                 
                            
                                         

                                        

                                                                               
def Ahalf (k s : ℕ) : ℚ :=
  ∑ l ∈ range k, (((l : ℚ) + 1 / 2)⁻¹) ^ s

                                                      
                                   

                                                       

                                                                                       
                                                                                                     
def DeltaGe (m : ℕ) (c : ℤ) (f : ℕ → ℚ_[2]) : Prop :=
  ∀ k : ℕ, 2 ^ m ≤ k →
    ‖f k - f (k - 2 ^ Nat.log 2 k)‖ ≤ (2 : ℝ) ^ (-(c + (Nat.log 2 k : ℤ)))

/-- Lai's `Δ(f) ≥ c`: `Δ₀(f) ≥ c` and `v₂(f 0) ≥ c - 1`. -/
def DeltaAll (c : ℤ) (f : ℕ → ℚ_[2]) : Prop :=
  DeltaGe 0 c f ∧ ‖f 0‖ ≤ (2 : ℝ) ^ (1 - c)

/-- `f` takes values in `ℤ₂`. -/
def IntValued (f : ℕ → ℚ_[2]) : Prop :=
  ∀ k, ‖f k‖ ≤ 1

/-- `h_β(x) = [δ^β] ∏_{k=0}^{n} (2x+2k+1+δ)^{-8}`, i.e. `h^{(β)}(x) / (β! 2^β)` for
`h(t) = ∏_{k=0}^{n} (2t+2k+1)^{-8}`.  (A function of the `{7,9,11}` construction.  It occurs here
only in the fields `hcoefInt`, `hcoefDelta` of the shared statement `Stmt_DeltaFun`, which the pair
does not use; `Pair/Proofs/Valuation.lean` proves the exponent-`6` analogue that it needs.) -/
def hcoef (n β x : ℕ) : ℚ :=
  coeff β (∏ k ∈ range (n + 1), ((C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 8)⁻¹)

/-! ## Basic API (proved here, available to every proof file) -/

theorem volkenbornSum_add (f g : ℕ → ℚ_[2]) (N : ℕ) :
    volkenbornSum (fun x => f x + g x) N = volkenbornSum f N + volkenbornSum g N := by
  unfold volkenbornSum
  rw [Finset.sum_add_distrib, mul_add]

theorem volkenbornSum_const_mul (a : ℚ_[2]) (f : ℕ → ℚ_[2]) (N : ℕ) :
    volkenbornSum (fun x => a * f x) N = a * volkenbornSum f N := by
  unfold volkenbornSum
  rw [← Finset.mul_sum]
  ring

theorem volkenbornSum_sum {ι : Type*} (s : Finset ι) (F : ι → ℕ → ℚ_[2]) (N : ℕ) :
    volkenbornSum (fun x => ∑ i ∈ s, F i x) N = ∑ i ∈ s, volkenbornSum (F i) N := by
  unfold volkenbornSum
  rw [Finset.sum_comm, Finset.mul_sum]

theorem HasVolkenborn.add {f g : ℕ → ℚ_[2]} {I I' : ℚ_[2]} (hf : HasVolkenborn f I)
    (hg : HasVolkenborn g I') : HasVolkenborn (fun x => f x + g x) (I + I') := by
  unfold HasVolkenborn at *
  rw [show volkenbornSum (fun x => f x + g x) = fun N => volkenbornSum f N + volkenbornSum g N
    from funext (volkenbornSum_add f g)]
  exact hf.add hg

theorem HasVolkenborn.const_mul {f : ℕ → ℚ_[2]} {I : ℚ_[2]} (a : ℚ_[2]) (hf : HasVolkenborn f I) :
    HasVolkenborn (fun x => a * f x) (a * I) := by
  unfold HasVolkenborn at *
  rw [show volkenbornSum (fun x => a * f x) = fun N => a * volkenbornSum f N
    from funext (volkenbornSum_const_mul a f)]
  exact hf.const_mul a

theorem HasVolkenborn.sum {ι : Type*} (s : Finset ι) {F : ι → ℕ → ℚ_[2]} {I : ι → ℚ_[2]}
    (h : ∀ i ∈ s, HasVolkenborn (F i) (I i)) :
    HasVolkenborn (fun x => ∑ i ∈ s, F i x) (∑ i ∈ s, I i) := by
  unfold HasVolkenborn at *
  rw [show volkenbornSum (fun x => ∑ i ∈ s, F i x) = fun N => ∑ i ∈ s, volkenbornSum (F i) N
    from funext (volkenbornSum_sum s F)]
  exact tendsto_finsetSum s h

theorem HasVolkenborn.unique {f : ℕ → ℚ_[2]} {I I' : ℚ_[2]} (h : HasVolkenborn f I)
    (h' : HasVolkenborn f I') : I = I' :=
  tendsto_nhds_unique h h'

                                                                                         
                       
                                                      

                                                           
                                   
                                                                 
                         

end Zeta2

end
