import Zeta2Lean.Defs

/-!
# Zeta2Lean.Statements — the shared statements

The statements that the pair development takes over from the `{7,9,11}` repository
(https://github.com/gmDevi/zeta2-7-9-11-lean, file of the same name; the statements of that
project's construction are omitted here).  Each is a `def Stmt_X : Prop` (or a `structure` with
named fields).  The pair statements (`Zeta2Lean/Pair/Statements.lean`) and the pair proofs take
them as hypotheses, and `Zeta2Lean/Pair/Main.lean` and `Zeta2Lean/Pair/Unconditional.lean` supply
their proofs:

* `PNT_Stmt`: the prime number theorem, proved in `Zeta2Lean/Cited/PNT.lean` (`PNT_proof`);
* `Stmt_JConv`: convergence of the Riemann sums of `(x + 1/2)^{-s}` (`Proofs/JConvergence.lean`);
* `Stmt_Translation`: the translation formula of the Volkenborn integral
  (`Proofs/Translation.lean`);
* `Stmt_Criterion`: Lai's irrationality criterion (`Proofs/Criterion.lean`);
* `Stmt_Delta`, `Stmt_DeltaFun`: the 2-adic Δ-calculus (`Proofs/DeltaCalculus.lean`,
  `Proofs/DeltaFunctions.lean`).

The five files `Zeta2Lean/Proofs/*.lean` are identical to those of the `{7,9,11}` repository.
References "proof.md P1–P3" are to `docs/proof.md` §2; "Lai" = arXiv:2304.00816, "LSZ" =
arXiv:2505.05005.
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ## The prime number theorem -/

                                                                                              
                                                                                     
                                                  
                      
                                                        

                                               

                                                                             
                        
                                          

                                                                                                 
                                                        
                              
                                                        
                                                                                                   

                                                                                   
                            
                                                                             
                                                              
                                                                      
                                                                                        
                           

                                                                                   

                                                                                       
structure Stmt_Delta : Prop where
  /-- Lai Lemma 2.4 (2.3), Riemann-sum form: `Δ_m(f) ≥ c ⇒ R_M ≡ R_m mod 2^{c-1}` (`M ≥ m`). -/
  riemann : ∀ (f : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ), DeltaGe m c f →
    ∀ M, m ≤ M → ‖volkenbornSum f M - volkenbornSum f m‖ ≤ (2 : ℝ) ^ (1 - c)
  /-- Lai Lemma 2.4 (2.2), Riemann-sum form: `Δ(f) ≥ c ⇒ v₂(R_M) ≥ c - 1`. -/
  riemannAll : ∀ (f : ℕ → ℚ_[2]) (c : ℤ), DeltaAll c f →
    ∀ M, ‖volkenbornSum f M‖ ≤ (2 : ℝ) ^ (1 - c)
  mono : ∀ (f : ℕ → ℚ_[2]) (m m' : ℕ) (c c' : ℤ), m ≤ m' → c' ≤ c → DeltaGe m c f → DeltaGe m' c' f
  monoAll : ∀ (f : ℕ → ℚ_[2]) (c c' : ℤ), c' ≤ c → DeltaAll c f → DeltaAll c' f
  ofAll : ∀ (f : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ), DeltaAll c f → DeltaGe m c f
  /-- Lai Lemma 2.5 / LSZ 2.6(a) (finite sums). -/
  sum : ∀ {ι : Type} (s : Finset ι) (F : ι → ℕ → ℚ_[2]) (m : ℕ) (c : ℤ),
    (∀ i ∈ s, DeltaGe m c (F i)) → DeltaGe m c (fun x => ∑ i ∈ s, F i x)
  sumAll : ∀ {ι : Type} (s : Finset ι) (F : ι → ℕ → ℚ_[2]) (c : ℤ),
    (∀ i ∈ s, DeltaAll c (F i)) → DeltaAll c (fun x => ∑ i ∈ s, F i x)
  /-- LSZ 2.6(b) (constant factor; only `≥` is needed). -/
  smul : ∀ (f : ℕ → ℚ_[2]) (m : ℕ) (c e : ℤ) (a : ℚ_[2]), ‖a‖ ≤ (2 : ℝ) ^ (-e) →
    DeltaGe m c f → DeltaGe m (c + e) (fun x => a * f x)
  smulAll : ∀ (f : ℕ → ℚ_[2]) (c e : ℤ) (a : ℚ_[2]), ‖a‖ ≤ (2 : ℝ) ^ (-e) →
    DeltaAll c f → DeltaAll (c + e) (fun x => a * f x)
  /-- Lai Lemma 2.5(2) (products of `ℤ₂`-valued functions). -/
  mul : ∀ (f g : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ), IntValued f → IntValued g →
    DeltaGe m c f → DeltaGe m c g → DeltaGe m c (fun x => f x * g x)
  mulAll : ∀ (f g : ℕ → ℚ_[2]) (c : ℤ), IntValued f → IntValued g →
    DeltaAll c f → DeltaAll c g → DeltaAll c (fun x => f x * g x)

                                                                                      
                                                                                             
                                                            
                                    
                                    
                                                                                                  
                                                              
                                          
                                                                                         
                                 
                                                                        
                                                                                                   
                                                                           

end Zeta2

end
