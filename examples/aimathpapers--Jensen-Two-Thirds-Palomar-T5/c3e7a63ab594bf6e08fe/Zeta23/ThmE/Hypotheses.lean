/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/Hypotheses.lean — Theorem E (Dirichlet L-functions), the χ-dependent densities and the
published inputs restated for L(s,χ).

Canonical text: the paper §7.2 [subsec:dirichlet], [thm:E] and its proof, items (i)–(iii), VERBATIM:
"(i) Explicit formula: with κ = (1−χ(−1))/2, Proposition prop:EF holds for
 W_χ(f,g) := Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ)) (zeros of L(s,χ)) with ν_X replaced by
 ν_{X,χ} := μ_χ + P_{X,χ},  μ_χ(τ) := (1/2π)[log(q/π) + Re Γ′/Γ(1/4 + κ/2 + iτ/2)],
 P_{X,χ}(τ) := −(1/π) Re Σ_{n≤X} Λ(n)χ(n) n^{−1/2−iτ}, and no pole term (Π_X ≡ 0); the derivation of
 Appendix A applies to [IK04, Theorem 5.12] for L(s,χ). Since ν_{X,χ} is real, G is again real
 symmetric. (ii) Zero side: the multiset of zeros of L(s,χ) is invariant under ρ ↦ 1−ρ̄ with
 multiplicities (functional equation χ ↔ χ̄ composed with conj L(conj s,χ) = L(s,χ̄)), all zeros have
 0<β<1, and N_χ(t+1) − N_χ(t) ≪_q log(t+3); Section 4 is otherwise verbatim. (iii) Prime side:
 |Λ(n)χ(n)| = Λ(n)·1_{(n,q)=1}, so Lemma lem:cheb holds for these coefficients with O_q(·) errors
 (finitely many primes removed); … μ_χ = (1/2π) log(q|τ|/2π) + O(τ⁻²) satisfies (eq:mufacts)–(eq:muints)
 with ℓ₁ replaced by ℓ_{1,χ} := log(qT/2π) + 2log2 − 1, and λ₁ = L/ℓ_{1,χ} → λ as q is fixed."

This file is ζ-free AND L-free: it defines the densities μ_χ, P_{X,χ}, ν_{X,χ}
as explicit real functions of (κ, q, the coefficient character values) and states the hypotheses
for an ABSTRACT `ZeroConfig`; only `Zeta23/ThmE/Statement.lean` mentions Mathlib's
`DirichletCharacter.LFunction`.  Everything the paper derives from these inputs is proved in the sibling files;
this file only states the inputs.
-/
import Zeta23.Hypotheses
import Mathlib.NumberTheory.DirichletCharacter.Basic

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23
namespace ThmE

/-! ## 1. The χ-dependent scalars and densities  ([thm:E] proof (i), (iii)) -/

                                                                                                     
                                                                                      

                                                                                                       
                                                                                                   
                                                        
                                      
                       
                                                                                             

                                                                                                      
                                                                                                     
                                                                                
def PXc (c : ℕ → ℂ) (X : ℝ) (τ : ℝ) : ℝ :=
  -(1 / Real.pi) * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
    ((Λ n : ℝ) : ℂ) * c n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)).re

                                                                                     
                                                                           

                                                                                                
                                                                             
structure CoeffOK (q : ℕ) (c : ℕ → ℂ) : Prop where
  norm_le : ∀ n, ‖c n‖ ≤ 1
  vanish : ∀ n, ¬ Nat.Coprime n q → c n = 0

/-- Unimodular coefficient sequences: additionally `‖c n‖ = 1` exactly on `(n,q) = 1`, `n > 0`
(true for a primitive χ).  Needed wherever the main term is TWO-sided ([prop:PP]'s diagonal uses
`|χ(n)|² = 1`); the four upper-bound statements only need `CoeffOK`. -/
structure CoeffUnimodular (q : ℕ) (c : ℕ → ℂ) : Prop extends CoeffOK q c where
  norm_eq : ∀ n, 0 < n → Nat.Coprime n q → ‖c n‖ = 1

/-! ## 2. The published inputs, restated for L(s,χ)  (abstract zero configuration Z) -/

                                                                                                    
                                                                                                      
                                                                                                      
                               
                                                                            
                                                                       
                                                                               
                                                      
                                                                                                  
                                                                                         

                                                                                                         
                                                                                                    
                                                                                                  
                                                                     
                                      
                                                                          
                                                                                         

                                                                                                      
                                                                                                          
                                              
                                          
                                 
                                           
                                             
                                     
                                        
                                                                                      
                                                                         
                                        
                                                                            
                                           
                                                                                
                                                             

                                                                                                      
                                                                                                  
                                                                                                
                                                                                            
                                                         
structure ChebyshevMertensCoprime (q : ℕ) : Prop where
  cheb2a : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), Λ n ^ 2 / n
      - Real.log x ^ 2 / 2| ≤ C * Real.log x
  cheb2b : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q),
        Λ n ^ 2 / n * (Real.log x - Real.log n) - Real.log x ^ 3 / 6| ≤ C * Real.log x ^ 2

                                                                                              
                                                                           
                                                                            
                                      
                                 
                         
                                   
                                   
                           

                                                                         

section PXcUnfold

                                                          
                                                                    
                                          
                                                                                                
                                                       
                                      
                                                                
                                                                
                                                       
                                                                      
                                                                                           
                    
         
                           
           
                                                  
         

                                                      
                                    
                                        
                                                                         
                                                                                  
                                                                               
                                                                                 
      

                                                                                            
                                                                                             
                                                
                                                         
                                          
                                                                                           
            
         
                     
                                            
                                              
                                          
                                                          
                                                                     
                         
                                                                       
                                                                                                    
                                                        
                                                       
                                                                       
             
        
                                
                                                         
                                                              
                                                                                         
                                                                                 
                                                                                    
        
         

end PXcUnfold

/-! ## Uniform-constant ("Bounded") variants, for the hybrid range [rem:otherL](i):
same fields as `GammaFactsChi` / `ChebyshevMertensCoprime`
but with every existential constant replaced by the given bound, so families of characters can
carry ONE constant uniformly in q. -/

                                                                                     
                                                             
                                          
                                 
                                           
                                             
                                     
                               
                                                                                      
                                                                
                           
                                                                            
                              
                                                                                
                                                             

                                 
                                                            
                                                           
                                                                      
                                                                               

                                                                    
structure ChebyshevMertensCoprimeBounded (q : ℕ) (B : ℝ) : Prop where
  cheb2a : ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q), Λ n ^ 2 / n
      - Real.log x ^ 2 / 2| ≤ B * Real.log x
  cheb2b : ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => Nat.Coprime n q),
        Λ n ^ 2 / n * (Real.log x - Real.log n) - Real.log x ^ 3 / 6| ≤ B * Real.log x ^ 2

                                 
                                                                              
                                                                           
                                

end ThmE
end Zeta23
