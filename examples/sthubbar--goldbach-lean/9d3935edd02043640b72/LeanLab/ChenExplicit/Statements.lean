module

public import Mathlib

/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Explicit Chen theorems, statements only, as `Prop`s so that no placeholder proof is needed.
* P0010 T. Yamada, Explicit Chen's theorem, arXiv 1511.03409, Theorem 1.1.
* P0009 M. Bordignon, D. R. Johnston, V. Starichkova, An explicit version of Chen's theorem,
  arXiv 2207.09452, Theorem 3, Corollary 4, Theorem 5.
Both papers define their count as the number of representations of `N` as a prime plus a
product of at most two primes; neither text, as read on 2026-10-16, adds size conditions on the
prime factors, so we use `Nat.IsAtMostAlmostPrime 2` from Mathlib, which admits `1`.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

noncomputable section
namespace LeanLab.ChenExplicit

                                                                                         
                               
                                                                              

                                                          
def twinC : ℝ := ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- `U_N = 2 e^{-γ} ∏_{p>2} (1 - 1/(p-1)²) ∏_{p>2, p ∣ N} (p-1)/(p-2)`, equation (2) of P0009
and the display after Theorem 1.1 of P0010. -/
def U (N : ℕ) : ℝ :=
  2 * Real.exp (-Real.eulerMascheroniConstant) * twinC *
    ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

                                                                                               
                    
                                                
                                                           

                                                                                     
                                                                            
                  
                                                        
                                                            

                                                                                                
                                  
                  
                                                        
                                                           

                                                                                       
                                   
                        
                                                        
                                                                   

                                                                                               
          
                  
                           
                                                                            

                                                                              
                               
                                                                                        

end LeanLab.ChenExplicit
