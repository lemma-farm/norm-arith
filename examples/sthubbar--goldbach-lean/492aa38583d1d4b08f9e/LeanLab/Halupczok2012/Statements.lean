module

public import Mathlib

/-!
# Halupczok 2012: basic objects and the statement of Theorem 1.2

K. Halupczok, *Goldbach's problem with primes in arithmetic progressions and in short intervals*,
J. Théor. Nombres Bordeaux 25, 2013, no. 2, 331 to 351, arXiv 1212.4406. This file defines the
sums, the singular series `S` and `T` and the statement `Theorem2` of the paper's Theorem 1.2,
called Theorem 2 in the arXiv version, in its coprime reading. AI wrote the Lean code, Claude,
Anthropic; it was checked by the Lean kernel. Binary Goldbach is open; ternary Goldbach is a
theorem, Helfgott 2013.

Conventions, following the paper's notation section.
* `[X, X+Y]` is the set of integers `m` with `X < m ≤ X + Y`.
* `L = log Y`.
* Every `≪`, `≫`, `≍` in a hypothesis is encoded by a universally quantified constant `c > 0`;
  every `≪` in a conclusion by an existential constant `C`, and "sufficiently large" by an
  existential threshold `Y0`. These may depend on `A`, the `ε`'s, the hypothesis constants and
  the fixed residue `a`. `B = B(A)` is existential after `A`.
-/

@[expose] public section

open Finset
open scoped Classical

namespace LeanLab.Halupczok2012

/-! ### Basic objects -/

/-- The integers `k` in the paper's interval `[X, X+R]`, that is `X < k ≤ X + R`. -/
noncomputable def kRange (X R : ℝ) : Finset ℕ :=
  (Icc 0 ⌈X + R⌉₊).filter (fun k => X < k ∧ (k : ℝ) ≤ X + R)

/-- `∑_{p2 + p3 = m, p2 ∈ [X2, X2+Y]} log p2 log p3`, with the extra condition `p2 ≡ a2 (q2)`. -/
noncomputable def binSumAP (X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (m : ℕ) : ℝ :=
  ∑ p ∈ (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ X2 < p ∧ (p : ℝ) ≤ X2 + Y ∧
      (p : ℤ) ≡ a2 [ZMOD q2]),
    Real.log p * Real.log ((m - p : ℕ) : ℝ)

/-- `∑_{p2 + p3 = m, p2 ∈ [X2, X2+Y]} log p2 log p3`. -/
noncomputable def binSum (X2 Y : ℝ) (m : ℕ) : ℝ := binSumAP X2 Y 1 0 m

/-- The twin prime type constant `∏_{p ≠ 2} (1 - 1/(p-1)^2)`, as a `tprod` over all primes.
The product converges absolutely, so `tprod` is its value. -/
noncomputable def twinC : ℝ :=
  ∏' p : Nat.Primes, (if (p : ℕ) = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- The binary singular series `S(r)` of the paper, display 2. -/
noncomputable def S (r : ℕ) : ℝ :=
  if Even r then 2 * twinC * ∏ p ∈ r.primeFactors.filter (· ≠ 2), (((p : ℝ) - 1) / ((p : ℝ) - 2))
  else 0

/-- The ternary singular series `T(n,q,a)` with one prime in an arithmetic progression,
as displayed after Theorem 2, written as a `tprod` over all primes of the local factor. -/
noncomputable def T (n q : ℕ) (a : ℤ) : ℝ :=
  (1 / (Nat.totient q : ℝ)) * ∏' p : Nat.Primes,
    (if ((p : ℕ) ∣ n ∧ ¬ (p : ℕ) ∣ q) ∨ (¬ ((p : ℕ) : ℤ) ∣ (n - a) ∧ (p : ℕ) ∣ q) then
        1 - 1 / ((p : ℝ) - 1) ^ 2
      else if ¬ (p : ℕ) ∣ n ∧ ¬ (p : ℕ) ∣ q then 1 + 1 / ((p : ℝ) - 1) ^ 3
      else (p : ℝ) / ((p : ℝ) - 1))

                                                                                 
                                                                          
                                                             
                                                                     
                                                                                                
                                                                    

                                                                                

                                                                                                
                                                                                 
                                                                                            
                                               
                                                                            
                                          
                                                                 

                                                                                  
                  
                                                                                
                                    
                                                                                                
                                                                                             
                                                                     
                      
                                                                     
                                                                           
                                                                                          
                                                                                               
                                                                   
                                                                                        

                                                                                               
                                                                                                 
                                                                                 
                                                                                 
                                                  
                                                                          
                                    
                          
                    
                                                                                    

end LeanLab.Halupczok2012
