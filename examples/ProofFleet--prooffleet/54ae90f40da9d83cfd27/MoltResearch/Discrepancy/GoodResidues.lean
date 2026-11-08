import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Push

/-!
# Discrepancy: good residue classes for the Maier-style decoupling (Tao 2015 §4)

Pure `ℕ`-arithmetic substrate for the Maier-style decoupling step in Tao's resolution of
the Erdős discrepancy problem (arXiv:1509.05363, §4; issue #2871, PR H prep).

Following the paper: *"Call a residue class `a (q^k)` bad if `a + m` is divisible by
`p^k` for some `p ∣ q` and `1 ≤ m ≤ 2H`, and good otherwise."*  This file formalises
that notion (`IsGoodResidue`) and the elementary facts the §4 argument consumes:

- `gcd_add_eq_of_modEq`: the gcd `(n + m, q^k)` only depends on the residue class of
  `n (mod q^k)` — so goodness data transfers from `a` to every `n ≡ a (q^k)`.
- `gcd_dvd_pow_pred_of_good`: for a good class, `(a + m, q^k) ∣ q^{k-1}` for all
  `1 ≤ m ≤ 2H` (the paper's gcd rigidity chain, first display after the definition).
- `coprime_div_gcd_of_good`: moreover `(a + m)/(a + m, q^k)` is coprime to `q`.
- `card_not_goodResidue_le`: the bad-count.  The paper bounds the number of bad `a` by
  `2H ∑_{p ∣ q} q^k p^{-k}`; we prove the explicit crude form
  `#bad ≤ 2H · ω(q) · (q^k/2^k + 1)`, which is `o(q^k)` as `k → ∞` for fixed `q, H` —
  all the consumer needs.  `le_card_goodResidue` is the complementary lower bound.

No complex numbers and no characters here: everything is gcd/factorization/counting.
-/

namespace MoltResearch

/-- Tao 2015 §4: the residue class `a (mod q^k)` is **good** (for shift range `H`) if
`a + m` is *not* divisible by `p^k` for any prime `p ∣ q` and any `1 ≤ m ≤ 2H`. -/
def IsGoodResidue (q k H a : ℕ) : Prop :=
  ∀ m ∈ Finset.Icc 1 (2 * H), ∀ p : ℕ, p.Prime → p ∣ q → ¬ p ^ k ∣ (a + m)

/-- Goodness only involves primes `p < q + a + 2H + 2`: a prime divisor of `q ≠ 0` is at
most `q`; if `q = 0` (where every prime divides `q`) a huge prime power `p^k` with
`k ≥ 1` cannot divide `a + m ≥ 1`, and for `k = 0` the small witness `p = 2` already
decides the matter.  This bounded form makes `IsGoodResidue` decidable. -/
theorem isGoodResidue_iff_bounded (q k H a : ℕ) :
    IsGoodResidue q k H a ↔
      ∀ m ∈ Finset.Icc 1 (2 * H), ∀ p ∈ Finset.range (q + a + 2 * H + 2),
        p.Prime → p ∣ q → ¬ p ^ k ∣ (a + m) := by
  constructor
  · intro h m hm p _ hp hpq
    exact h m hm p hp hpq
  · intro h m hm p hp hpq hdvd
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    by_cases hlt : p < q + a + 2 * H + 2
    · exact h m hm p (Finset.mem_range.mpr hlt) hp hpq hdvd
    · -- a huge prime divisor forces `q = 0`, and then `p ^ k ∣ a + m` forces `k = 0`
      have hq0 : q = 0 := by
        rcases Nat.eq_zero_or_pos q with h0 | hqpos
        · exact h0
        · have := Nat.le_of_dvd hqpos hpq
          omega
      have hk0 : k = 0 := by
        rcases Nat.eq_zero_or_pos k with h0 | hkpos
        · exact h0
        · have h1 : p ≤ p ^ k := Nat.le_self_pow hkpos.ne' p
          have h2 : p ^ k ≤ a + m := Nat.le_of_dvd (by omega) hdvd
          omega
      have h2 := h m hm 2 (Finset.mem_range.mpr (by omega)) Nat.prime_two
        (by rw [hq0]; exact dvd_zero 2)
      rw [hk0, pow_zero] at h2
      exact h2 (one_dvd _)

instance instDecidableIsGoodResidue (q k H a : ℕ) : Decidable (IsGoodResidue q k H a) :=
  decidable_of_iff' _ (isGoodResidue_iff_bounded q k H a)

                                                                                       
                                                                                        
                       
                                                                           
                                                        
                        

                                                                                           
                                                   
                                                         
                              

                                                                                       
                                                                                       
                                                                                       
                                
                                                           
                                                                             
                                               
                                         
                                  
                                          
                                                                      
                                                                              
         
                                                                                
                            
                                                    
                               
                      
                                                                                    
                                        
                                      
                                          
                                                           
                                                        
                                                
                   
                                                                                      
                                                          
                                                
                           
                                                                                          

                                                                                  
                                                                               
                                                                                        
                    
                                                          
                                                                             
                                                           
                                         
                                  
                                          
                                                                      
                                                                                  
                                                       
                                                            
                
                                                                     
                                                                         
                                           
                                                                                     
                                                        
                                                                                          
                                              
                 
                                                                                    
                                         
                                                                  
                                                     
       

                                                                                  
                                                             
                                                           
                                                                       
                                             
                                                                 
                                                                 
                                                          
                                                                                     
                             
                             
              
                                                                         
                                             
                                                 
                                      
                                                                            
                                                      
                                                    
                                                          
                                       
                                                                               
                            
                                                                        
                                                                               
                                              
                                                     
                          
                       
       

                                                                   
                                                                                
                                                                                      
                                                                                 
                                                          
                                                          
                                                                         
                                                               
                                                                              
                                                        
                                                                                  
              
                                
                              
                                
                    
                                            
                           
                                                                                       
                                          
                                                                            
                                                         
                                                                                       
                                
                                                      
                                                                              
                              
                                                                                 
                               
                    
                                      
                                                                   
                                                                                   
                                     
                                                                     
                                                     
                                                                                   
             
                                                               
                                                                             
                             

                                                                                      
                                                                             
                                                      
                                                             
                                                                                 
                                                                                  
                                                                             
                                      
                                                                         
                                               
                                                        
                                         
       

end MoltResearch
