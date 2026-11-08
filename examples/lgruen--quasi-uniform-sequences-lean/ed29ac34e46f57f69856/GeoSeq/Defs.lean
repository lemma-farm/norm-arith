/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited), sequel to "Low-discrepancy
quasi-uniform digital nets in every dimension" (the nets paper (hexagon:2610.00217v1)).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.DGSDefs

@[expose] public section

/-!
# GeoSeq stage S0: core definitions (`sec:prelim`, `sec:law`)

Shared by the statement files `GeoSeq/Statements/*.lean` and the proof files, so statements and
proofs use the same constants (house convention of the geo formalization, `*Defs` modules).

* Digital sequences over a finite commutative ring `R` whose digits are read through a code
  `enc : R ≃ Fin q` with `enc 0 = 0` (`DigitCode`; `sec:prelim`). Generator matrices are infinite:
  `C c n k` = row `n` (output digit, `0` most significant) and column `k` (index digit) of `C_c`.
* The point with index `v` (`seqPoint`, a real point of `[0,1]^s`, all digits), its cells
  (`cellIdx`), the `(0,s)`-sequence property in the block form of the paper (`IsSeq0`), and the
  separation of the full level `P_{sK}` (`SepAtLevel`, the statement `c(P_{sK}) ≥ LB`).
* The level law: digits of an index VECTOR (`vecDigit`) and the carry responses `D_i(l)` (entry
  `(c, c')`, `IsCarryEntry`), defined semantically as in `sec:law`.
* The one-coordinate certificate quantity `f_j` of `lem:cert` as an integer numerator
  (`gapNum`: `f_j(e, σ) = gapNum / q^j`), and its one-digit form over `ℤ/qℤ` (`gapNum1`).
* Self-similar scrambles (`def:selfsim`, `ssGen`), the brick walls `W^±` (`def:WF`, `WFgen`), and the
  base-2 sequence of `thm:B2` (`B2gen`).

Box membership is read off the digits (an elementary box with `d_c` digits in coordinate `c` is
the set of points whose first `d_c` digits encode `a_c`), as in geo `lem:nie`; this avoids the
ambiguity of digit expansions ending in `q-1, q-1, …` and agrees with the paper's convention.
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## Digit codes and digital sequences (`sec:prelim`) -/

/-- The fixed bijection `enc : R → {0, …, q-1}` of `sec:prelim`, with `enc 0 = 0`. -/
structure DigitCode (R : Type*) [Zero R] (q : ℕ) where
  enc : R ≃ Fin q
  enc_zero : ((enc 0 : Fin q) : ℕ) = 0

                                                                           
                                                         
        
                                              
                                
                                  
                                                                                   
                     

variable {R : Type*} [CommRing R] {q s : ℕ}

/-- Generator matrices of an `s`-dimensional digital sequence over `R`: `C c n k = C_c[n][k]`. -/
abbrev Gen (s : ℕ) (R : Type*) := Fin s → ℕ → ℕ → R

/-- Base-`q` index digit `v_k` of the index `v = ∑_k v_k q^k`, as an element of `R`. -/
def idxDigit [NeZero q] (D : DigitCode R q) (v k : ℕ) : R :=
  D.enc.symm ⟨v / q ^ k % q, Nat.mod_lt _ (NeZero.pos q)⟩

/-- Digit `n` of coordinate `c` of the point with index `v`: `y_{c,n}(v) = ∑_k C_c[n][k] v_k`
(the sum is finite: `v_k = 0` for `k > v` when `q ≥ 2`). -/
def seqDigit [NeZero q] (D : DigitCode R q) (C : Gen s R) (v : ℕ) (c : Fin s) (n : ℕ) : R :=
  ∑ k ∈ range (v + 1), C c n k * idxDigit D v k

/-- Coordinate `c` of the point `y(v) ∈ [0,1]`: `y_c(v) = ∑_n enc(y_{c,n}(v)) q^{-n-1}`. -/
noncomputable def seqCoord [NeZero q] (D : DigitCode R q) (C : Gen s R) (v : ℕ) (c : Fin s) : ℝ :=
  ∑' n : ℕ, ((D.enc (seqDigit D C v c n) : ℕ) : ℝ) / (q : ℝ) ^ (n + 1)

/-- The point `y(v)` of the digital sequence. -/
noncomputable def seqPoint [NeZero q] (D : DigitCode R q) (C : Gen s R) (v : ℕ) : Fin s → ℝ :=
  fun c => seqCoord D C v c

/-- The cell index of coordinate `c` with `d` digits: `∑_{n<d} enc(y_{c,n}(v)) q^{d-1-n}`. -/
def cellIdx [NeZero q] (D : DigitCode R q) (C : Gen s R) (v : ℕ) (c : Fin s) (d : ℕ) : ℕ :=
  ∑ n : Fin d, (D.enc (seqDigit D C v c n) : ℕ) * q ^ (d - 1 - (n : ℕ))

/-- The block `{y(v) : k q^m ≤ v < (k+1) q^m}` is a `(0,m,s)`-net: for every `d` with `∑_c d_c = m`,
every elementary box with `d_c` digits in coordinate `c` contains exactly one point of the block. -/
def BlockNet0 [NeZero q] (D : DigitCode R q) (C : Gen s R) (m k : ℕ) : Prop :=
  ∀ d : Fin s → ℕ, ∑ c, d c = m → ∀ a : Fin s → ℕ, (∀ c, a c < q ^ d c) →
    ∃! v : ℕ, (k * q ^ m ≤ v ∧ v < (k + 1) * q ^ m) ∧ ∀ c, cellIdx D C v c (d c) = a c

                                                                                                      
                                        
                                                                 
                              

                                                                                                  
                                                                                    
                      
                                                                        
                      

                                                                                                   
                                                                                                
                                                                           

                                                                                                   
                                                                                            
def SepAtLevel (q s K : ℕ) (pt : ℕ → Fin s → ℝ) (LB : ℝ) : Prop :=
  ∀ v w : ℕ, v < q ^ (s * K) → w < q ^ (s * K) → v ≠ w →
    LB ≤ (q : ℝ) ^ K * Z3NetDGS.torDist2 (pt v) (pt w)

                                                                                          
                                                          
                                                     
                                                                    

                                                                                              
                                                                                    

                                                                     
                                                                                
                    

                                                                                               

                                                                                           
                                                                                        

                                                                                         
                                   
                                                                                     
              
                                                           

                                                           

                                                                                                     
                                                                                               
           
def vecDigit {m : ℕ} (C : Gen s R) (V : Fin m → R) (c : Fin s) (n : ℕ) : R :=
  ∑ k : Fin m, C c n k * V k

/-- The carry pattern at level `K`: `1` on the `l` finest cell digits `K-l, …, K-1` of coordinate
`c'`, `0` on every other cell digit (`sec:law`; `1 ≤ l ≤ K`). -/
def carryPat (K l : ℕ) (c' c : Fin s) (n : ℕ) : R :=
  if c = c' ∧ K - l ≤ n ∧ n < K then 1 else 0

/-- `IsCarryEntry C K i l c c' d`: the entry `D_i(l)[c][c'] = d` of the carry response at level `K`
(`sec:law`): there is an index vector `V ∈ R^{sK}` whose cell digits (digits `0, …, K-1` of every
coordinate) are the carry pattern of coordinate `c'`, and every such `V` has the digit `K+i` of
coordinate `c` equal to `d`. (For a `(0, sK, s)`-net `V` is unique; by linearity, `d` is the change of
the geometric digit `K+i` of coordinate `c` when `1` is added to each of the `l` finest cell digits
of coordinate `c'`, which for prime `q` is the step of `n_{c'}` by `+1` with carry length `l`.) -/
def IsCarryEntry (C : Gen s R) (K i l : ℕ) (c c' : Fin s) (d : R) : Prop :=
  (∃ V : Fin (s * K) → R, ∀ c₁ : Fin s, ∀ n < K, vecDigit C V c₁ n = carryPat K l c' c₁ n) ∧
  ∀ V : Fin (s * K) → R, (∀ c₁ : Fin s, ∀ n < K, vecDigit C V c₁ n = carryPat K l c' c₁ n) →
    vecDigit C V c (K + i) = d

/-! ## The certificate quantity `f_j` (`lem:cert`) -/

/-- The integer `enc(R) = ∑_{i<j} enc(R_i) q^{j-1-i}` of a vector of `j` geometric digits. -/
def encVec (D : DigitCode R q) {j : ℕ} (r : Fin j → R) : ℕ :=
  ∑ i : Fin j, (D.enc (r i) : ℕ) * q ^ (j - 1 - (i : ℕ))

/-- Numerator of the guaranteed gap `f_j(e, σ)` of `lem:cert`:
`f_j(e, σ) = max(0, min_R |e q^j + enc(R ⊕ σ) - enc(R)| - 1) / q^j`, `⊕` digitwise in `R`
(truncated subtraction on `ℕ` gives the `max(0, ·)`). -/
def gapNum [Fintype R] [DecidableEq R] (D : DigitCode R q) (j : ℕ) (e : ℤ) (σ : Fin j → R) : ℕ :=
  ((univ.image fun r : Fin j → R =>
      ((e * (q : ℤ) ^ j + (encVec D (r + σ) : ℤ) - (encVec D r : ℤ)).natAbs)).min'
      (by simp)) - 1

                                                                                          
                                                                            
                                                          
                                
                                                                                   

                                                                      

                                                                                            
                                                                                              
def digInc [NeZero q] (D : DigitCode R q) (y : R) : R :=
  D.enc.symm ⟨((D.enc y : ℕ) + 1) % q, Nat.mod_lt _ (NeZero.pos q)⟩ - y

/-- The top digit `ȳ = enc⁻¹(q - 1)` (`rem:F4carry`). -/
def topDigit [NeZero q] (D : DigitCode R q) : R :=
  D.enc.symm ⟨q - 1, Nat.sub_lt (NeZero.pos q) Nat.one_pos⟩

/-- `δ_i(l, y)[c][c']` of `eq:carrychange`: the change of the geometric digit `K+i` of coordinate `c`
when the cell index of coordinate `c'` steps by `+1` with carry length `l`, stopping at a digit with
value `y`: `Δ(ȳ) D_i(l-1) + Δ(y) (D_i(l) - D_i(l-1))`, where `Dr i l = D_i(l)` (with `D_i(0) = 0`). -/
def carryChange [NeZero q] (D : DigitCode R q) (Dr : ℕ → ℕ → Fin s → Fin s → R) (i l : ℕ) (y : R)
    (c c' : Fin s) : R :=
  digInc D (topDigit D) * Dr i (l - 1) c c' + digInc D y * (Dr i l c c' - Dr i (l - 1) c c')

/-- `σ_c ∈ R^j` of `lem:cert` (general digit code): `σ_{c,i} = ∑_{c'} e_{c'} δ_i(l_{c'}, y_{c'})[c][c']`
(the terms with `e_{c'} = 0` vanish). -/
def certSigma [NeZero q] (D : DigitCode R q) (Dr : ℕ → ℕ → Fin s → Fin s → R) (j : ℕ)
    (e : Fin s → ℤ) (l : Fin s → ℕ) (y : Fin s → R) (c : Fin s) : Fin j → R :=
  fun i => ∑ c', (e c' : R) * carryChange D Dr i (l c') (y c') c c'

                                                                                           
                                                
                                                                                       
                              
                                              

                                                                                                 
                                                                          
def IsStep (K : ℕ) (e : Fin s → ℤ) (l : Fin s → ℕ) : Prop :=
  (∀ c, -1 ≤ e c ∧ e c ≤ 1) ∧ (∃ c, e c ≠ 0) ∧ ∀ c, 1 ≤ l c ∧ l c ≤ K

/-- One term of the certificate: `(∑_c f_j(e_c, σ_c)²)^{1/2}`, with `f_j = gapNum / q^j`. -/
noncomputable def certTerm [Fintype R] [DecidableEq R] (D : DigitCode R q) (j : ℕ) (e : Fin s → ℤ)
    (σ : Fin s → Fin j → R) : ℝ :=
  Real.sqrt (∑ c, ((gapNum D j (e c) (σ c) : ℝ) / (q : ℝ) ^ j) ^ 2)

/-! ## Self-similar scrambles and the constructions (`def:selfsim`, `def:WF`, `thm:B2`) -/

                                                                                           
                                                                                        
                                                                   
                                       

                                                                                                
                     
                                                                     
                               

                                                                                                     
                                                                                                  
                                                                             
                                                                    

                                                                                           
                                                                  
                                               
          
                                        
                                                                                  
                             

                                                                        
                                                                                         

                                                                                                 
                                                    
                                                                                           
                                                               
                                    

                                                                                                     
                                     
                                                                                           
                                                                           

                                                                                               
                                                                               
                           

                                                                                                    
                                
                                                                        

                         
                                                           

                                                                                     
                                                       
                                                      

                                                                                                     
                                                                       

                                                                  
                                                                 
                                                         

                                                                         
                                                           
                                                                        
                                              

                                                  

                                           
instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

                                                                                      
                                                          

                                                                                               
                                                       
                                                                  

                                                                                                         
                                                                             

                                                                        
                                                         

                                                                                                   
                           
             
                                                                              

                                                                                                
                 
                                      

                                                                                                
                                                                 

                                                                   

                                                                                                   
                
                                                                                                   
                                 

                                                   
                                                                                    
                                                                                                   
                                                                      
                                                                                                  
                                   
                             
                                                                                                       

                                                                                              
                                                                    
                                             
                                                                                   

                                                                             

                                                                                                      
                                      
                                                                              
                                             
                                  

                                                                                  
                                        
                                                                                          
                                                 

                                                                           
                                            
                                                                                          
                                                         

                                                                         
                                                                                       

                                                                                    
                                                                        
                                        

                                                                       

                                                                   
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

                                                                                               
                                                                                      
                                
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                     
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                     

end GeoSeq
