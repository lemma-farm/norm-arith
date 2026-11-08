import MoltResearch.Discrepancy.BandCapstone
import MoltResearch.Discrepancy.LevelSizes
import MoltResearch.Discrepancy.PrimeMassCell

/-!
# The level legs of the `[mrt]` A.2 inner band (Track R, A2-III, VI-2)

The A.2 capstone takes the first-index partition abstractly.  This module binds
that partition to the small-value sets of the e-adic cell polynomials and then
composes the already proved level estimates with the schedule arithmetic.
-/

namespace MoltResearch

/-- The prime polynomial carried by one e-adic cell of a level. -/
noncomputable def levelCellPoly (P : Finset ℕ) (N v : ℕ) (g : ℕ → ℂ)
    (xi : ℝ) : ℂ :=
  ∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
    * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)

/-! ## The exact level decomposition -/

/-- The noncollision fibre in the Ramaré decomposition of the typical-set
polynomial. -/
noncomputable def typicalSMainFibre (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (p : ℕ) (xi : ℝ) : ℂ :=
  (g p / (p : ℂ))
      * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)
      * ∑ m ∈ (((typicalS A B rest).filter (fun n => p ∣ n)).image (· / p)).filter
          (fun m => ¬ p ∣ m),
        ((g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          / (((P.filter (· ∣ m)).card : ℂ) + 1)

/-- The repeated-prime fibre left by the Ramaré decomposition. -/
noncomputable def typicalSCollision (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (xi : ℝ) : ℂ :=
  ∑ p ∈ P, ∑ m ∈ (((typicalS A B rest).filter
      (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
    ((g (p * m) / ((p * m : ℕ) : ℂ))
        * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ))
      / (((P.filter (· ∣ (p * m))).card : ℂ))

                                                                             
                                                             
                                                      
                                      

                                                                   
                                                               
                    
                                                               

                                                                          
                                                            
                                                    
                                                                           
            
                                                             
                                   
                                      
                                                        
                                                            
                                                                         

                                                                            
                                                  
                                                    
                                          
           
                           
                                                          
                
                                                                   
                          
                                                        

                                                              

                                                                        
                                                                        
                                                                      
                                                                       
  
                                           
                                        
                                                            
                                                               
                                           
                                        
                                                                               
                                                  
                            
                                                                             
                              
                                                             
                                                  
                                                                             
           
                                                                      
                                       
                                                           
                                                  
                              
                                                                
                                                          
                                     
                                            
                                                                   
                                        
                        
                                                                                   
                                             
                                                  
                           
           
            
      

                                                                      
                                                              
                     
                                                                      

                                                                            
                                                         
                                                                   
                     
                                                       
                                            
                                                                

                                                                                 
                                                  
                                        
                                                               
                                     
                                          
                                                     
           
                          
                                             
                                                                          

                                                           
                                                 
                                             
                             
                                                         
                                                     

                                                                  
                                    
                                        
                                      
                                                       
                          
                                                                     
                                                         
                                                     

                                                                      
                                                    
                                                         
                             
                                                         
                             

                                    
                                                                 

                                                                          
                                                                          
                                                                         
                                                                
  
                                                     
                                     
                                       
                                           
                                             
                          
                                                                          
                               
                             
                                               
                                                                         
                                        
           
                                                               
                                                                            
                            
                                              
                                                                    
                                                                      
                                                                           
                                                  
                                                                   
                                                        
                                                                           
                                              
                                           
                                                               
                       
                                                                       
                                
                                                                        
            
                            
                       
                                             
                  
        
                                                           
                                                   
                                           
                                                                  
                       
                                           
                                      
                                                                                   
                                              
                    
                                                             
                                                                                              
                                                        
                                   
        
                                                                   
                                                   
                                                            
      
                                                                          
                                                    
                                                                               
                                               
                    
                                                           
     
                          
                                                         
                                                  
                        
                                               
                                      
                                                 
                
                  
                               
                             
                                               
                                                    

                                                                             
                                                
                                                          
                              
                                  
                                
                                                               
                                                             
                                 

                                    
                                                                       

                                                                       
                                                                           
                                                                            
                                
  
                                                     
                                     
                                       
                                          
                              
                                                   
                                                                        
                                                         
                                                                   
                                                     
                                                     
                                   
                                              
                                                         
           
      
                                                                        
                                                              
                                                                      
                                               
                    
                                               
                                                       
                                           
                                    
                                        
                              
                                                                                
                                    
                                        
                                      
                                 
                                                   
                                            
                                                    
                                             
                           
                                                                          
                                                      
                                                          

                                                                            
                                                                    
                    
                                                                 

                                                                  
                                                       
                                                    
                                               
           
                                
                         
                                           
                                                                            
                                                       
                                                     
                                                      
                                                                         
                           
             
        
                                       
                      
                                                                               
             

                                                                           
                                                              
                                                                   
                     
                                                       
                                                 
                                                                

                                                                               
                                            
                                        
                                                            
                    
                                                                   
                                            
                                                                     
                          
                                                                       
                                                 
                                                                                  
           
                                                                      
                                       
                                                    
                                                     
                                            
                                                                   
                                        
                     
                                                                             
                                                                        
                                
           
            

                                                                         
                                         
                                        
                                      
                                                            
                               
                                                                     
                                                         
                                                     

                                    
                                                                        
                           
                                                   
                                       
                                             
                  
                                                                  
                                     
                          
                                          
                                  
                                                                        
                               
                             
                                               
                                               
           
                                                      
                            
                                              
                                                                    
                                                                   
                                                        
                                                                           
                                              
                                           
                                                               
                       
                         
                                                    
                                                                  
                                   
                                                                        
            
                       
                                             
                   
        
                                                           
                                                    
                                            
                                                                  
                       
                                           
                                      
                                                                                   
                                               
                     
                                                             
                                                         
                                                         
                                    
        
                                                                    
                                                   
                                                            
      
                                          
                                  
                                                                        
                                                     
                                                                               
                                               
                    
                                                           
                        
                                                       
                                                 
                        
                                             
                                    
                                               
              
                
                               
                             
                                               
                                                    

                                                                          
                      
                                                          
                                     
                                       
                                           
                                             
                          
                                                                               
                               
                             
                                               
                                                                         
                                        
                                                                           
                                                          
                                                                            
                                                      
                                   
                                                       

open Finset in
/-- **The exact typical-set decomposition, grouped by e-adic cells.**

The useful first half of the decomposition is purely algebraic:
`typicalS_phase_main_add_coll` supplies the corrected `1/(ω+1)` quotient
weight and the repeated-prime term, while disjointness of `eadicCell` changes
the outer prime sum into the level's cell range.  No estimate and no enlarged
quotient block enters this equality.

The cover is kept explicit because the analytic schedule normally indexes only
the cells between its endpoints `v₀` and `v₁`, rather than every cell from
zero. -/
theorem typicalS_phase_eq_eadic_main_add_collision
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A B : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (xi : ℝ) :
    ∑ m ∈ typicalS A (A + B) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
      = (∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          ∑ p ∈ eadicCell P (2 * N) v,
            typicalSMainFibre g A (A + B) P rest p xi)
        + typicalSCollision g A (A + B) P rest xi := by
  classical
  rw [typicalS_phase_main_add_coll g hcm A B P hP rest xi]
  change (∑ p ∈ P, typicalSMainFibre g A (A + B) P rest p xi)
      + typicalSCollision g A (A + B) P rest xi = _
  congr 1
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.Ico v₀ (v₁ + 1)) : Set ℕ) (eadicCell P (2 * N)) :=
    fun v _ w _ hvw => eadicCell_disjoint P (2 * N) hvw
  calc
    ∑ p ∈ P, typicalSMainFibre g A (A + B) P rest p xi =
        ∑ p ∈ (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)),
          typicalSMainFibre g A (A + B) P rest p xi := by
            rw [hcov]
    _ = ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          ∑ p ∈ eadicCell P (2 * N) v,
            typicalSMainFibre g A (A + B) P rest p xi :=
      Finset.sum_biUnion hdisj

              
                                                                              

                                                                           
                                                                           
                                                                           
                                                                            
                                                                        
                                          
  
                                                                   
                                                   
                                                        
                                          
                                                                       
               
                                
                                                   
                                                                       
                          
                                                                       
                                                  
                                                     
                           
                                                                       
              
                                                             
                                                                
                                      
                                      
                            
                                                                         
                                                            
                                 
                                                                              
                                                           
                                                                                
            
         
                                            
                                            
                          
                                          

                                    
                                                        

                                                                            
                                   
                                                                 
                                                                         
                                                                            
  
                                                            
                                                   
                                                        
                                          
                                                                       
                                               
                                
                                                          
                       
                                                                        
                       
                                        
                                        
                                                                 
                         
                                                                  
           
                                                
                                                               
                                                                                
                                                 
                                                         
           
                            
                                                             
                                                
                                                                 
                                       
                                   
                                    
                                                             
                                            
                                                 
                                            
                                                       
                            
                                                
                                                
                                                                           
      
                                                          
                       
                                                                        
                    
                                           
                                            
                                                                
                                                                      
                                         
                    
                                               
                                                                          
                                    
                       
                                        
                                        
                                                                 
                         
                                                               
                                                                 

                                   

                                                                    
                                                  
noncomputable def typicalSQuotCoeff (g : ℕ → ℂ) (P S : Finset ℕ)
    (m : ℕ) : ℂ :=
  if m ∈ S then g m / (((P.filter (· ∣ m)).card : ℂ) + 1) else 0

                                                                  
                                                 
                                                    
                                         
           
                          
           
                 
                                                   
                                                 
                                                  
                                                                     
                             
               
          
                                         
                          
                                                                     
               
        

                                                                     
                                                              
                                             
                                                      
                                                                   
                                                     
           
                                         
                                    
                                                                       
                              
                                                     
                                                      
                                                       
                                             

                                                                  

                                                                            
                                                                              
                                                                              
                                                                   
                                                        
  
                                                  
                                              
                                    
                                                      
                                                                    
                                                                         
              
                                                 
                                                                     
                        
                                                                     
                                                
                                                   
                                               
                                                                          
           
                                  
                                           
                     
                                              
        
                                

                                                                            

                                                                             
                                                                           
                                                                           
                                                                       
                                                   
  
                                          
                                          
                            
                                          
                                      
                                   
                                                             
             
                
                                                 
                                
                            
                                                            
                           
                                                                         
                                                                         
                                                                     
                
                                                 
                                
                           
                             
                                                                  

                                                                     
          

                                                                             
                                                                              
                                                                           
                                                                                 
                                        
  
theorem typicalS_fibre_image_eq_quotient_support
    (A B p : ℕ) (hp : 0 < p) (rest : List (Finset ℕ))
    (hstable : ∀ m, HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m) :
    ((typicalS A B rest).filter (fun n => p ∣ n)).image (· / p)
      = (Finset.Ioc (A / p) (B / p)).filter
          (fun m => m ∈ typicalS 0 B rest) := by
  classical
  ext m
  constructor
  · intro hm
    rw [Finset.mem_image] at hm
    obtain ⟨n, hn, hnm⟩ := hm
    rw [Finset.mem_filter] at hn
    have hnEq : n = p * m := by
      calc
        n = p * (n / p) := (Nat.mul_div_cancel' hn.2).symm
        _ = p * m := by rw [hnm]
    rw [Finset.mem_filter, Finset.mem_Ioc]
    rw [mem_typicalS] at hn
    subst n
    have hlo : A / p < m := by
      apply (Nat.div_lt_iff_lt_mul hp).mpr
      rw [mul_comm]
      exact hn.1.1.1
    have hhi : m ≤ B / p := by
      apply (Nat.le_div_iff_mul_le hp).mpr
      rw [mul_comm]
      exact hn.1.1.2
    exact ⟨⟨hlo, hhi⟩, (mem_typicalS.mpr
      ⟨⟨lt_of_le_of_lt (Nat.zero_le (A / p)) hlo,
          le_trans hhi (Nat.div_le_self B p)⟩,
        (hstable m).mp hn.1.2⟩)⟩
  · intro hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    rw [mem_typicalS] at hm
    rw [Finset.mem_image]
    refine ⟨p * m, ?_, Nat.mul_div_cancel_left m hp⟩
    rw [Finset.mem_filter, mem_typicalS]
    have hlo : A < p * m := by
      have := (Nat.div_lt_iff_lt_mul hp).mp hm.1.1
      simpa [mul_comm] using this
    have hhi : p * m ≤ B := by
      have := (Nat.le_div_iff_mul_le hp).mp hm.1.2
      simpa [mul_comm] using this
    exact ⟨⟨⟨hlo, hhi⟩, (hstable m).mpr hm.2.2⟩, dvd_mul_right p m⟩

/-- Under the same stability condition, the full quotient image carries the
fixed zero-extended Ramaré coefficient. -/
theorem typicalS_full_fibre_eq_block
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (p : ℕ) (hp : 0 < p)
    (hstable : ∀ m, HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (xi : ℝ) :
    (∑ m ∈ ((typicalS A B rest).filter (fun n => p ∣ n)).image (· / p),
        ((g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          / (((P.filter (· ∣ m)).card : ℂ) + 1))
      = ∑ m ∈ Finset.Ioc (A / p) (B / p),
          (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ) := by
  classical
  rw [typicalS_fibre_image_eq_quotient_support A B p hp rest hstable,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m ∈ typicalS 0 B rest
  · simp only [hm, if_true, typicalSQuotCoeff]
    ring
  · simp [hm, typicalSQuotCoeff]

/-- The `p ∣ m` terms added when a noncollision fibre is enlarged to its full
quotient support, grouped over the same e-adic cells as the main term. -/
noncomputable def typicalSAddedTerms (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (xi : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
    ((g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
      * ∑ m ∈ (((typicalS A B rest).filter
          (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
        ((g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          / (((P.filter (· ∣ m)).card : ℂ) + 1)

              
                                                                 

                                                                       
                                                                           
                                                            
  
                                                   
                                        
                                                    
                 
                                                                       
              
                                              
                                          
                                                          
           
                                   
                                                                  
                                                       
      
                                              
                                                                    
                                     
                                                              
                                   
                                                   
                                                    
                                                                 
                                                 
                                                                     
                                   
                                                         
                                     
                                          
                                                                    

                                    
                                                                       
                                                      
                                     
                                       
                                          
                              
                                          
                                                                       
                          
                     
                                                                 
                                                         
                                                                   
                                                     
                                                     
                                   
                                                   
                                                              
           
      
                     
                                                                 
                                                              
                                                                           
                                               
                    
                                               
                                                        
                                                        
                                    
                                        
                              
                                                                                     
                                    
                                        
                                      
                                 
                                                   
                                            
                                                    
                                             
                           
                                                                               
                                                      
                                                          

open Finset in
/-- **The N3-f main term in the full block shape consumed by II-2e.**

Enlarge every noncollision quotient fibre by the omitted `p ∣ m` terms.  The
stability hypothesis identifies the enlarged support with
`Ioc (A/p) (B/p)` carrying the single coefficient
`typicalSQuotCoeff g P (typicalS 0 B rest)`.  Subtracting the added terms from
N3-f's repeated-prime term preserves equality, leaving exactly a full
prime-block main term plus one adjusted collision error.
-/
theorem typicalS_phase_eq_eadic_prime_block_add_adjusted_collision
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (xi : ℝ) :
    ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
      = (∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          ∑ p ∈ eadicCell P (2 * N) v,
            ((g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * (∑ m ∈ Finset.Ioc (A / p) ((A + Delta) / p),
                  (typicalSQuotCoeff g P (typicalS 0 (A + Delta) rest) m /
                      (m : ℂ))
                    * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))
        + (typicalSCollision g A (A + Delta) P rest xi
            - typicalSAddedTerms g A (A + Delta) P rest N v₀ v₁ xi) := by
  rw [typicalS_phase_eq_eadic_main_add_collision g hcm A Delta P hP rest N v₀ v₁
    hcov xi]
  have hfull :
      (∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          ∑ p ∈ eadicCell P (2 * N) v,
            ((g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * (∑ m ∈ Finset.Ioc (A / p) ((A + Delta) / p),
                  (typicalSQuotCoeff g P (typicalS 0 (A + Delta) rest) m /
                      (m : ℂ))
                    * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))
        = (∑ v ∈ Finset.Ico v₀ (v₁ + 1),
            ∑ p ∈ eadicCell P (2 * N) v,
              typicalSMainFibre g A (A + Delta) P rest p xi)
          + typicalSAddedTerms g A (A + Delta) P rest N v₀ v₁ xi := by
    unfold typicalSAddedTerms
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpP := (mem_eadicCell.mp hp).1
    have hp0 := (hP p hpP).pos
    rw [← typicalS_full_fibre_eq_block g A (A + Delta) P rest p hp0
      (hstable p hpP) xi]
    unfold typicalSMainFibre
    rw [← mul_add]
    congr 1
    have hpart := Finset.sum_filter_add_sum_filter_not
      (((typicalS A (A + Delta) rest).filter
        (fun n => p ∣ n)).image (· / p)) (fun m => ¬ p ∣ m)
      (fun m => ((g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
        / (((P.filter (· ∣ m)).card : ℂ) + 1))
    simpa only [not_not] using hpart.symm
  rw [hfull]
  ring

/-- The full prime-indexed quotient-block main term obtained from N3-f. -/
noncomputable def typicalSPrimeBlock (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (xi : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
    ((g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
      * (∑ m ∈ Finset.Ioc (A / p) (B / p),
          (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))

/-- The adjusted collision: N3-f's repeated-prime term minus the terms added
to make every main fibre a full quotient block. -/
noncomputable def typicalSAdjustedCollision (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (xi : ℝ) : ℂ :=
  typicalSCollision g A B P rest xi - typicalSAddedTerms g A B P rest N v₀ v₁ xi

/-- The full-block decomposition in named-function form, ready for the energy
lemmas. -/
theorem typicalS_phase_eq_primeBlock_add_adjustedCollision
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (xi : ℝ) :
    ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
      = typicalSPrimeBlock g A (A + Delta) P rest N v₀ v₁ xi
        + typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi := by
  simpa [typicalSPrimeBlock, typicalSAdjustedCollision] using
    typicalS_phase_eq_eadic_prime_block_add_adjusted_collision
      g hcm A Delta P hP rest N v₀ v₁ hcov hstable xi

                                                                 
                                                           
                                                           
                                                              
           
                                                
                                                               
                                                                                
                           
                                              
                                              
                                                           
                                          
                                             

                                                         
theorem continuous_typicalSAdjustedCollision (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) :
    Continuous (typicalSAdjustedCollision g A B P rest N v₀ v₁) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  unfold typicalSAdjustedCollision typicalSCollision typicalSAddedTerms
  apply Continuous.sub
  · refine continuous_finsetSum _ fun p _ => ?_
    refine continuous_finsetSum _ fun m _ => ?_
    exact (continuous_const.mul (hchar (Real.log (p * m : ℕ)))).div_const _
  · refine continuous_finsetSum _ fun v _ => ?_
    refine continuous_finsetSum _ fun p _ => ?_
    refine (continuous_const.mul (hchar (Real.log p))).mul ?_
    refine continuous_finsetSum _ fun m _ => ?_
    exact (continuous_const.mul (hchar (Real.log m))).div_const _

                                                                   
                                                          
                                             
                                                     
           
                          
                                              
                                              
                                                          
                                                                  

                                                                     
                                                           
                                                           
                                                              
           
                           
                                              
                                              
                                                           
                                                             
                                              
                                                          
                                                                  

                             
                                                                              

                                                                           
                                                                       
                                                                             
                          
  
                                                             
                                     
                                       
                                          
                              
                                          
                                                                       
                          
                     
                                                                        
                                                             
                                                   
                                                            
                                                                    
                                                         
                                                                      
           
                                                                          
                              
                                                                          
                                           
                                             
                                                       
                                                     
                                         
                                                 
                                                      
                                      
                                                            
                                      
                                                           
                                   

                     
                                                                        

                                                                           
                                                                       
                                                                             
                                    
  
                                           
                                     
                                       
                                          
                              
                                          
                                                                       
                                                               
                          
                                                           
                                        
                   
                                                                        
                                           
                                                                
                                         
                                             
                                          
                                                 
                           
                 
                                                                         
                                                   
          

                                               
                                             
                                                                
                                   
                          
                                     
                                                 
                                                                   
                                                                    

                                                     
                                             
                                                           
                                    
                                     
                                   
                                                      
                                                          
                                                                
                                                                  
                                                                 
                                                                   

                                    
                                                                    

                                                                         
                                                                            
                                                                     
                                                                             
                                            
  
                                                               
                                                                         
                                                         
                                          
                                                       
                                                                       
                            
                                                          
               
                                                                        
                                             
                                          
                                           
                                        
                                                           
                                        
                                  
                                                    
                                                            
                                              
                                                     
                                             
                                                          
                       
                                                                        
                                                          
                                                                         
                                                                  
                         
                                                                                    
                                                              
                                                                       
                                                                 
                                                                               
                                                                
                            
                                                                 
                                                                    
                                                                        
                                                      
                                                 
                                                                      
                       
                                                                        
                       
                                                                     
                         
                                                                                  
        
                                                            
                         
                                                                          
                                                                          
                                                                                    
                                         
                    
                                               
                                                               
                                                               
                                             
                                                                      
                                                                             
                   
      
                                                          
                       
                                                                        
                       
                                                                     
                         
                                                                                      
                                                                         
                                                                     
                         
                                                                                  
            
               
               
          

                                                                             
                                                      
noncomputable def typicalSCellUniformMain (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (q : ℕ → ℕ) (xi : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
    levelCellPoly P N v g xi
      * (∑ m ∈ Finset.Ioc (A / q v) (B / q v),
          (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))

/-- The endpoint-replacement error between every prime's quotient block and
its cell representative's block. -/
noncomputable def typicalSCellReplacement (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (q : ℕ → ℕ) (xi : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
    ((g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
      * ((∑ m ∈ Finset.Ioc (A / p) (B / p),
            (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
        - (∑ m ∈ Finset.Ioc (A / q v) (B / q v),
            (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))

/-- The full prime block is exactly its cell-uniform main plus the replacement
error. -/
theorem typicalSPrimeBlock_eq_cellUniform_add_replacement
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (q : ℕ → ℕ) (xi : ℝ) :
    typicalSPrimeBlock g A B P rest N v₀ v₁ xi
      = typicalSCellUniformMain g A B P rest N v₀ v₁ q xi
        + typicalSCellReplacement g A B P rest N v₀ v₁ q xi := by
  classical
  unfold typicalSPrimeBlock typicalSCellUniformMain typicalSCellReplacement levelCellPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **The final pointwise level decomposition.**

The typical-set polynomial is the cell-uniform main plus a combined error
consisting of the II-2e endpoint replacement and the adjusted N3-f collision.
This is the exact two-term shape consumed by
`typicalS_level_leg_le_budget_of_decomposition`.
-/
theorem typicalS_phase_eq_cellUniform_add_errors
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ) (xi : ℝ) :
    ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
      = typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q xi
        + (typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q xi
          + typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi) := by
  rw [typicalS_phase_eq_primeBlock_add_adjustedCollision
    g hcm A Delta P hP rest N v₀ v₁ hcov hstable xi,
    typicalSPrimeBlock_eq_cellUniform_add_replacement]
  ring

/-- The cell-uniform main is continuous in frequency. -/
theorem continuous_typicalSCellUniformMain
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ) (rest : List (Finset ℕ))
    (N v₀ v₁ : ℕ) (q : ℕ → ℕ) :
    Continuous (typicalSCellUniformMain g A B P rest N v₀ v₁ q) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  unfold typicalSCellUniformMain levelCellPoly
  refine continuous_finsetSum _ fun v _ => Continuous.mul ?_ ?_
  · exact continuous_finsetSum _ fun p _ =>
      continuous_const.mul (hchar (Real.log p))
  · exact continuous_finsetSum _ fun m _ =>
      continuous_const.mul (hchar (Real.log m))

/-- The cell-replacement error is continuous in frequency. -/
theorem continuous_typicalSCellReplacement
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ) (rest : List (Finset ℕ))
    (N v₀ v₁ : ℕ) (q : ℕ → ℕ) :
    Continuous (typicalSCellReplacement g A B P rest N v₀ v₁ q) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  unfold typicalSCellReplacement
  refine continuous_finsetSum _ fun v _ => ?_
  refine continuous_finsetSum _ fun p _ => ?_
  refine (continuous_const.mul (hchar (Real.log p))).mul ?_
  apply Continuous.sub
  · exact continuous_finsetSum _ fun m _ =>
      continuous_const.mul (hchar (Real.log m))
  · exact continuous_finsetSum _ fun m _ =>
      continuous_const.mul (hchar (Real.log m))

                                    
                                                                        
              

                                                                             
                                                                         
                                                                            
                                                               
  
                                                      
                                                             
                                                                      
               
                                                                        
                        
                                          
                                           
                                        
                                                           
                                        
                                                           
                                                            
                                
                                                                        
                                                        
                                                    
                                  
                                
                      
                                                                   
                                             
                             
                                                                         
                                                  
                             
                                                                          
                                                                 
             
                                                  
                                                                 
                                                                                  
                                                
                                                             
                            
                                              
                                                 
                                                    
                                                  
                                                              
                                                        
                                                              
                                                                
                                                               
                                                                  
                                                            
                                                                      
                                                                             
                                                                              

open MeasureTheory in
/-- **The complete capstone-facing level leg, with the three analytic costs
separated.**

The exact decomposition supplies a cell-uniform main, the II-2e endpoint
replacement, and the adjusted repeated-prime collision.  If their square-split
energies cost shares `κ_main`, `κ_replace`, and `κ_collision`, then the two
successive `L²` triangles make the total unweighted cost
`2(κ_main+κ_replace+κ_collision)`.  Multiplying once by `(4H/A)²` and
checking that against `2⁻⁽ʲ⁺¹⁾` gives exactly the `hleg` shape of
`band_energy_typicalS_le`.

`band_energy_level_one_main_le_budget` or the later-level ladder supplies
`hmain`; `setIntegral_norm_sq_typicalSCellReplacement_le` followed by
`eadic_replacement_error_le_budget` supplies `hreplacement`.  The remaining
`hcollision` is deliberately separate because M-10 is a collar theorem, not a
repeated-prime theorem.
-/
theorem typicalS_level_leg_le_budget
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta H : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ)
    (K₁ K₂ T : ℝ) (J j : ℕ) (Pset : ℕ → Set ℝ)
    (hPset : ∀ i, MeasurableSet (Pset i))
    (hpartT : bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
      ⊆ Set.Ioc (-T) T)
    (kappaMain kappaReplacement kappaCollision c₃ eps : ℝ)
    (hc₃ : 0 ≤ c₃)
    (hmain : (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hreplacement : 2 * (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ kappaReplacement * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hcollision : 2 * (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
      ≤ (1 : ℝ) / 2 ^ (j + 1)) :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (∫ xi in bandPartOn Pset J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (1 / 2 ^ (j + 1))
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  let Gpart := bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
  let main := typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q
  let replacement := typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q
  let collision := typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁
  have hGpart : MeasurableSet Gpart :=
    bandPartOn_measurableSet Pset hPset J _ (measurableSet_inner_band K₁ K₂) j
  have herror : 2 * (∫ xi in Gpart, ‖replacement xi + collision xi‖ ^ 2)
      ≤ (2 * (kappaReplacement + kappaCollision))
        * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    have hsplit := ExpSums.setIntegral_norm_add_sq_le replacement collision
      (continuous_typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q)
      (continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁)
      T Gpart hGpart hpartT
    change 2 * (∫ xi in Gpart, ‖replacement xi‖ ^ 2)
      ≤ kappaReplacement * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
      at hreplacement
    change 2 * (∫ xi in Gpart, ‖collision xi‖ ^ 2)
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
      at hcollision
    linarith
  let F : ℝ → ℂ := fun xi =>
    ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
      * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
  let error : ℝ → ℂ := fun xi => replacement xi + collision xi
  have houter : (∫ xi in Gpart, ‖F xi‖ ^ 2)
      ≤ 2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
        + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2) := by
    calc
      (∫ xi in Gpart, ‖F xi‖ ^ 2) =
          ∫ xi in Gpart, ‖main xi + error xi‖ ^ 2 := by
            apply setIntegral_congr_fun hGpart
            intro xi _
            exact congrArg (· ^ 2) (congrArg norm
              (typicalS_phase_eq_cellUniform_add_errors
                g hcm A Delta P hP rest N v₀ v₁ hcov hstable q xi))
      _ ≤ _ := ExpSums.setIntegral_norm_add_sq_le main error
        (continuous_typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q)
        ((continuous_typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q).add
          (continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁))
        T Gpart hGpart hpartT
  change (∫ xi in Gpart, ‖main xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) at hmain
  change 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)
      ≤ 2 * (kappaReplacement + kappaCollision)
        * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) at herror
  have hB0 : 0 ≤ bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) :=
    bandBudget_nonneg c₃ eps _ hc₃ (by positivity)
  have hparts : 2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
        + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)
      ≤ (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    calc
      2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
          + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)
        ≤ 2 * (kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
            + 2 * (kappaReplacement + kappaCollision)
              * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by linarith
      _ = _ := by ring
  change (4 * (H : ℝ) / (A : ℝ)) ^ 2 * (∫ xi in Gpart, ‖F xi‖ ^ 2)
    ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
  calc
    (4 * (H : ℝ) / (A : ℝ)) ^ 2 * (∫ xi in Gpart, ‖F xi‖ ^ 2)
      ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * (2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
            + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left houter (sq_nonneg _)
    _ ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * ((2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))) :=
        mul_le_mul_of_nonneg_left hparts (sq_nonneg _)
    _ = ((4 * (H : ℝ) / (A : ℝ)) ^ 2
          * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision))
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by ring
    _ ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) :=
      mul_le_mul_of_nonneg_right hshare hB0

                     
                                                                             

                                                                          
                                                      
                                                                       
                                                                         
  
                                                     
                                                                         
                                         
                                          
                              
                                          
                                                                       
                            
                                                          
               
                                                           
                                         
                                                                  
                       
                                                          
                  
                                       
                                           
                                                                            
                                                              
                                                  
                                           
                                                                            
                                                                     
                                                                    
                                                                   
                                         
                                                                     
                                
                               
                                    
                                               
                                                                    
                                                                          
                         
                                                           
                                                                      
                                                
                                                                           
                                                                           
                            
                                                            
                                                                        
                

                                    
                                                         

                                                                              
                                                                            
                                                                         
                                                                           
                                                                
  
                                            
                                                               
                                             
                                                 
                                           
                                  
                                                    
                        
                                                                  
                                                              
                         
                                       
                                                                  
                                                     
                                
                                                            
                                  
                                       
                                                  
                                                      
                                                
                               
                                                                 
                                    
                                                                 
                                                         
                                          
                                                
                               
                        
                                   
                                                           
                                                     
                                            
                                              
                                
                                                  
                                                   
                                                                               
                                           
                                                                          
                                                                                
                                                                          
                                           
                                          
                                                                            
                                    
                        
                       
                                                                         
                          

                                    
                                                                       
                      

                                                                         
                                                    
                                                                          
                                                                          
                                                                   

                                                                   
                                                                             
                                                                        
  
                                        
                                                     
                                           
                                     
                                                          
                                          
                                           
                                                      
                                 
                                   
                                                         
                                                             
                              
                        
                                                                  
                                  
                                           
                                                                 
                     
                                                                
                                                     
                                      
                                                               
                           
                                                          
                                             
                                                     
                                                         
                          
                                                                
                                
                                                           
                                                         
                                
                                                    
                                                     
                                             
                                                              
                                                         
                                                
                                  
                                                                   
                                  
                                        
                                              
                                      
                          
                                                        
                                                                               
                                           
                                  
                                                
                               
                                      
                                      
                                          
                                                  
                                                                       
                                
                 
              
                                                               
                                                
                                 
                                                           
                                                                       
                
                                                     
                                                                              
                                         
                                                             
                                                                           
                                                             
                                  
                                                 
                                                
                                                                          
                                                     
                  
                                                                   
                               
                                                   
                                     
                                                                  
                                       
                                           
                                                                       
                                                         
                                                                     
                                  
                                                 

                     
                                                               

                                                                        
                                                                           
                                                                              
                                                                        
                                                                           

                                                                          
                                                                              
                                                          
  
                                            
                                                     
                                        
                                                                  
                                                   
                                                  
                                                  
                                       
                                          
                                             
                                           
                                                          
                                
                                           
                                         
                                         
                                       
                                      
                                               
        
                               
                                                   
                                           
                        
                                                                   
                                        
                                              
                                                                                
                                              
                                         
                                                                  
        
                                    
                                           
                                                 
                                                               
                                                                         
      
                                
                                            
                                               
                                            
                                          
                                     
                                            
                                           
                                            
                                        
                                           

                     
                                                                     

                                                                              
                                                                          
                                                                         
                                                    
                                                                          
                                                                            
                                                                            
                               
  
                                                     
                                                          
                                              
                                         
                                                                  
                       
                                                   
                                
                     
                                                           
                                                           
                                                                   
                             
                                                    
                                       
                                                          
                                                              
                                            
                                                           
                                                               
                                         
                                                                 
                               
                                    
                                               
                                                               
                                                                          
                         
                                                           
                  
                                                        
                               
                                                                              
                                            
                                                                   
                                                               
                                                    
                                                      
                                                          
                                                         

                                                                      
                      
                                                                    
                                                  
                                           
                                      
                                                              

                                 
                                                    
                                      
                                            
                                         
                                          
                                                                    
         

                                                 
                                   
                                                    
                             
                                                           
           
                                              
                                         
                                                    
                                                                     
          
         
                                                  
                                        
                                                                   
                                                                   

                                                                             
        
                                             
                                                    
                                                  
                 
                                                                     
                                       
                                        
                                                                     
                                              
               

                                                                          
                                                           
                                                
                                                    
                                                  
                               
                                                                     
                                                   
                                           
                                     
                                                              
                                              
                                                                 
           
                                      
                                                  
                                                      
                   
             

                                                                 

                                                                          
                      
                                                                    
                         
                                                        
                                 

                                                
                                                            
                            
                                                    
                                         
                                                         
                                                                     

                                                                            
                                                                   
                                    
                                                    
                                                            
                                                            
                                                       
                                                                    
                                                               
                           
                                                                 
        

                                                                           
                 
                                        
                                                    
                                                              
                                                                                  
           
                           
       
                                       
                                                                       
                                                        
                               
                                                        
                                         
                                                        
                             

                                                                     
                                            
                                                    
                                                   
                                                  
                                                              
           
                           
       
                          
                            

                                                                     
                                
                                                    
                                                 
                                                       
                                                                        
                                         
                                   
                                                            
                                            
               

                                                    
                                           
                                                    
                                                 
                
                                                           
                                                                                  
           
                     
                                                               
                  
                                                               
                  
                 
                                                  
                                                  
                        
                  
                                            
                                               
                                        
                                        
                                                                  
                                               
                                        
                                        
                                                                  

                                                                             
                          
                                
                                                    
                                               
                                 
                                                        
                                                     
                                                          
           
              
                           
                                                                       
                 
                                                            
                                                                             
                            
                                              
                
                     
                                            
                                           
                                                
                                          
                                      
                              
                
                                                        
                                                                                  
                                              
                                                           

                     
                                                                      

                                                                        
                                                                               
                                                                       
                                                                      
           
  
                                                        
                                                    
                                                              
                                       
                                           
                                                                
                       
                                              
                                   
                                                            
                                                                        
                                              
                                                              
                            
                                                                
                   
                                           
                                                   
                                                        
                                                       
             
                                                                                
            
                                                                         
              
                                                                        
                    
                                                                         
                                   
                                                          
                                                 
                                                                    
                                  
                                                          
            
                                                                                
                                                                   
                 
                                         
                                         
      
                                                                
                   
                                                     
                                                          
                                                    
                                                            
                         
                                        
                                            

                                    

                                                            

                                                                             
                                                                        
                                                                           
                                                                            
                                                                

                                                                              
                                                                    
  
                                         
                                                                        
                
                                                              
                                           
                                  
                                                      
                                                                    
                                           
                                  
                                                      
                                                                    
                                                   
                                          
                             
                                                         
                                           
                                                                  
                                                 
                                                        
                                                      
                                                      
                               
                                            
                                     
                                                        
                                                            
                                                                  
                                                                    
                                                                   
                                                                      
                                           
                                    
                                                  
                                                            
                                                          
                                                            
                                                          
                                                  
                                  
                     
                                          
                 
              
              


                                                                

                                                                       
                   
                                                                 
                                       
                                                            
                               
                                 
                                

                                                                

                                                                     
                                                                           
                      
                                                                  
                               
                                                    
       
                          
                               

                                             

                                                                               
                                                                            
                                                                              
                                                                               
                                                                     
                                                                            
                                                                    
                                    


                     
                                                                                

                                                                            
                                                                            
                                                                                
                                                                            
                                                                                
               
                                                            
                                                                         
                                         
                                                                    
                              
                 
                                                                       
                            
                                                                      
               
                                                           
                                         
                                                                  
                       
                                                          
                  
                                       
                                           
                                                                                  
                                                              
                                                  
                                           
                                                                                  
                                                                     
                                                                          
                                                                   
                                         
                                                                     
                                
                               
                                    
                                               
                                                                        
                                                                          
                         
                                                           
                                            
                                                                                
                                                                               
                                                                           
                        

end MoltResearch
