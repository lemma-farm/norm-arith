module

public import Mathlib.Analysis.MeanInequalities

/-! # Normalized finite power means for response comparisons -/

@[expose] public section

open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

/-- The normalized v-mean on a finite set of cells. -/
noncomputable def finitePowerMean {ι : Type*} [Fintype ι] (f : ι → ℝ) (v : ℝ) : ℝ :=
  Real.rpow ((∑ i, Real.rpow (f i) v) / (Fintype.card ι : ℝ)) (1 / v)

                                                      
                                                                           
                        
                                    
                                                                                   

                                                    
                                                            
                                                                          
                        
                         
                                                                                             
                     
                                  
                                                                                             

                                                                  
                                         
                                                
                        
                                                                                
                                                                                 
                                                                                                 

                                                    
                                                                         
                                                                        
                        
                                                                         
                                                          
                                                                                              
                                                                 

theorem finitePowerMean_add_le {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    {v : ℝ} (hv : 1 ≤ v) :
    finitePowerMean (fun i => f i + g i) v ≤ finitePowerMean f v + finitePowerMean g v := by
  have h := Real.Lp_add_le (Finset.univ : Finset ι) f g hv
  simp only [abs_of_nonneg (hf _), abs_of_nonneg (hg _),
    abs_of_nonneg (add_nonneg (hf _) (hg _))] at h
  unfold finitePowerMean
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (add_nonneg (hf i) (hg i)) v)
    (Nat.cast_nonneg _) (1 / v),
    Real.div_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) v)
      (Nat.cast_nonneg _) (1 / v),
    Real.div_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hg i) v)
      (Nat.cast_nonneg _) (1 / v), ← add_div]
  exact div_le_div_of_nonneg_right h (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end CoarseDeGiorgi.SharpnessExamples
