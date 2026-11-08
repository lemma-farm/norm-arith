module

public import Sidon.Analysis.VanDerCorput
public import Sidon.Combinatorics.IntervalSize
public import Mathlib.Tactic

@[expose] public section

/-! # Correlation estimates for a Sidon set and its interval model -/

noncomputable section

open scoped ComplexConjugate

namespace Sidon

                                                    
                                                    

def correlationError (N : ℕ) (S : Finset ℤ) (H : ℕ) (f g : ℤ →₀ ℂ) : ℝ :=
  (fejerWeight H).sum
    (fun h w => w * |(S.card : ℝ) ^ 2 / N - (correlation f g h).re|)

                                                             
                                      

theorem correlation_indicatorFinsupp (S T : Finset ℤ) (h : ℤ) :
    correlation (indicatorFinsupp S) (indicatorFinsupp T) h =
      (((S.filter fun x => x + h ∈ T).card : ℕ) : ℂ) := by
  classical
  rw [correlation, Finsupp.sum, support_indicatorFinsupp, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x hx
  simp [indicatorFinsupp_apply, hx]

theorem re_correlation_indicatorFinsupp (S T : Finset ℤ) (h : ℤ) :
    (correlation (indicatorFinsupp S) (indicatorFinsupp T) h).re =
      ((S.filter fun x => x + h ∈ T).card : ℝ) := by
  rw [correlation_indicatorFinsupp]
  simp

                                                                  
                                                                          
                                   
      

theorem re_correlation_indicatorFinsupp_zero (S : Finset ℤ) :
    (correlation (indicatorFinsupp S) (indicatorFinsupp S) 0).re = S.card := by
  rw [re_correlation_indicatorFinsupp]
  simp only [add_zero]
  rw [Finset.filter_eq_self.mpr (fun _ hx => hx)]

                                                                         
                                                                          
                                      
            

theorem re_correlation_indicatorFinsupp_le_one {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) {h : ℤ} (hh : h ≠ 0) :
    (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re ≤ 1 := by
  rw [re_correlation_indicatorFinsupp]
  have hcard : (S.filter fun x => x + h ∈ S).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hyh⟩ := Finset.mem_filter.mp hy
    exact (hS.eq_of_sub_eq_sub hxh hx hyh hy (by omega) (by omega)).2
  exact_mod_cast hcard

                                                              
                                                                             
                  
                                                

                                                                           
                                                                 
                                                                                  
                                                                  
                                    
     

                                                                    
                           
                                                                      
                                                          
                                         
                                                                  
                                                    
                                              
                                                                                    
                                   
                                                                              
                                                          
                
        
                                 

                                                   
                                                                  
                                                                   
                                                                   
                                                              
                                                    
                                      
             
                     
                                                             
              
                                                
                                                  
                                                                                   
                                        
                                               
                                                 
                                                 
              
                                                
                                                  
                                                                                   
                                         
                                                           
                                                 

                                                                             
                                                                 
                         
                                                       
                                 
                                                              

                                                          
                                                                       
                                                                     
                                              
                         
                                   
            
                                  
                                              
                                       
                                                              
                                      
                                                     
      
                                                    
                                                         
                                             
                                                           
                                                     

                                                                    
                                                                  
                               
           
                          
                      
                                                                   
                                        
           
                                                                 
           
             
                                                                            
          
                                                                                  
                         
                                                                            
                          
                                                                      
                                                                   
                                        
           
                                                                 
           
             
                                                                            
          
                                                                                  
                         
                                                                            
                          
                                                                                  
        

                                                                          
                                                                
                              
                                                                          
                                                                             
                                                                      
                         
      

                                                                      
                                  
                                                                                         
                                                      
                                                                  
                                         
                                                            
                                                                              
              
        
                                         

                                                                             
                                  
                                                                    
                                              
                         
                                   
            
                                 
                                                  
                                                  
                                           
                                      
                                                              
      
                                                
                                                       
                                                     

                                                                      
                            
                                      
                                     
                                                                               
                                                                          
                                                                  
                                                          
                                                        
                 
                                               
                                     
                                                                               
                  
                                                                    
                                 

theorem self_correlation_pointwise_error {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) (b : ℝ) (h : ℤ) :
    |b - (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re| ≤
      (1 + |b - 1|) - (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re +
        if h = 0 then 2 * (S.card : ℝ) else 0 := by
  by_cases hh : h = 0
  · subst h
    rw [re_correlation_indicatorFinsupp_zero, if_pos rfl]
    apply abs_le.mpr
    constructor <;> nlinarith [le_abs_self (b - 1), neg_le_abs (b - 1),
      Nat.cast_nonneg (α := ℝ) S.card]
  · rw [if_neg hh, add_zero]
    have hr := re_correlation_indicatorFinsupp_le_one hS hh
    calc
      |b - (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re| =
          |(b - 1) + (1 -
            (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re)| := by
        congr 1
        ring
      _ ≤ |b - 1| + |1 -
          (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr hr)]; ring

theorem self_correlationError_le_mass {N H : ℕ} (hH : 0 < H) {S : Finset ℤ}
    (hS : IsSidonSet (S : Set ℤ)) :
    correlationError N S H (indicatorFinsupp S) (indicatorFinsupp S) ≤
      1 - (fejerWeight H).sum (fun h w =>
        w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) +
      |(S.card : ℝ) ^ 2 / N - 1| + 2 * (S.card : ℝ) / H := by
  let b : ℝ := (S.card : ℝ) ^ 2 / N
  let m : ℝ := S.card
  have hzero : 0 ∈ (fejerWeight H).support := by
    rw [Finsupp.mem_support_iff, fejerWeight_zero H hH]
    positivity
  have hdelta : (fejerWeight H).sum
      (fun h w => w * (if h = 0 then 2 * m else 0)) = 2 * m / H := by
    simp only [mul_ite, mul_zero, Finsupp.sum]
    rw [Finset.sum_ite_eq']
    simp only [hzero, if_true, fejerWeight_zero H hH]
    ring
  calc
    correlationError N S H (indicatorFinsupp S) (indicatorFinsupp S) ≤
        (fejerWeight H).sum (fun h w => w * ((1 + |b - 1|) -
          (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re +
            if h = 0 then 2 * m else 0)) := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_left (self_correlation_pointwise_error hS b h)
        (fejerWeight_nonneg H h)
    _ = (1 + |b - 1|) * (fejerWeight H).sum (fun _ w => w) -
        (fejerWeight H).sum (fun h w =>
          w * (correlation (indicatorFinsupp S) (indicatorFinsupp S) h).re) +
        (fejerWeight H).sum (fun h w => w * (if h = 0 then 2 * m else 0)) := by
      simp only [Finsupp.sum, mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    _ = _ := by rw [sum_fejerWeight H hH, hdelta]; dsimp only [b, m]; ring

                                                                    
                                                                         
                                                                      
                                      
                                                                       
                                                 
                                                             
                                         
                                             
                                         
                                                   
                                
                                                        
              
        
                                                            
                                          
                                                       
                                         
                                              
                                                   
                                                                         
                                                    
                     
          

end Sidon
