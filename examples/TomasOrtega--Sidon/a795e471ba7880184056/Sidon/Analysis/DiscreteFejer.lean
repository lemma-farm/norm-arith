module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! # The discrete Fejér probability kernel -/

open scoped BigOperators

namespace Sidon

/-- The distribution of the difference of two independent uniform interval points. -/
noncomputable def fejerWeight (H : ℕ) : ℤ →₀ ℝ :=
  ∑ u ∈ Finset.range H, ∑ v ∈ Finset.range H,
    Finsupp.single ((v : ℤ) - u) ((H : ℝ) ^ 2)⁻¹

theorem fejerWeight_apply (H : ℕ) (h : ℤ) :
    fejerWeight H h = ∑ u ∈ Finset.range H, ∑ v ∈ Finset.range H,
      if (v : ℤ) - u = h then ((H : ℝ) ^ 2)⁻¹ else 0 := by
  classical
  simp only [fejerWeight, Finset.sum_apply', Finsupp.single_apply]

theorem fejerWeight_nonneg (H : ℕ) (h : ℤ) : 0 ≤ fejerWeight H h := by
  rw [fejerWeight_apply]
  exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => by
    split_ifs <;> positivity

theorem sum_fejerWeight_mul (H : ℕ) (F : ℤ → ℝ) :
    (fejerWeight H).sum (fun h w => w * F h) =
      ∑ u ∈ Finset.range H, ∑ v ∈ Finset.range H,
        ((H : ℝ) ^ 2)⁻¹ * F ((v : ℤ) - u) := by
  classical
  unfold fejerWeight
  rw [← Finsupp.sum_finsetSum_index (h := fun h w => w * F h)
    (fun h => zero_mul (F h)) (fun h x y => add_mul x y (F h))]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finsupp.sum_finsetSum_index (h := fun h w => w * F h)
    (fun h => zero_mul (F h)) (fun h x y => add_mul x y (F h))]
  apply Finset.sum_congr rfl
  intro v _
  exact Finsupp.sum_single_index (zero_mul _)

                                                                       
                         
                                              
                                                 
                                               
           
                    
                                                             
                                                                   
                            
           
                                                             
                                                                   
                            
           
                                                

                                                     
                                                 
                                                    
                                                                
                            
           
                            
           
                                                 

theorem sum_fejerWeight (H : ℕ) (hH : 0 < H) :
    (fejerWeight H).sum (fun _ w => w) = 1 := by
  have h : (H : ℝ) ≠ 0 := by positivity
  calc
    (fejerWeight H).sum (fun _ w => w) =
        (fejerWeight H).sum (fun _ w => w * 1) := by simp
    _ = ∑ u ∈ Finset.range H, ∑ v ∈ Finset.range H,
        ((H : ℝ) ^ 2)⁻¹ * 1 := sum_fejerWeight_mul H (fun _ => 1)
    _ = 1 := by
      simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

                                                                                    
           
                                                            
                            
           
                            
           
                                                               
                 

                                               
                                     
           
                        
      
                                                
                                                         
                                                    
                                
                
                                            
                               
                       
                                                                   
                                           
                

theorem fejerWeight_eq_zero_of_le_abs (H : ℕ) (h : ℤ) (hh : (H : ℤ) ≤ |h|) :
    fejerWeight H h = 0 := by
  classical
  rw [fejerWeight_apply]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  rw [if_neg]
  intro heq
  have hu' : (u : ℤ) < H := by exact_mod_cast Finset.mem_range.mp hu
  have hv' : (v : ℤ) < H := by exact_mod_cast Finset.mem_range.mp hv
  have hbound : |(v : ℤ) - u| < (H : ℤ) := abs_lt.mpr ⟨by omega, by omega⟩
  rw [heq] at hbound
  exact (not_lt_of_ge hh) hbound

theorem abs_lt_of_mem_support_fejerWeight (H : ℕ) {h : ℤ}
    (hh : h ∈ (fejerWeight H).support) : |h| < (H : ℤ) := by
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hh)
    (fejerWeight_eq_zero_of_le_abs H h (le_of_not_gt hn))

theorem sum_fejerWeight_mul_le (H : ℕ) (hH : 0 < H) (F : ℤ → ℝ) (B : ℝ)
    (hF : ∀ h ∈ (fejerWeight H).support, F h ≤ B) :
    (fejerWeight H).sum (fun h w => w * F h) ≤ B := by
  calc
    (fejerWeight H).sum (fun h w => w * F h) ≤
        (fejerWeight H).sum (fun _ w => w * B) := by
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_left (hF h hh) (fejerWeight_nonneg H h)
    _ = (fejerWeight H).sum (fun _ w => w) * B := by
      simp only [Finsupp.sum, Finset.sum_mul]
    _ = B := by rw [sum_fejerWeight H hH, one_mul]

                                                         
                                                            
                                   
            
                                                            

                                                              
                                                                                
                                   
            
                         
                                                            

end Sidon
