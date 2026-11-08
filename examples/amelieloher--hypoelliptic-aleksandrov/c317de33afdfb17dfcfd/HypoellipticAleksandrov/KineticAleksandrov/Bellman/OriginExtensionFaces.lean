module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionWeak
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # The literal kinetic inner rectangle and its normal surface weights -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

/-- Reference parametrizations of the two position faces and two velocity faces. -/
def bellmanOriginFace (i : Fin 4) (w : ℝ) : ℝ × ℝ :=
  if i.val < 2 then (if i.val = 0 then -1 else 1, w)
  else (w, if i.val = 2 then -1 else 1)

/-- The reference face never passes through the origin. -/
theorem bellmanOriginFace_ne_zero (i : Fin 4) (w : ℝ) :
    bellmanOriginFace i w ≠ (0, 0) := by
  fin_cases i <;> simp [bellmanOriginFace]

                                                    
                                                                                         
                                                    
                          
                        

                                                                                             
                                                                               
                                              
                                                    
                                                         
                                                        
                                       
                            
                                                      
                                         
                            
                                                      
                                                                                     
                                                               
                                                                               
                                                           
                                                               
                                                                                        
             
                                                                      
                                  
                                                              
                             
                 
            

                                                                               
                                                                     
                                                   
                                                                               
                                                                                         
                                     
                                                     
             
                                                                  
                                                                           

                                                                                         
                                                 
                                               
                                                       
                                           
                                                              
                                           
                                                                                              
                                                                               
                          
                                         
                                                        
                                                      
                                                                                   
                          
                                                                          
                                                                                       

                                                                                       
def bellmanOriginFaceError (k : ℕ) (delta : ℝ) (i : Fin 4)
    (f test : (ℝ × ℝ) → ℝ) : ℝ :=
  delta ^ k * ∫ w in (-1 : ℝ)..1,
    f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
      test (bellmanPlaneDilation delta (bellmanOriginFace i w))

                                                                                         
                                                                                
                            
                                             
                             
                                                          
                                                                   
                                                         
                            
                                                                
                                                                
                                                                        
                                                                              

                                                                                 
                                                                                 
                            
                                             
                                       
                                                      
                                                               
                                                         
                            
                                                            
                                                                  
                                                                         
                                                                     

                                                                                     
theorem bellmanOriginFaceError_bound (beta : ℝ) (f : (ℝ × ℝ) → ℝ)
    (hscale : ∀ r : ℝ, 0 < r → ∀ q ∈ bellmanPuncturedSet,
      f (bellmanPlaneDilation r q) = r ^ beta * f q)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ i : Fin 4, ∀ w ∈ Icc (-1 : ℝ) 1, |f (bellmanOriginFace i w)| ≤ C)
    (test : (ℝ × ℝ) → ℝ) (M : ℝ) (_hM : 0 ≤ M) (hMt : ∀ q, |test q| ≤ M)
    (k : ℕ) (delta : ℝ) (hd : 0 < delta) (i : Fin 4) :
    |bellmanOriginFaceError k delta i f test| ≤ 2 * C * M * delta ^ (beta + k) := by
  have hi : |∫ w in (-1 : ℝ)..1,
      f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
        test (bellmanPlaneDilation delta (bellmanOriginFace i w))| ≤
      (delta ^ beta * C * M) * 2 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := 1) (C := delta ^ beta * C * M)
      (f := fun w => f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
        test (bellmanPlaneDilation delta (bellmanOriginFace i w))) (fun w hw => ?_)
    · simpa only [Real.norm_eq_abs, sub_neg_eq_add, one_add_one_eq_two, abs_of_pos
        (by norm_num : (0 : ℝ) < 2)] using hh
    · have hw' : -1 < w ∧ w ≤ 1 := by simpa using hw
      rw [Real.norm_eq_abs, abs_mul,
        hscale delta hd _ (bellmanOriginFace_ne_zero i w), abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos hd beta)]
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hb i w ⟨hw'.1.le, hw'.2⟩)
          (Real.rpow_nonneg hd.le _)
      · exact hMt _
      · exact abs_nonneg _
      · exact mul_nonneg (Real.rpow_nonneg hd.le _) hC
  unfold bellmanOriginFaceError
  rw [abs_mul, abs_of_nonneg (pow_nonneg hd.le k)]
  calc
    delta ^ k * |∫ w in (-1 : ℝ)..1,
        f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
          test (bellmanPlaneDilation delta (bellmanOriginFace i w))| ≤
        delta ^ k * ((delta ^ beta * C * M) * 2) :=
      mul_le_mul_of_nonneg_left hi (pow_nonneg hd.le k)
    _ = 2 * C * M * delta ^ (beta + k) := by
      rw [Real.rpow_add hd, Real.rpow_natCast]
      ring

end HypoellipticAleksandrov.KineticAleksandrov
