module

public import GinibrePoincare.Analysis.MatrixSpatialCutoff

@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def matrixSpatialTruncation (n k : ℕ) (F : MatrixRealSpace n → ℝ) : MatrixRealSpace n → ℝ :=
  fun A => matrixSpatialCutoff n k A * F A

theorem matrixSpatialTruncation_contDiff (n k : ℕ) (F : MatrixRealSpace n → ℝ)
    (hF : ContDiff ℝ 1 F) : ContDiff ℝ 1 (matrixSpatialTruncation n k F) :=
  ((matrixSpatialCutoff_smooth n k).of_le (by simp)).mul hF

                                                                               
                                                        
                                             

theorem matrixSpatialTruncation_fderiv (n k : ℕ) (F : MatrixRealSpace n → ℝ)
    (hF : ContDiff ℝ 1 F) (A H : MatrixRealSpace n) :
    fderiv ℝ (matrixSpatialTruncation n k F) A H =
      fderiv ℝ (matrixSpatialCutoff n k) A H * F A +
        matrixSpatialCutoff n k A * fderiv ℝ F A H := by
  have hd := ((matrixSpatialCutoff_smooth n k).differentiable (by simp) A).hasFDerivAt.mul
    (hF.differentiable (by norm_num) A).hasFDerivAt
  unfold matrixSpatialTruncation
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, mul_comm, add_comm, Pi.mul_def] using
      congrArg (fun L : MatrixRealSpace n →L[ℝ] ℝ => L H) hd.fderiv

theorem matrixSpatialTruncation_limits (n : ℕ) (F : MatrixRealSpace n → ℝ)
    (hF : ContDiff ℝ 1 F) (A H : MatrixRealSpace n) :
    Tendsto (fun k => matrixSpatialTruncation n k F A) atTop (nhds (F A)) ∧
      Tendsto (fun k => fderiv ℝ (matrixSpatialTruncation n k F) A H)
        atTop (nhds (fderiv ℝ F A H)) := by
  constructor
  · simpa [matrixSpatialTruncation] using (matrixSpatialCutoff_tendsto n A).mul_const (F A)
  · simp_rw [matrixSpatialTruncation_fderiv n _ F hF A H]
    simpa using ((matrixSpatialCutoff_derivative_tendsto n A H).mul_const (F A)).add
      ((matrixSpatialCutoff_tendsto n A).mul_const (fderiv ℝ F A H))

                                                                                      
                                                                          
                                                                  
                                          
                                                                    
                                                                                                  
                    
           
                   
           
                                                      
                                                         
                                                          
                                                               
                                                               
                                                                                    

                                                  

                                                                
                                                                 
                                                                    
                                                
                                                                                 
                                                       
                                                               
                                           
                                                              
                                                                           
                                                             
                                          
                                                 
                                                                     
                                                                                                     
                                                    
                                                                                         
           
                   
           
                                                      
                                                                 
                                                
                                                           
                                                                
                                                                                 
                       
                                                                 
                                                                                            
                                                               
                                                                          
                                                                        
                                                  
                                                                                    

                                                              

                                                      
                                                              
                                                                        
                                                       
                                                         
                                                                                    
                                                          
           
                                        
                                                                               
                                                                                  
                                                                                                        
                                            
                                                                                        
                                                                                                 
                                                                  
                                                                                     
                                                                               
                            
                                                   
                                               
                                                 
                            
                                                               
              
         
                                      
                                                                             

                                                    

                                                                                
                                                                                        
                                                     
                                                     
                                              
                                        
                                                                         
                                  
                                               
                                                                                        
                                                                
                                                                        
                                                                               
                                                 
                                                              
                                                          
                                              
                                                               
                                                                                           
                                                              
                                                                         
                                                   
                                                                  
                                                     
                                                                                        
                                                                                           
                                             
                                                                        
                                                      
                                           
              

                                      

theorem matrixSpatialTruncation_L2_errors (n : ℕ) (μ : Measure (MatrixRealSpace n))
    (F : MatrixRealSpace n → ℝ) (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ)
    (H : MatrixRealSpace n) (hD : MemLp (fun A => fderiv ℝ F A H) 2 μ) :
    Tendsto (fun k => ∫ A, (matrixSpatialTruncation n k F A - F A) ^ 2 ∂μ)
      atTop (nhds 0) ∧
    Tendsto (fun k => ∫ A,
      (fderiv ℝ (matrixSpatialTruncation n k F) A H - fderiv ℝ F A H) ^ 2 ∂μ)
      atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := matrixSpatialCutoff_derivative_bound n
  have hb (k : ℕ) (A : MatrixRealSpace n) :
      |fderiv ℝ (matrixSpatialCutoff n k) A H| ≤ M * ‖H‖ := by
    refine (hM k A H).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg H))
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  constructor
  · have ht := tendsto_integral_of_dominated_convergence (fun A => F A ^ 2)
      (fun k => (((matrixSpatialTruncation_contDiff n k F hF).continuous.sub hF.continuous).pow 2).aestronglyMeasurable)
      hv.integrable_sq (fun k => ae_of_all _ fun A => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (matrixSpatialCutoff n k A * F A - F A) ^ 2 ≤ F A ^ 2
        obtain ⟨h0, h1⟩ := matrixSpatialCutoff_mem_unit n k A
        have hc : (matrixSpatialCutoff n k A - 1) ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (F A))])
      (ae_of_all _ fun A => by simpa using
        (((matrixSpatialTruncation_limits n F hF A H).1.sub_const (F A)).pow 2))
    simpa using ht
  · have ht := tendsto_integral_of_dominated_convergence
      (fun A => 2 * (M * ‖H‖) ^ 2 * F A ^ 2 + 2 * (fderiv ℝ F A H) ^ 2)
      (fun k => (((((matrixSpatialTruncation_contDiff n k F hF).continuous_fderiv one_ne_zero).clm_apply
        continuous_const).sub ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)).pow 2).aestronglyMeasurable)
      ((hv.integrable_sq.const_mul (2 * (M * ‖H‖) ^ 2)).add (hD.integrable_sq.const_mul 2))
      (fun k => ae_of_all _ fun A => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (fderiv ℝ (matrixSpatialTruncation n k F) A H - fderiv ℝ F A H) ^ 2 ≤ _
        rw [matrixSpatialTruncation_fderiv n k F hF]
        obtain ⟨hc0, hc1⟩ := matrixSpatialCutoff_mem_unit n k A
        have hc2 : (matrixSpatialCutoff n k A - 1) ^ 2 ≤ 1 := by nlinarith
        have hd2 : (fderiv ℝ (matrixSpatialCutoff n k) A H) ^ 2 ≤ (M * ‖H‖) ^ 2 := by
          have hh := hb k A
          nlinarith [sq_abs (fderiv ℝ (matrixSpatialCutoff n k) A H),
            abs_nonneg (fderiv ℝ (matrixSpatialCutoff n k) A H), mul_nonneg hM0 (norm_nonneg H)]
        have hx := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (F A))
        have hy := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (fderiv ℝ F A H))
        nlinarith [sq_nonneg (fderiv ℝ (matrixSpatialCutoff n k) A H * F A -
          (matrixSpatialCutoff n k A - 1) * fderiv ℝ F A H)])
      (ae_of_all _ fun A => by simpa using
        (((matrixSpatialTruncation_limits n F hF A H).2.sub_const (fderiv ℝ F A H)).pow 2))
    simpa using ht

#print axioms matrixSpatialTruncation_L2_errors
end
end GinibrePoincare
