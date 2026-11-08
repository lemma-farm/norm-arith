module
public import GuthMaynard.Improvement.PoissonTails

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace GuthMaynard.Improvement

theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp]

def secondKernelError (ψ : ℝ → ℂ) (S K H τ : ℝ) (Q : Finset ℝ) (z : ℝ × ℝ) : ℂ :=
  ∑ q ∈ Q, ∑ q' ∈ Q, ((q*q':ℝ):ℂ)*phase (τ*(q'*z.2-q*z.1))*
    (((S/K:ℝ):ℂ)*(∑' n : ℤ, poissonRemainder ψ (S/K) (q'*z.2-q*z.1) H n))

theorem second_kernel_error_measurable (ψ : 𝓢(ℝ, ℂ)) (S K H τ : ℝ) (Q : Finset ℝ) :
    Measurable (secondKernelError ψ S K H τ Q) := by
  have hψ : Continuous (𝓕 (ψ:ℝ→ℂ)) := (𝓕 ψ).continuous
  have hm (q q' : ℝ) (n : ℤ) : Measurable (fun z : ℝ × ℝ =>
      poissonRemainder ψ (S/K) (q'*z.2-q*z.1) H n) := by
    unfold poissonRemainder
    apply Measurable.ite
    · exact measurableSet_lt measurable_const (by fun_prop)
    · fun_prop
    · fun_prop
  unfold secondKernelError phase
  fun_prop

/-- Both coefficient sums and the modulus-one oscillatory phase are retained.
The bound is uniform in tau and covers S/K arbitrarily small. -/
theorem second_kernel_error_bound (ψ : 𝓢(ℝ, ℂ)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S K H τ : ℝ) (Q : Finset ℝ),
      0 < S → 0 < K → 0 ≤ H → ∀ z : ℝ × ℝ,
      ‖secondKernelError ψ S K H τ Q z‖ ≤
        (C*(S/K)*(1+K/S)^2/(1+H)^j)*(∑ q ∈ Q, |q|)^2 := by
  obtain ⟨C,hC,h⟩ := second_poisson_remainder_bound ψ j
  refine ⟨C,hC,?_⟩
  intro S K H τ Q hS hK hH z
  unfold secondKernelError
  calc
    _ ≤ ∑ q ∈ Q, ∑ q' ∈ Q, ‖((q*q':ℝ):ℂ)*phase (τ*(q'*z.2-q*z.1))*
      (((S/K:ℝ):ℂ)*(∑' n : ℤ, poissonRemainder ψ (S/K) (q'*z.2-q*z.1) H n))‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun q _ => norm_sum_le _ _))
    _ ≤ ∑ q ∈ Q, ∑ q' ∈ Q, (|q| *|q'|)*(C*(S/K)*(1+K/S)^2/(1+H)^j) := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      intro q' _
      rw [norm_mul, norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (h S K q q' z.1 z.2 H hS hK hH) (by positivity)
    _ = _ := by
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

                                                                   
                                                                                
                                                              
                                                                
                                                    
                             
                                                                                       
                              
                                                                                                
                                                                       
                                                  
                  
                                        
                                                       
                                                       
                                                                                                             
                                           
                                                                               
                           
                                                                                                  
                                                                                                                   
                                                                                
                  
      
                                                                                                                                    
                                                                                          
                                                                           

end GuthMaynard.Improvement
                                                
                                                                    
                                                               
                                                                    
