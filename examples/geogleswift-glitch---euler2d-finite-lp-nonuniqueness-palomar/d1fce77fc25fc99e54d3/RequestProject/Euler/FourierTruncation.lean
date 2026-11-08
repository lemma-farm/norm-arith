module

                                              
public import RequestProject.Euler.WeakAux
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Finite Fourier projections and quantitative tails on the two-dimensional torus

The measure on the unit quotient torus in this file is normalized Haar measure.
The operators below are actual finite sums of Fourier modes, rather than an
assumed family of compact approximations.  The weighted estimate is the
spectral estimate needed after the distributional div--curl identities have
been transferred from the fundamental square to the quotient torus.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Euler2D

namespace FourierProjection

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 E)

/-- The orthogonal projection retaining precisely a finite set of basis modes. -/
def trunc (s : Finset ι) : E →L[𝕜] E :=
  ∑ i ∈ s, (innerSL 𝕜 (b i)).smulRight (b i)

theorem trunc_apply (s : Finset ι) (x : E) :
    trunc b s x = ∑ i ∈ s, b.repr x i • b i := by
  simp [trunc, HilbertBasis.repr_apply_apply]

                                               
                                                           
                  
                                                              
                                        

                                                
                                                                       
                                              
                                 
                                                                        
                                      
                                                                                  
                       
                                  
                                       

theorem repr_trunc [DecidableEq ι] (s : Finset ι) (x : E) (i : ι) :
    b.repr (trunc b s x) i = if i ∈ s then b.repr x i else 0 := by
  rw [trunc_apply, map_sum]
  simp only [map_smul, HilbertBasis.repr_self, lp.coeFn_sum, lp.coeFn_smul,
    Finset.sum_apply, Pi.smul_apply, lp.single_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem repr_sub_trunc [DecidableEq ι] (s : Finset ι) (x : E) (i : ι) :
    b.repr (x - trunc b s x) i = if i ∈ s then 0 else b.repr x i := by
  rw [map_sub]
  change b.repr x i - b.repr (trunc b s x) i = _
  rw [repr_trunc]
  split_ifs <;> simp

theorem norm_sq_eq_tsum (x : E) :
    ‖x‖ ^ 2 = ∑' i, ‖b.repr x i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    (b.repr x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] using h

/-- Exact Parseval tail identity for finite orthogonal projection. -/
theorem norm_sub_trunc_sq [DecidableEq ι] (s : Finset ι) (x : E) :
    ‖x - trunc b s x‖ ^ 2 =
      ∑' i, if i ∈ s then 0 else ‖b.repr x i‖ ^ 2 := by
  rw [norm_sq_eq_tsum b]
  congr 1
  funext i
  rw [repr_sub_trunc]
  split_ifs <;> simp

/-- A lower frequency bound and a weighted coefficient bound give a uniform
projection error.  A bound on all finite weighted sums suffices, so no
summability assumption on derivatives is hidden in the statement. -/
theorem norm_sub_trunc_le_of_weighted [DecidableEq ι]
    (s : Finset ι) (x : E) (w : ι → ℝ) {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hw : ∀ i, 0 ≤ w i)
    (hout : ∀ i ∉ s, r ^ 2 ≤ w i)
    (hbound : ∀ t : Finset ι, ∑ i ∈ t, w i * ‖b.repr x i‖ ^ 2 ≤ M ^ 2) :
    ‖x - trunc b s x‖ ≤ M / r := by
  have hsq : ‖x - trunc b s x‖ ^ 2 ≤ (M / r) ^ 2 := by
    rw [norm_sub_trunc_sq]
    apply Real.tsum_le_of_sum_le
    · intro i
      change 0 ≤ (if i ∈ s then 0 else ‖b.repr x i‖ ^ 2)
      split_ifs <;> positivity
    · intro t
      have hterm : ∀ i, r ^ 2 * (if i ∈ s then 0 else ‖b.repr x i‖ ^ 2) ≤
          w i * ‖b.repr x i‖ ^ 2 := by
        intro i
        split_ifs with hi
        · simpa using mul_nonneg (hw i) (sq_nonneg ‖b.repr x i‖)
        · exact mul_le_mul_of_nonneg_right (hout i hi) (sq_nonneg _)
      have hsum : r ^ 2 * (∑ i ∈ t, if i ∈ s then 0 else ‖b.repr x i‖ ^ 2) ≤ M ^ 2 := by
        calc
          _ = ∑ i ∈ t, r ^ 2 * (if i ∈ s then 0 else ‖b.repr x i‖ ^ 2) := by rw [Finset.mul_sum]
          _ ≤ ∑ i ∈ t, w i * ‖b.repr x i‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i
          _ ≤ M ^ 2 := hbound t
      rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
      simpa [div_pow, mul_comm] using hsum
  exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hM hr.le)).mp hsq

end FourierProjection

attribute [local instance] instMeasureSpaceUnitAddCircle

/-- Scalar complex `L²` on the normalized two-dimensional quotient torus. -/
abbrev FourierL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))

/-- Fourier frequencies retained in the square `[-N,N]²`. -/
def fourierModes (N : ℕ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem mem_fourierModes (N : ℕ) (k : Fin 2 → ℤ) :
    k ∈ fourierModes N ↔ ∀ i, -(N : ℤ) ≤ k i ∧ k i ≤ N := by
  simp [fourierModes, Fintype.mem_piFinset]

/-- The continuous linear square Fourier truncation. -/
def fourierTrunc (N : ℕ) : FourierL2 →L[ℂ] FourierL2 :=
  FourierProjection.trunc UnitAddTorus.mFourierBasis (fourierModes N)

                                                    
                                            
                                                                        
                                                                                     

                                                      
                                                                         
                                               

                                                                        
                                                          
                                
                                                                                        
                                                                  
                                                                                     

                                                                              
                                 
def frequencySq (k : Fin 2 → ℤ) : ℝ := (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2

theorem frequencySq_nonneg (k : Fin 2 → ℤ) : 0 ≤ frequencySq k := by
  unfold frequencySq
  positivity

theorem frequencySq_ge_of_not_mem (N : ℕ) {k : Fin 2 → ℤ}
    (hk : k ∉ fourierModes N) : (N : ℝ) ^ 2 ≤ frequencySq k := by
  rw [mem_fourierModes, not_forall] at hk
  obtain ⟨i, hi⟩ := hk
  have hi' : (N : ℝ) ^ 2 ≤ (k i : ℝ) ^ 2 := by
    push_neg at hi
    by_cases h : -(N : ℤ) ≤ k i
    · have ht := hi h
      have ht' : (N : ℝ) < (k i : ℝ) := by exact_mod_cast ht
      nlinarith [sq_nonneg ((k i : ℝ) - N)]
    · have ht : k i < -(N : ℤ) := by omega
      have ht' : (k i : ℝ) < -(N : ℝ) := by exact_mod_cast ht
      nlinarith [sq_nonneg ((k i : ℝ) + N)]
  fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one] at hi' <;>
    simp only [frequencySq] <;> nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]

/-- A uniform spectral `H¹` bound gives the `M/N` Fourier tail estimate.
For a divergence-free velocity, the div--curl coefficient identities turn
the vorticity's `L²` bound into precisely the finite-sum hypothesis below. -/
theorem norm_sub_fourierTrunc_le (N : ℕ) (hN : 0 < N) (f : FourierL2)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s : Finset (Fin 2 → ℤ),
      ∑ k ∈ s, frequencySq k * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 ≤ M ^ 2) :
    ‖f - fourierTrunc N f‖ ≤ M / N := by
  apply FourierProjection.norm_sub_trunc_le_of_weighted _ _ f frequencySq
    (by exact_mod_cast hN) hM frequencySq_nonneg
    (fun k hk => frequencySq_ge_of_not_mem N hk)
  simpa only [UnitAddTorus.mFourierBasis_repr] using hbound

                                                                        
                                                                            
                                                           
                                                     
                                                
                                                                              
                          
                                                           
                                        
            
                                                               
                                                                 
                                         
                                                                                         

                                                                        
                                                                 
theorem fourier_div_curl_identity (k : Fin 2 → ℤ) (a b : ℂ) :
    frequencySq k * (‖a‖ ^ 2 + ‖b‖ ^ 2) =
      ‖(k 0 : ℂ) * a + (k 1 : ℂ) * b‖ ^ 2 +
      ‖(k 0 : ℂ) * b - (k 1 : ℂ) * a‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    sub_zero, add_zero, frequencySq]
  ring

/-- The finite weighted velocity sum is bounded by the vorticity `L²` norm
once the Fourier div--curl identities have been established.  The factor
`2π` from a unit-period spatial derivative is included explicitly. -/
theorem fourier_velocity_weighted_bound (u₀ u₁ ω : FourierL2)
    (hdiv : ∀ k, (k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k +
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k = 0)
    (hcurl : ∀ k, (2 * Real.pi : ℂ) * Complex.I *
      ((k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k -
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k) = UnitAddTorus.mFourierCoeff ω k)
    (s : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ s, frequencySq k *
      (‖UnitAddTorus.mFourierCoeff u₀ k‖ ^ 2 +
       ‖UnitAddTorus.mFourierCoeff u₁ k‖ ^ 2) ≤ (‖ω‖ / (2 * Real.pi)) ^ 2 := by
  have hpoint : ∀ k, (2 * Real.pi) ^ 2 * (frequencySq k *
      (‖UnitAddTorus.mFourierCoeff u₀ k‖ ^ 2 +
       ‖UnitAddTorus.mFourierCoeff u₁ k‖ ^ 2)) =
      ‖UnitAddTorus.mFourierCoeff ω k‖ ^ 2 := by
    intro k
    rw [fourier_div_curl_identity, hdiv k, norm_zero, zero_pow (by decide : 2 ≠ 0),
      zero_add, ← hcurl k, norm_mul, norm_mul, mul_pow, mul_pow]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos, mul_pow]
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < 2 * Real.pi))).mpr
  calc
    _ = ∑ k ∈ s, ‖UnitAddTorus.mFourierCoeff ω k‖ ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]; exact hpoint k
    _ ≤ ‖ω‖ ^ 2 := by
      simpa only [← UnitAddTorus.mFourierBasis_repr, HilbertBasis.repr_apply_apply] using
        UnitAddTorus.mFourierBasis.orthonormal.sum_inner_products_le ω (s := s)

/-- Each velocity component has the Fourier tail controlled by the
vorticity, with the correct normalization on the unit torus. -/
theorem fourier_velocity_tail_le (N : ℕ) (hN : 0 < N) (u₀ u₁ ω : FourierL2)
    (hdiv : ∀ k, (k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k +
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k = 0)
    (hcurl : ∀ k, (2 * Real.pi : ℂ) * Complex.I *
      ((k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k -
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k) = UnitAddTorus.mFourierCoeff ω k) :
    ‖u₀ - fourierTrunc N u₀‖ ≤ (‖ω‖ / (2 * Real.pi)) / N ∧
    ‖u₁ - fourierTrunc N u₁‖ ≤ (‖ω‖ / (2 * Real.pi)) / N := by
  have hbound := fourier_velocity_weighted_bound u₀ u₁ ω hdiv hcurl
  constructor
  · apply norm_sub_fourierTrunc_le N hN u₀ (by positivity)
    intro s
    apply le_trans _ (hbound s)
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (sq_nonneg _)) (frequencySq_nonneg k)
  · apply norm_sub_fourierTrunc_le N hN u₁ (by positivity)
    intro s
    apply le_trans _ (hbound s)
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (sq_nonneg _)) (frequencySq_nonneg k)

/-! ## Fourier test functions in the original fundamental-square model -/

                                                              
                                                   
                                                             

                                                        
                                                            
                                         

                                                                    
                                                                       
                                                                    

                                                                                 
                                                     
                                                                
             
                                                             
             
              
                                        
                                         

                                                     
                                                                
             
                                                             
             
              
                                        
                                         

                                                                
                                                      
                                                       
                                                       
                               
      

                                                                
                                                      
                                                      
                                                       
                               
      

                                                                    
                                                                     
                                                                 
                                                       
                                                         
                                                            

                                                                                       
                                                                         
                                                
                                                                       
                                             
                  
                                                                                        
                                                                                                       

                                                                                       
                                                                         
                                                
                                                                       
                                             
                  
                                                                                        
                                                                                                       

                                                  
                                             
                                                                                           
                                                                                
          
                        
      

                                                  
                                             
                                                                                           
                                                                             
          
                        
      

                                                
                                             
                                                                                 
                                                                                
                           
                         
                                                                                        

                                                
                                             
                                                                                 
                                                                               
                           
                         
                                                                                        

                                                                      
                                                                          
                                                                            
                                                    
                                                              
                                                   
                                                   
                                           
                                                               
                                                 
                                                                               
                                                               
                                                 
                                                                               
                       
                                                                               
                                                                       
                                                           
              
            

                                                                         
                                                                            
                                                                  
                                                       
                                       
                                                                 
                                                                                 
                                                   
                                                   
                                                               
                                                 
                                                                               
                                                               
                                                 
                                                                               
                       
                                                                               
                                                                           
                                                          
            
            

                                                                             
                                                                               
                                                                      
                                        

                                                                          
                                                
                               
                                                             
                                                                        
                                    
                                             
                           
               
                                                                                        
                
                                                                                                  
                                                                                    
                                                                                                  
                                                                                    
                                    
                                     
           
                                                     
              
                                                           
                                                           

                                                                            
                                                                     
                                                                    

                                                   
           
                                                                          
                                                                              

                                                                 
                                                                        
                                                
                                                     

                                                             
                                   

                                                                            
                                                                                 
           
                             
                                                                

                                                                         
                        
                                              
                                    

                                       
                                                                          
                                  

                                                         
                                                                               
                            
                

                                                                                  
                                            

                                                                                
                                                                          

                                                                      
                                                       
                                                       
                                                                            
                                                        
                                                                                     
                                                           

end Euler2D

end
