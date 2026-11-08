module

public import FourPapersCommon.ContinuousAdaptedSteps
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! The genuine predictable L² class of a bounded continuous adapted
coefficient, and norm convergence of its actual uniform left step classes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology BigOperators
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
set_option maxHeartbeats 800000

theorem continuousAdaptedLeftStep_norm_le (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) (K : ℝ≥0) (hK : ∀ t ω, ‖H t ω‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) (p : ℝ≥0 × Ω) :
    ‖continuousAdaptedLeftStep 𝓕 H T (n+1) p‖ ≤
      (Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω)).indicator (fun _ => (K:ℝ)) p := by
  classical
  by_cases hp : p.1 ∈ Ioc 0 T
  · have hp' : p.1 ∈ Ioc (uniformPartitionTime T (n+1) 0)
        (uniformPartitionTime T (n+1) (n+1)) := by
      simpa only [uniformPartitionTime, Nat.cast_zero, mul_zero, zero_div,
        mul_div_cancel_right₀ T (by positivity : ((n+1:ℕ):ℝ≥0) ≠ 0)] using hp
    obtain ⟨i, hi, hcell⟩ := exists_partition_cell hp'
    rw [continuousAdaptedLeftStep_of_cell 𝓕 H T hi p hcell,
      indicator_of_mem (show p ∈ Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω) from ⟨hp, mem_univ _⟩)]
    exact hK _ _
  · rw [continuousAdaptedLeftStep_off 𝓕 H T (Nat.zero_lt_succ n) p hp,
      indicator_of_notMem (show p ∉ Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω) from fun h => hp h.1)]
    simp only [norm_zero, le_refl]

theorem continuousAdaptedTimeCut_norm_le (H : ℝ≥0 → Ω → ℝ) (K : ℝ≥0)
    (hK : ∀ t ω, ‖H t ω‖ ≤ K) (T : ℝ≥0) (p : ℝ≥0 × Ω) :
    ‖continuousAdaptedTimeCut H T p‖ ≤
      (Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω)).indicator (fun _ => (K:ℝ)) p := by
  classical
  by_cases hp : p.1 ∈ Ioc 0 T
  · rw [continuousAdaptedTimeCut, if_pos hp,
      indicator_of_mem (show p ∈ Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω) from ⟨hp, mem_univ _⟩)]
    exact hK _ _
  · rw [continuousAdaptedTimeCut, if_neg hp,
      indicator_of_notMem (show p ∉ Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω) from fun h => hp h.1)]
    simp only [norm_zero, le_refl]

theorem finiteMeasure_time_rectangle (T : ℝ≥0) :
    (nonnegativeLebesgueMeasure.prod P) (Ioc (0:ℝ≥0) T ×ˢ (univ:Set Ω)) ≠ ∞ := by
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact nonnegativeLebesgueMeasure_Ioc_ne_top 0 T

                                                                               
                                                
                                                       
                                         
                                                                                    
                                                                             
                                                                                               
                                                                                  
                                                 
                                                            

                                                                                
                                                          
                                                 
                                                                                             
                                                                             
                                                                                               
                                                                                    
                                                 
                                                                 

                                                                                   
                                                
                                                       
                                                                     
                                                              
                                                                                          
                                                                          

                                                                                    
                                                          
                                                                             
                                                            
                                                                                            
                                                                        

theorem norm_sq_toLp_sub {S : Type*} [MeasurableSpace S] {Q : Measure S}
    {f g : S → ℝ} (hf : MemLp f 2 Q) (hg : MemLp g 2 Q) :
    ‖hf.toLp f-hg.toLp g‖^2 = ∫ x, (f x-g x)^2 ∂Q := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with x hs hx hy
  rw [hs, Pi.sub_apply, hx, hy]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

                                                                                      
                                                
                                                       
                                         
                                                                      
                                                                        
           
                                        
                                                                        
                                                                                                      
                                                                         
                                                
                                                                            
                                                                                               
                                                        
                                                                    
                                                                
                                          
                                          
                  
                                                                                                  
                                                                                                        
         
                                             
                           
                                                                     
                                                                     
                                                                
                                           
                                                               
                                                          
                                                                 
                                                                                                
                                                                    
                                                                         
                                                                                   
                             
                                                                   
                                                                     
                                                    
                                       
                                        
                                                                 
                   
                                                            
                                                                 
                                                               
                                                                                     
                                                                            
                                                                            
                                                                                   
                                                                                               
                                                                  

end FourPapersCommon
