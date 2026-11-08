-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.HMinusTools
public import AVenhance.Infra.Ergodic.HMinusOneErgodicFlow
public import Mathlib

/-! Fourier test density connecting the analytic App C dual tests to the
smooth-test norm. All approximants are actual finite real trig sums. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance
open AVenhance.Infra.Ergodic
namespace AVenhance.Infra.Section5

                                                                                         
                                                                    
                                                   

                                                  
                                                               
                                                     
                                                                    

                                                                                                
                                            
                                                                          
               

local instance avInfraSection5TestDensityIsFiniteMeasure1 : IsFiniteMeasure (volume.restrict unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

/-- The actual real Fourier truncation on the supremum-norm lattice ball. -/
def testFourierCutoff (f : Vec 2 → ℝ) (N : ℕ) : Vec 2 → ℝ := lowProjection f N

theorem testFourierCutoff_analytic (f : Vec 2 → ℝ) (N : ℕ) :
    ContDiff ℝ ⊤ (testFourierCutoff f N) := lowProjection_contDiff N

theorem testFourierCutoff_periodic (f : Vec 2 → ℝ) (N : ℕ) :
    IsZ2Periodic (testFourierCutoff f N) := fun k x => lowProjection_periodic N x k

theorem TestDensity.cutoff_coeff {f : Vec 2 → ℝ} (_hf : Continuous f) (N : ℕ) (k : Fin 2 → ℤ) :
    Infra.Torus.smoothFourierCoeff (fun x => (testFourierCutoff f N x : ℂ)) k =
      if k ∈ frequencyBall N then Infra.Torus.smoothFourierCoeff (fun x => (f x : ℂ)) k else 0 :=
  smoothFourierCoeff_euclideanCutoff N _ (fun k => smoothFourierCoeff_real_neg k) k

                                                                                            
                                                                                           
                                                                                                    
                                                                                                                                              
                                                                                  
                                
                                     
                    

theorem TestDensity.eventually_frequency_mem (k : Fin 2 → ℤ) :
    ∀ᶠ N : ℕ in atTop, k ∈ frequencyBall N := by
  obtain ⟨n, hn⟩ := exists_nat_ge ‖k‖
  filter_upwards [eventually_ge_atTop n] with N hN
  rw [mem_frequencyBall]
  exact hn.trans (by exact_mod_cast hN)

theorem TestDensity.tail_tsum_tendsto {a : (Fin 2 → ℤ) → ℝ} (ha : Summable a)
    (hpos : ∀ k, 0 ≤ a k) :
    Tendsto (fun N => ∑' k, if k ∈ frequencyBall N then 0 else a k) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence ha
    (g := fun _ => (0 : ℝ))
    (f := fun N k => if k ∈ frequencyBall N then 0 else a k)
    (fun k => tendsto_const_nhds.congr' ((TestDensity.eventually_frequency_mem k).mono (fun N hn => by simp [hn])))
    (Eventually.of_forall (fun N k => by split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hpos k), hpos k]))
  simpa using h

                                                                        
                                                                                  
                                                                                          
                                                                                        
                                                                 
                                                                        
                                                        
                                                              
                                                                 
                     
                    
           
                                                                                     
                                                                                                          
                                             
                                                                                                 
               
                                                                          

theorem TestDensity.gradient_coeff_cutoff {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : IsZ2Periodic f) (N : ℕ) (i : Fin 2) (k : Fin 2 → ℤ) :
    Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad (testFourierCutoff f N) x i : ℂ)) k =
      if k ∈ frequencyBall N then Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad f x i : ℂ)) k else 0 := by
  rw [Infra.Torus.smoothFourierCoeff_spaceGrad ((testFourierCutoff_analytic f N).of_le (by simp))
    (testFourierCutoff_periodic f N), Infra.Torus.smoothFourierCoeff_spaceGrad hf hp]
  change (2 * Real.pi * Complex.I * (k i : ℂ)) *
    Infra.Torus.smoothFourierCoeff (fun x => (testFourierCutoff f N x : ℂ)) k = _
  rw [TestDensity.cutoff_coeff hf.continuous]
  split_ifs <;> simp [Infra.Torus.realToComplex, Function.comp_def, Complex.ofRealCLM_apply]

theorem TestDensity.grad_component_cont {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    Continuous (fun x => spaceGrad f x i) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem TestDensity.gradient_energy_parseval {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) :
    HasSum (fun k : Fin 2 → ℤ => ∑ i : Fin 2,
      ‖Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad f x i : ℂ)) k‖ ^ 2)
      (gradNormSq (spaceGrad f)) := by
  have h := Infra.Torus.hasSum_sq_realToComplexGradientFourierCoeff hf
  convert h using 1
  funext k
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  congr 1
  funext x
  exact (Infra.Torus.coordDeriv_realToComplex hf i x).symm

/-- Orthogonal truncation never increases gradient energy. Thus normalized
tests stay normalized without an artificial rescaling. -/
theorem testFourierCutoff_gradient_le {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : IsZ2Periodic f) (N : ℕ) :
    gradNormSq (spaceGrad (testFourierCutoff f N)) ≤ gradNormSq (spaceGrad f) := by
  have h1 := TestDensity.gradient_energy_parseval hf
  have h2 := TestDensity.gradient_energy_parseval ((testFourierCutoff_analytic f N).of_le (by simp))
  rw [← h1.tsum_eq, ← h2.tsum_eq]
  apply Summable.tsum_le_tsum _ h2.summable h1.summable
  intro k
  apply Finset.sum_le_sum
  intro i _
  rw [TestDensity.gradient_coeff_cutoff hf hp]
  split_ifs <;> simp

/-- The Fourier derivative multiplier and Parseval give gradient-error
convergence, not merely convergence of values. -/
theorem testFourierCutoff_gradient_error_tendsto {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hp : IsZ2Periodic f) :
    Tendsto (fun N => gradNormSq (spaceGrad (fun x => f x - testFourierCutoff f N x))) atTop (𝓝 0) := by
  let a := fun k => ∑ i : Fin 2,
    ‖Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad f x i : ℂ)) k‖ ^ 2
  have hsum := TestDensity.gradient_energy_parseval hf
  have heq (N : ℕ) : gradNormSq (spaceGrad (fun x => f x - testFourierCutoff f N x)) =
      ∑' k, if k ∈ frequencyBall N then 0 else a k := by
    have hc := (testFourierCutoff_analytic f N).of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤)
    rw [← (TestDensity.gradient_energy_parseval (hf.sub hc)).tsum_eq]
    apply tsum_congr
    intro k
    have hcoord (i : Fin 2) :
        Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad (fun x => f x - testFourierCutoff f N x) x i : ℂ)) k =
        if k ∈ frequencyBall N then 0 else Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad f x i : ℂ)) k := by
      have he : (fun x => (spaceGrad (fun x => f x - testFourierCutoff f N x) x i : ℂ)) =
          fun x => (spaceGrad f x i : ℂ) - (spaceGrad (testFourierCutoff f N) x i : ℂ) := by
        funext x
        simp [spaceGrad, fderiv_fun_sub ((hf.differentiable (by norm_num)).differentiableAt) ((hc.differentiable (by norm_num)).differentiableAt)]
      rw [he, smoothFourierCoeff_sub (f := fun x => (spaceGrad f x i : ℂ)) (g := fun x => (spaceGrad (testFourierCutoff f N) x i : ℂ)) (Complex.continuous_ofReal.comp (TestDensity.grad_component_cont hf i))
        (Complex.continuous_ofReal.comp (TestDensity.grad_component_cont hc i)), TestDensity.gradient_coeff_cutoff hf hp]
      split_ifs <;> simp
    simp_rw [hcoord]
    split_ifs <;> simp [a]
  simp_rw [heq]
  exact TestDensity.tail_tsum_tendsto hsum.summable (fun k => Finset.sum_nonneg (fun i _ => sq_nonneg _))

                                                                    
                                                                         
                                            
                                                
                                                                                       
                                                    
                                                                                                                                 

                                                                              
                                                                            
                                                                           
                                                         
                                                                                
                               
                                                                                                             
                  

                                           
                                                                                   
                         
                                                                                        
                                                                                           
                                                                
                                                                               
                                               
                                                                           
                                                                               
                                                                                               
                                                                                                      

                                                                             
                                                           
                                                     
                                                                           
                                            
                                                                                             
                                                      
                                                                                      
                                                        
                                                                                                        
                                                                
                                                                                                                                             
                                                                                                           
                                           
                                            
                                                                       
                                                                                                   
                                                                                                                                             
                                                                                                
                                                                                                    
                       
                                                                                                   
        
               
                                           

                                                                         
                                            
                                                    
                                                                            
                                                 
                                                                                
                                                                                                          
                                                                                                
                                                                     
            
                                 
                                                          

                                                                             
                                                                     
                                                
                                                            
                                                      
                   
                 
           
                              
                                             
                                                                      
                                                   
                                  
               
                                                          
                                                    
                
                                           
                                                                                 
                                            
                                                                                                                 
                                                                                                                                              
                                               
                                                                             
              
                                                                                    
                                                                              
                                                                                      
                                                                              
                            
                                                                                   
                                                   
                                                           
                                                      
                      
                            
                              
           
                                                                                         
                                 
                                                                      
                                                                              
                               
                                                        
                                           

                                                                    
                                                         
                                                                               
                                               
                                                                                         
                                                                                       
                                                                
                                                  
                                                                          
         

                                                                                      
                        
                                                         
                                                 
                                                   

                                                                                        
                                                                           
                                                                                
                                              
                                                      
                                                                  
                                                       
                                  
         

end AVenhance.Infra.Section5
