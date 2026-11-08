module
public import Paper.Hyperbolic
public import Mathlib
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Tactic

@[expose] public section

/-!
# Pathwise state equation for a Dirac Parisi measure

For a continuous noise path `W`, subtracting the additive term `β W` from the
post-interface state reduces the equation to an ordinary differential equation.
The bounded globally Lipschitz tanh drift gives existence on the full finite
time interval and pathwise uniqueness, using Picard–Lindelöf.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped NNReal Topology

namespace Paper

/-- The pathwise drift after the additive noise is subtracted. -/
def diracNoiseDrift (β : ℝ) (W : ℝ → ℝ) (t y : ℝ) : ℝ :=
  β ^ 2 * Real.tanh (y + β * W t)

private theorem diracState_continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh x).continuousAt)

/-- The nonlinear drift is globally Lipschitz in the state, with constant `β²`. -/
theorem lipschitzWith_diracNoiseDrift (β : ℝ) (W : ℝ → ℝ) (t : ℝ) :
    LipschitzWith ⟨β ^ 2, sq_nonneg β⟩ (diracNoiseDrift β W t) := by
  have hd (y : ℝ) : HasDerivAt (diracNoiseDrift β W t)
      (β ^ 2 * sech (y + β * W t) ^ 2) y :=
    ((hasDerivAt_tanh (y + β * W t)).comp_add_const y (β * W t)).const_mul (β ^ 2)
  apply lipschitzWith_of_nnnorm_deriv_le (fun y => (hd y).differentiableAt)
  intro y
  rw [(hd y).deriv]
  change ‖β ^ 2 * sech (y + β * W t) ^ 2‖ ≤ β ^ 2
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg β),
    Real.norm_of_nonneg (sq_nonneg (sech (y + β * W t)))]
  exact mul_le_of_le_one_right (sq_nonneg β) (sech_sq_le_one _)

/-- The drift is bounded by `β²`, uniformly in the noise path and state. -/
theorem norm_diracNoiseDrift_le (β : ℝ) (W : ℝ → ℝ) (t y : ℝ) :
    ‖diracNoiseDrift β W t y‖ ≤ β ^ 2 := by
  unfold diracNoiseDrift
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg β), Real.norm_eq_abs]
  exact mul_le_of_le_one_right (sq_nonneg β) (Real.abs_tanh_lt_one _).le

/-- A continuous noise path gives a jointly continuous pathwise drift. -/
theorem continuous_diracNoiseDrift (β : ℝ) (W : ℝ → ℝ) (hW : Continuous W) :
    Continuous (fun p : ℝ × ℝ => diracNoiseDrift β W p.1 p.2) :=
  (diracState_continuous_tanh.comp
    (continuous_snd.add ((hW.comp continuous_fst).const_mul β))).const_mul (β ^ 2)

/-- A pathwise solution of the drift ODE on the post-interface interval. -/
structure IsDiracNoiseSolution (β h q : ℝ) (W Y : ℝ → ℝ) : Prop where
  initial : Y q = h
  hasDerivWithinAt : ∀ t ∈ Icc q (1 : ℝ),
    HasDerivWithinAt Y (diracNoiseDrift β W t (Y t)) (Icc q (1 : ℝ)) t

namespace IsDiracNoiseSolution

variable {β h q : ℝ} {W Y Z : ℝ → ℝ}

/-- Every pathwise ODE solution is continuous on its interval. -/
theorem continuousOn (hY : IsDiracNoiseSolution β h q W Y) :
    ContinuousOn Y (Icc q (1 : ℝ)) :=
  HasDerivWithinAt.continuousOn hY.hasDerivWithinAt

                                                     
                                                               
                                                          
                                                                  
                                            
                        
                                   
                                                                 
                                     
                                                    
                           
                                                                      
                                                           
                                                                      
                                                                          

                                                               
                                                  
                                                                          
                                                                           
                                            
              
                                                                            
                                
              
                                                                            
                                
                               

end IsDiracNoiseSolution

/-- Boundedness of the tanh drift lets the Picard–Lindelöf existence interval
cover all of `[q,1]`, with no small-time restriction. -/
theorem exists_diracNoiseSolution (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) :
    ∃ Y : ℝ → ℝ, IsDiracNoiseSolution β h q W Y := by
  let L : ℝ≥0 := ⟨β ^ 2, sq_nonneg β⟩
  let a : ℝ≥0 := ⟨β ^ 2 * (1 - q), mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hq)⟩
  let t₀ : Icc q (1 : ℝ) := ⟨q, le_rfl, hq⟩
  have hf : IsPicardLindelof (diracNoiseDrift β W) t₀ h a 0 L L := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (lipschitzWith_diracNoiseDrift β W t).lipschitzOnWith
    · intro y _
      exact ((continuous_diracNoiseDrift β W hW).comp
        (continuous_id.prodMk continuous_const)).continuousOn
    · intro t _ y _
      exact norm_diracNoiseDrift_le β W t y
    · dsimp [L, a, t₀]
      simp only [sub_self, sub_zero, max_eq_left (sub_nonneg.mpr hq)]
      rfl
  obtain ⟨Y, hy0, hy⟩ := hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨Y, hy0, hy⟩

                                                                                              
                                                                     
                                              

                                                                                 
                                                    
                                                                   
                                                          
                                                        
                                                                                 
                                                
                                                                
                                   
                      
                                             
             
                     
         
                                              
                                                              
                                                                                 
                                         
              
              
                 
                              
                                 
         
      

                                                                           
def diracNoiseSolution (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) : ℝ → ℝ :=
  Classical.choose (exists_diracNoiseSolution β h q hq W hW)

theorem diracNoiseSolution_spec (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) :
    IsDiracNoiseSolution β h q W (diracNoiseSolution β h q hq W hW) :=
  Classical.choose_spec (exists_diracNoiseSolution β h q hq W hW)

/-- Constant extension of the correction outside `[q,1]`; it is globally continuous. -/
def diracCorrection (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) (t : ℝ) : ℝ :=
  diracNoiseSolution β h q hq W hW (projIcc q 1 hq t)

theorem diracCorrection_eq (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    diracCorrection β h q hq W hW t = diracNoiseSolution β h q hq W hW t := by
  simp only [diracCorrection, projIcc_of_mem hq ht]

theorem continuous_diracCorrection (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) :
    Continuous (diracCorrection β h q hq W hW) :=
  (diracNoiseSolution_spec β h q hq W hW).continuousOn.domRestrict.comp continuous_projIcc

                                                                                 
                                       
                                              
                                                                  

                                                      
                                                                                 
                                            
                                                                
                                                                     
                                  
            
             
         
                                                                
                                                    
                                                    

                                                                                      
                                                               
                                                     
                                          
                                                        

                                                 
                                                  
                                                          
                                                  
                                                 

                                                                             
theorem diracCorrection_spec (β h q : ℝ) (hq : q ≤ 1)
    (W : ℝ → ℝ) (hW : Continuous W) :
    IsDiracNoiseSolution β h q W (diracCorrection β h q hq W hW) := by
  have hy := diracNoiseSolution_spec β h q hq W hW
  refine ⟨?_, ?_⟩
  · rw [diracCorrection_eq β h q hq W hW ⟨le_rfl, hq⟩, hy.initial]
  · intro t ht
    rw [diracCorrection_eq β h q hq W hW ht]
    exact (hy.hasDerivWithinAt t ht).congr_of_mem
      (fun s hs => diracCorrection_eq β h q hq W hW hs) ht

                                                                                   
                                                 
                                                                      
                                              
                                                                    
                                                                    

                                                   
theorem lipschitzWith_tanh : LipschitzWith 1 Real.tanh := by
  have hc : (⟨(1 : ℝ) ^ 2, sq_nonneg (1 : ℝ)⟩ : ℝ≥0) = 1 :=
    Subtype.ext (by norm_num)
  have hl := lipschitzWith_diracNoiseDrift 1 (fun _ => 0) 0
  rw [hc] at hl
  have he : diracNoiseDrift 1 (fun _ => 0) 0 = Real.tanh := by
    funext y
    simp [diracNoiseDrift]
  rwa [he] at hl

/-- The pathwise drift depends Lipschitz-continuously on the noise value. -/
theorem dist_diracNoiseDrift_noise_le (β : ℝ) (W V : ℝ → ℝ) (t y : ℝ) :
    dist (diracNoiseDrift β W t y) (diracNoiseDrift β V t y) ≤
      β ^ 2 * |β| * dist (W t) (V t) := by
  have ht := lipschitzWith_tanh.dist_le_mul (y + β * W t) (y + β * V t)
  norm_num only [NNReal.coe_one, one_mul] at ht
  rw [diracNoiseDrift, diracNoiseDrift, dist_eq_norm, ← mul_sub,
    norm_mul, Real.norm_of_nonneg (sq_nonneg β)]
  calc
    β ^ 2 * ‖Real.tanh (y + β * W t) - Real.tanh (y + β * V t)‖ ≤
        β ^ 2 * dist (y + β * W t) (y + β * V t) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg β)
    _ = β ^ 2 * |β| * dist (W t) (V t) := by
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, Real.norm_eq_abs]
      rw [dist_eq_norm]
      ring

/-- Uniform perturbations of the noise give a quantitative Grönwall bound. -/
theorem IsDiracNoiseSolution.noise_dependence
    {β h q : ℝ} {W V Y Z : ℝ → ℝ}
    (hY : IsDiracNoiseSolution β h q W Y)
    (hZ : IsDiracNoiseSolution β h q V Z) {D : ℝ}
    (hD : ∀ t ∈ Icc q (1 : ℝ), dist (W t) (V t) ≤ D)
    {t : ℝ} (ht : t ∈ Icc q (1 : ℝ)) :
    dist (Y t) (Z t) ≤ gronwallBound 0 (β ^ 2) (β ^ 2 * |β| * D) (t - q) := by
  have hy' : ∀ s ∈ Ico q (1 : ℝ),
      HasDerivWithinAt Y (diracNoiseDrift β W s (Y s)) (Ici s) s :=
    fun s hs => (hY.hasDerivWithinAt s (mem_Icc_of_Ico hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hz' : ∀ s ∈ Ico q (1 : ℝ),
      HasDerivWithinAt Z (diracNoiseDrift β V s (Z s)) (Ici s) s :=
    fun s hs => (hZ.hasDerivWithinAt s (mem_Icc_of_Ico hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hb : ∀ s ∈ Ico q (1 : ℝ),
      dist (diracNoiseDrift β V s (Z s)) (diracNoiseDrift β W s (Z s)) ≤
        β ^ 2 * |β| * D := by
    intro s hs
    rw [dist_comm]
    exact (dist_diracNoiseDrift_noise_le β W V s (Z s)).trans
      (mul_le_mul_of_nonneg_left (hD s (mem_Icc_of_Ico hs)) (by positivity))
  have hi : dist (Y q) (Z q) ≤ (0 : ℝ) := by rw [hY.initial, hZ.initial, dist_self]
  have hout := dist_le_of_approx_trajectories_ODE (εf := (0 : ℝ))
    (εg := β ^ 2 * |β| * D)
    (fun s => lipschitzWith_diracNoiseDrift β W s)
    hY.continuousOn hy' (fun _ _ => by simp) hZ.continuousOn hz' hb hi t ht
  change dist (Y t) (Z t) ≤
    gronwallBound 0 (β ^ 2) (0 + β ^ 2 * |β| * D) (t - q) at hout
  simpa only [zero_add] using hout

                                                                                              
                                   
                                   
                                         
                                                      
                                                            
                                                                
                                                                           
                                                                    
              
                                                                                                                          
              
                                                                                                                               
                                                                     
                               

                                                                     
def diracCorrectionConstant (β q : ℝ) : ℝ :=
  gronwallBound 0 (β ^ 2) (β ^ 2 * |β|) (1 - q)

theorem diracCorrectionConstant_nonneg (β q : ℝ) (hq : q ≤ 1) :
    0 ≤ diracCorrectionConstant β q := by
  have hm := gronwallBound_mono (δ := (0 : ℝ)) (K := β ^ 2)
    (ε := β ^ 2 * |β|) le_rfl (by positivity) (sq_nonneg β)
    (show 0 ≤ 1 - q from sub_nonneg.mpr hq)
  simpa [diracCorrectionConstant, gronwallBound_x0] using hm

private theorem gronwallBound_scale_zero (K ε D x : ℝ) :
    gronwallBound 0 K (ε * D) x = gronwallBound 0 K ε x * D := by
  unfold gronwallBound
  split_ifs <;> simp only [zero_add, zero_mul, div_eq_mul_inv] <;> ring

/-- Extend a compact continuous noise path constantly beyond its endpoints. -/
def compactNoiseExtension (a b : ℝ) (hab : a ≤ b) (w : C(Icc a b, ℝ)) : ℝ → ℝ :=
  fun t => w (projIcc a b hab t)

theorem continuous_compactNoiseExtension (a b : ℝ) (hab : a ≤ b)
    (w : C(Icc a b, ℝ)) : Continuous (compactNoiseExtension a b hab w) :=
  w.continuous.comp continuous_projIcc

/-- The correction as a continuous map on the post-interface time interval. -/
def diracCorrectionPath (β h q : ℝ) (hq : q ≤ 1) (w : C(Icc q (1 : ℝ), ℝ)) :
    C(Icc q (1 : ℝ), ℝ) :=
  ⟨fun t => diracCorrection β h q hq (compactNoiseExtension q 1 hq w)
    (continuous_compactNoiseExtension q 1 hq w) t,
    (continuous_diracCorrection β h q hq (compactNoiseExtension q 1 hq w)
      (continuous_compactNoiseExtension q 1 hq w)).comp continuous_subtype_val⟩

/-- Picard–Lindelöf selection defines a globally Lipschitz map of the noise path. -/
theorem lipschitzWith_diracCorrectionPath (β h q : ℝ) (hq : q ≤ 1) :
    LipschitzWith ⟨diracCorrectionConstant β q, diracCorrectionConstant_nonneg β q hq⟩
      (diracCorrectionPath β h q hq) := by
  apply LipschitzWith.of_dist_le_mul
  intro w v
  apply (ContinuousMap.dist_le (mul_nonneg (diracCorrectionConstant_nonneg β q hq)
    (dist_nonneg : 0 ≤ dist w v))).mpr
  intro t
  have hd : ∀ s ∈ Icc q (1 : ℝ),
      dist (compactNoiseExtension q 1 hq w s) (compactNoiseExtension q 1 hq v s) ≤
        dist w v := fun s _ => ContinuousMap.dist_apply_le_dist (projIcc q 1 hq s)
  have hb := (diracCorrection_spec β h q hq (compactNoiseExtension q 1 hq w)
    (continuous_compactNoiseExtension q 1 hq w)).noise_dependence
    (diracCorrection_spec β h q hq (compactNoiseExtension q 1 hq v)
      (continuous_compactNoiseExtension q 1 hq v)) hd t.property
  rw [gronwallBound_scale_zero] at hb
  have hm := gronwallBound_mono (δ := (0 : ℝ)) (K := β ^ 2)
    (ε := β ^ 2 * |β|) le_rfl (by positivity) (sq_nonneg β)
    (sub_le_sub_right t.property.2 q)
  exact hb.trans (mul_le_mul_of_nonneg_right hm dist_nonneg)

                                                                                         
                                                                 
                                                
                                                                    

                                                    
                                                     
                                 
                                         
                                                               
                                                    
                                      
                                                            
                                         
                                     
                                                           
                                                           
                             
                                                    

                                                                                   
                                                       
                                                      
                                                                           
                                                           
                                                                               
                                                                                        

                                                                                    
                                                                           
                                                     
                                                                          
                                     
                                    
           
                                          
                                                                                           
         
                                                  
                                                  
                                                                              
                                                                              
                                                      
                                                                
                                                                
                                                            
                                                             
                                                                             
                                                  
                           
                                             
                                                          
                                                                               
                                    
                                                                              
                                                                              
                                                                                  
                                                                     
                                                        

                                                              
                                                                        
                                           
                                                               

                                                                                      
                                                                        
                                        
                                                       
                                                          
                                              

                                                              
                                                                
                                                                      
                                         
                                                                                        
            
                      
                                              
                                                       
                                                            
                                               
                                                  
                                                                      
                                                    

                                                                      
                                                                  
                                
                                                                 
                                                            

                                                                         
                                              
                                                            
                                                       
                                                                                      

                                                                  
                                                    
                                    
           
                                         
                                               
         
                                                                                                         

                                                                              
                                                              
                                                              
                                                        

                                                                             
                                                                          
                                                                                    
                                                                  

                                                                                   
                             
                                                                            
                                                   
                                 
                                                                 
                                                  
                                                        
                                                  
                                                                              
                                                                              
                                                    
              
                                                                   
                                                                                  
                                              
                                                                                 
                                              
                                                                             

                                                                               
                                           
                                                     
                                                                        
                                                     
                                                         
                                                               
                                                        
                                                                           
                                                                      
         
                                                             

                                                                                 
structure IsDiracStateSolution (β h q : ℝ) (W X : ℝ → ℝ) : Prop where
  continuous : Continuous X
  before : ∀ t ∈ Icc (0 : ℝ) q, X t = h + β * W t
  after : ∀ t ∈ Icc q (1 : ℝ),
    X t = h + β * W t + ∫ s in q..t, β ^ 2 * Real.tanh (X s)

                                                                                        
                                                            
                                     
                                                                
                                         
                                                       
                                                    

                                                                               
                                                                 
                                            
                                                                   
                                                                              
                                                            
                                                                     
                                            
                                                                    
                      
        
                 
                                                                    
              
                                                          
                                                                                    
                                  
                                                       
                        
                          
           
        

                                                                        
                                 
                                                        
                                                                                 
                                  
                                                                     
            
                      
                                                         
                                               
                    
            

                                                                     
                                                        
                                                       
                                                                     
                                       
                                                                             

                                                                               
                                                              
                                        
                                                       
                                                                                          
         
                                                           
                                
                                                                  
                                        
         
                                                                             
                                 
                                             
                                     
                                                                    
                                    
          

end Paper
