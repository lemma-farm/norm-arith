module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
/- Compatibility adaptation: direct extensional simplification where modern elaboration closes conversion goals automatically. -/
public import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinIBPDeriv
public import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinFernique
public import Common.Mathlib.Probability.Distributions.Gaussian.TiltKernel
public import Mathlib
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/- Adaptation: declarations are placed in ColeHopfFoundation to avoid duplicate names when imported alongside the independently sourced RSAT library. -/
namespace ColeHopfFoundation
open _root_.MeasureTheory
open _root_.ProbabilityTheory


/-!
# Cameron–Martin IBP: analytic layer

Differentiate `t ↦ ∫ F(y) · exp(t⟨x,y⟩ - t²‖x‖²/2) dμ` at `t = 0`. Main:
`cameronMartinTiltKernel_aeEq_tiltKernel`, `hasDerivAt_tiltFun_at0_of_bounded`,
`hasDerivAt_tiltFun_at0_of_integrable_profile`.
-/

open MeasureTheory Filter
open scoped _root_.Topology _root_.Real _root_.ENNReal _root_.NNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

namespace CameronMartinIBPAnalytic

                                                                   
                                                                          
                                                                                       

                                                                                    
                                                   
      
                                                                       
                                                   
                                      

                                                                                  
                                             
                                                                             
                                                         
                                                            
                                                               
             
                                                           
                                                              
                                                                    
                                                                                            
                                       

                                                        
                                                                    
                                                                   
                                                                              
                                                                          
                                          
                                                                                                  
       
                               

                                                
                                                                   
                     
                                      
                                      
                                                                              
                                                      
                                                   
            
                                                                   
                                                                         
                                                                                      

                                                                     
                                                                         
                                                                              
                                                                    
                                                                               
                                                                     
                                                                          
                                                                                     
                                                    

                                                            
                                                                               
                                                                                              
            
                                                 
                                                                                   
                                                             
                                                                                                  
            
        
                                                                                             
                                                                 
                                                
                     

                                                                               
                                                                                     
                                                                 
                                            

                                                                                   
                                                                                   
                                                                        
                                            
                                                                                         
                                                                                  
                                              

                                                           
                                                                          
                                                                               
                                                                                                  
                                                 
                                                                                    
                                                                                            
                                                                            
                                              
                                                                                  
            
                                            
                      

                                                               
                                                                                     
                                                                                                    
            
                                                 
                                                                                   
                                                             
                                                                                                  
         
            
                                                                         
          
                                                                                               
                                                                   
                                                  
        
                                                                                       
                                        
                
                                            
                                                                                            
                                                                                         
                                                        
                     

                                                                                  
                                                                                           
             
                                                                                              
                                                                                                  
             
                                                         
                                                                     
                  
                         

                                                                                         
                                                                              
                                                                     
                                            
                                                                                       
                                                                                                 
                                                                                       
                                                
              
                                                                                    
                                                                             
              
                                   
                                                               
                              

  
                                                                                            
                                                                                               
                               
  

section ShiftFun

variable (F : E → ℝ)

omit [CompleteSpace E] [SecondCountableTopology E] [IsGaussian μ] in
lemma aestronglyMeasurable_shiftFun_integrand (hF_meas : Measurable F) (v : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun y : E => F (y + t • v)) μ :=
  Filter.Eventually.of_forall (fun t =>
    (hF_meas.comp (by fun_prop)).aestronglyMeasurable)

omit [CompleteSpace E] [SecondCountableTopology E] [IsGaussian μ] in
lemma aestronglyMeasurable_shiftFun_integrandDeriv_at0
    {F' : E → E →L[ℝ] ℝ} (hF'cont : Continuous F') (v : E) :
    AEStronglyMeasurable (fun y : E => (F' y) v) μ := by
  exact ((ContinuousLinearMap.measurable_apply v).comp hF'cont.measurable).aestronglyMeasurable

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E] in
lemma hasDerivAt_shiftFun_integrand
    {F' : E → E →L[ℝ] ℝ} (hF' : ∀ y, HasFDerivAt F (F' y) y) (v : E)
    (t : ℝ) (y : E) :
    HasDerivAt (fun s => F (y + s • v)) ((F' (y + t • v)) v) t := by
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v t := by
    simpa [id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add y
  simpa [Function.comp_def] using ((hF' (y + t • v)).comp_hasDerivAt t hline)

omit [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E] [IsGaussian μ] in
lemma norm_shiftFun_integrandDeriv_le_of_norm_fderiv_le
    {F' : E → E →L[ℝ] ℝ} (hfderiv : ∀ y, fderiv ℝ F y = F' y) (v : E)
    (bound : E → ℝ) {δ : ℝ}
    (hbound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(fderiv ℝ F (y + t • v)) v‖ ≤ bound y) :
    ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(F' (y + t • v)) v‖ ≤ bound y := by
  filter_upwards [hbound] with y hy t ht
  simpa [hfderiv (y + t • v)] using hy t ht

end ShiftFun

private lemma hasDerivAt_shiftFun_at0_of_integrable_bound_core
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F)
    {δ : ℝ} (hδ : 0 < δ)
    (hF_int : Integrable F μ)
    (bound : E → ℝ) (hbound_int : Integrable bound μ)
    (hbound : ∀ᵐ y ∂μ,
      ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(fderiv ℝ F (y + t • cmCoe x)) (cmCoe x)‖ ≤ bound y)
    {F' : E → E →L[ℝ] ℝ} (hF'cont : Continuous F') (hF' : ∀ y, HasFDerivAt F (F' y) y)
    (hfderiv : ∀ y, fderiv ℝ F y = F' y) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := by
  let v : E := cmCoe x
  let G : ℝ → E → ℝ := fun t y => F (y + t • v)
  let G' : ℝ → E → ℝ := fun t y => (F' (y + t • v)) v
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := G) (F' := G') (s := Metric.ball (0 : ℝ) δ) (x₀ := (0 : ℝ))
      (bound := bound) (Metric.ball_mem_nhds _ hδ)
      (aestronglyMeasurable_shiftFun_integrand (μ := μ) (F := F) hF_meas v)
      (by simpa [G] using hF_int)
      (by
        simpa [G', zero_smul, add_zero] using
          (aestronglyMeasurable_shiftFun_integrandDeriv_at0 (μ := μ) hF'cont v))
      (norm_shiftFun_integrandDeriv_le_of_norm_fderiv_le (μ := μ) (F := F) hfderiv v bound
        (by simpa [v] using hbound))
      hbound_int
      (ae_of_all _ (fun y t ht => by
        simpa [G, G'] using hasDerivAt_shiftFun_integrand (F := F) hF' v t y))
  have hInt0 : (∫ y, G' 0 y ∂μ) = ∫ y, (fderiv ℝ F y) v ∂μ := by
    refine integral_congr_ae (ae_of_all _ (fun y => by simp [G', v, hfderiv y]))
  simpa [cameronMartinShiftFun, G, v, hInt0] using h.2

/-- Differentiate the Cameron–Martin shift functional at `t = 0` under a local domination
hypothesis. -/
theorem hasDerivAt_shiftFun_at0_of_integrable_bound
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {δ : ℝ} (hδ : 0 < δ)
    (hF_int : Integrable F μ)
    (bound : E → ℝ) (hbound_int : Integrable bound μ)
    (hbound : ∀ᵐ y ∂μ,
        ∀ t ∈ Metric.ball (0 : ℝ) δ, ‖(fderiv ℝ F (y + t • cmCoe x)) (cmCoe x)‖ ≤ bound y) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := by
  classical
  rcases (contDiff_one_iff_hasFDerivAt.mp hF_c1) with ⟨F', hF'cont, hF'⟩
  exact hasDerivAt_shiftFun_at0_of_integrable_bound_core (μ := μ) x F hF_meas hδ hF_int bound
    hbound_int hbound hF'cont hF' (fun y => (hF' y).fderiv)

                                                                                    
                                       
                                                                                       
                                                                                 
                                                              
                                                
                                 
                                                                                       
                                                                                                
                                                      
                                                            
                                                     
                                                                
                                        
                                                                  
                                                      
                                                       
                                                                                            
             
                                                                                         
                                                  

                                                                                            
theorem hasDerivAt_shiftFun_at0_polyGrowth
    (x : cameronMartin μ) (F : E → ℝ) (hF_meas : Measurable F) (hF_c1 : ContDiff ℝ 1 F)
    {C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hF_growth : ∀ y, |F y| ≤ C * (1 + ‖y‖) ^ m)
    (hF'_growth : ∀ y, ‖fderiv ℝ F y‖ ≤ C * (1 + ‖y‖) ^ m) :
    HasDerivAt (fun t => cameronMartinShiftFun (μ := μ) x F t)
      (∫ y, (fderiv ℝ F y) (cmCoe x) ∂μ) 0 := by
  have hbase : Integrable (fun y : E => (1 + ‖y‖) ^ m) μ :=
    ProbabilityTheory.IsGaussian.integrable_one_add_norm_pow (μ := μ) m
  have hF_int : Integrable F μ :=
    (hbase.const_mul C).mono' hF_meas.aestronglyMeasurable <|
      ae_of_all _ (fun y => by simpa [Real.norm_eq_abs] using hF_growth y)
  let v : E := cmCoe x
  let bound : E → ℝ := fun y => (C * ‖v‖ * (1 + ‖v‖) ^ m) * (1 + ‖y‖) ^ m
  have hbound_int : Integrable bound μ :=
    hbase.const_mul (C * ‖v‖ * (1 + ‖v‖) ^ m)
  have hbound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) (1 : ℝ),
      ‖(fderiv ℝ F (y + t • v)) v‖ ≤ bound y := by
    refine ae_of_all _ (fun y t ht => ?_)
    have ht1 : ‖t‖ ≤ (1 : ℝ) := le_of_lt (by simpa [Metric.mem_ball, Real.norm_eq_abs] using ht)
    have hnorm : ‖y + t • v‖ ≤ ‖y‖ + ‖v‖ := by
      have : ‖t • v‖ ≤ ‖v‖ := by simpa [norm_smul] using mul_le_mul_of_nonneg_right ht1 (norm_nonneg
        v)
      have htmp : ‖y‖ + ‖t • v‖ ≤ ‖y‖ + ‖v‖ := by
        simpa [add_comm] using add_le_add_right this ‖y‖
      exact (norm_add_le _ _).trans htmp
    have hle : 1 + ‖y + t • v‖ ≤ (1 + ‖v‖) * (1 + ‖y‖) := by
      have h1 : (1 : ℝ) + ‖y + t • v‖ ≤ (1 : ℝ) + (‖y‖ + ‖v‖) := by
        simpa [add_assoc, add_left_comm, add_comm] using (add_le_add_left hnorm 1)
      have h2 : (1 : ℝ) + (‖y‖ + ‖v‖) ≤ (1 + ‖v‖) * (1 + ‖y‖) := by
        nlinarith [norm_nonneg y, norm_nonneg v]
      exact h1.trans h2
    have hp : (1 + ‖y + t • v‖) ^ m ≤ ((1 + ‖v‖) * (1 + ‖y‖)) ^ m :=
      pow_le_pow_left₀ (by positivity) hle m
    have hOp := (fderiv ℝ F (y + t • v)).le_opNorm v
    have hB : ‖fderiv ℝ F (y + t • v)‖ ≤ C * (1 + ‖y + t • v‖) ^ m := hF'_growth (y + t • v)
    calc
      ‖(fderiv ℝ F (y + t • v)) v‖ ≤ ‖fderiv ℝ F (y + t • v)‖ * ‖v‖ := hOp
      _ ≤ (C * (1 + ‖y + t • v‖) ^ m) * ‖v‖ := by gcongr
      _ ≤ (C * ((1 + ‖v‖) * (1 + ‖y‖)) ^ m) * ‖v‖ := by gcongr
      _ = bound y := by
          simp [bound, mul_pow]
          ring
  simpa using
    hasDerivAt_shiftFun_at0_of_integrable_bound (μ := μ) x F hF_meas hF_c1 (δ := (1 : ℝ))
      (by norm_num) hF_int bound hbound_int hbound

/-
### Tilt functional: helper lemmas
-/

                                 
                                                        
                                                                                   
                                                  
                                                                             
            
                                                                  
                                                  
                                                                   
                                            
                                                               
                                              
                                                               
                                            
                                                            

                                                                 
                                                              
                        
                                    
                                                                                   
                                         
                                                                       
                            
                                  
                                                                                          
                                       
                                                                                                
                                                                           
                                                                         

                                                         
                                               
                                       
                                                         
           
                                                           
                                                           
                                                        
             
                                                                 
                                                                    
                                 
                       
                                                           

                                                                                       
                      
                                                    
                                                              
                        
                                    
                                                                                   
                                                             
                                   
                         
                                                            
                                                                                   
                                                                                               
                                                                   
                                            
                                                                                                 
                                                                                
                                                                    
                                                     
                                     
                                   
                                                                                      
                                      
                                                 
                                                                                   
                                                                   
              
                                     
                                                
                                                              
                                                                            
                                         
                                                                                          
                                                                           
                                              
                                                                           
                   
             
                                                          
                                                                               
                                  
                                         
                                                                                                 
                                         
                       
                                                                                        
                                                                          
               
                                                             
                                                                      
                                                                                              
                                         
                                                                                                   
                                            
                                   
                                                                                       
                                                        
                                                      
                           
                                                                                             
                                     
                       

                                                                                   
                                      
                                                              
                                         
                                                             
                                   
                                                                                        
             
                              
                                                                                                    
                                                                     
                                                                                    
                                                        
                                                               
                                                               
                                                              
                                                                               
                
                                                                                 
                         
               
                                  
                                                                        
                                                            
        
                                                                                           
                                                           
                                                        
                          
                                                   
                                                            
                                       
                                                  
                                                                                                  
          

                                                                                           
                                         
                                                              
                                
                                                
                          
                                                             
                                   
                                                                                      
                                                                 
                                                                 
                                                                  
                
                                                          
                                                                               
                                                                            
                             
                                                               
                                                       
                                                         
                                                          
                           
                                                   
                                                                        
                                                                 
                                                    
                                                              
                                                                      
              
                                                  
                                                               
                                        
                                                                                
                                             
              
                                                                                    
                                                                       
             
                
                     
                                                                                          
                                                               
                                                            
         
        
        
                                                                                 

end CameronMartinIBPAnalytic

open CameronMartinIBPAnalytic
                                                                                      
                                               
                                     
                            
                            
                                      
                                                  
                                                                  
                              
                               
                
                                                                                               
               
                                                                                    
                                                                                       

                                                                                               
                                                  
                                     
                            
                            
                                
                                                
                                                            
                                                                  
                
                                                                        
                                               
               
                                                                       
                                                     
                                                                                       

                                                                                       
                                                           
                                     
                            
                            
                        
                             
                                                     
                      
                                                                                          
                          
                     
                                                                                       
                                                                  
                
                                                                                 
                                                         
               
                                                                                  
                             
                                                                                       

end ProbabilityTheory

end ColeHopfFoundation
