/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/

public import StochasticCalculus.ItoConstruction
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

/-!
# The natural Itô integral as an L²-valued process

This file gives the quotient/a.e. layer of the time-indexed integral.  A
predictable process is cut off on `(0,t]` inside predictable product `L²`, and
the existing terminal-value Itô isometry is applied to that cutoff.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace StochasticCalculus

variable {W : Type*}  
   [MeasurableSpace W] 
  
  {P : Measure W} [IsProbabilityMeasure P]
  {B : ℝ≥0 → W → ℝ}

/-- The product-space time frame `(0,t] × Ω`. -/
@[expose] def predictableTimeFrame (t : ℝ≥0) : Set (ℝ≥0 × W) :=
  Set.Ioc 0 t ×ˢ Set.univ

omit    
     [IsProbabilityMeasure P]  in
/-- The initial time frame is measurable for the predictable sigma-algebra. -/
theorem measurableSet_predictableTimeFrame
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) :
    MeasurableSet[𝓕.predictable] (predictableTimeFrame (W := W) t) := by
  exact measurableSet_predictable_Ioc_prod 0 t MeasurableSet.univ

        
                                 
                                                                                     
                                         
                                                      
                                                                   
                                          
                                                 
                                          
                                                             
                                                     
                                            
                                                 
                                                                      
                
                                               
                                                              
                                 
                                                 
                                     
                                               
                                                  
                                                    
                                          
                                           
                                               

        
                                 
                                                  
                                     
                                                      
                                    
                                                     
                                        
                                                                         
                                          
                                                 
                                          
                                                             
                                                     
                                            
                                                 
                                                                         
                                                        
                                     
                             

        
                                 
                                                                 
                                       
                                                      
                                    
                                               
                                                              
                           
                               
                                                                        
      
                                                           
                                             
                                                            
                                                                     
                                                            
                                   
                                              
                                                                        

        
                                 
                                                      
       
                                    
                                            
                                    
                                           
                   
              
                                                      
                                                                          
         
                                                                                     
                  

        
                                 
                                                                          
                                        
                                                                      
                                    
                                                                 
                                         
                   
              
                                                   
                                      
                                        
                                                            
           
                                                    
                                                        
                                                          
                                           
                                                         
                                                                      

        
                                 
                                                                           
                                    
                                     
                                                                      
                                    
                                                                 
                                         
                   
              
                                                   
                                      
                                                     
         
                                                    
                                 
                                                        
              
                                                  
                                                                     

        
                                 
                                                                           
                                   
                                                        
                                    
                                                                 
                                                 
                                    
                        
                                                  
                         
                                               

        
                                 
                                             
                                   
                                                      
                                      
                                         
                                                                         
                   
              
                                                            
                                        
                                        
                                                             
                                                                  
                                                        
                                
                                                                   
                      
                                                          
                                                                             
                      
                   
                          
                                                   
                                
                                                                                 
                        
                                                       
                                                       
                    
                                                       
       
                                           
                                                                       

        
                                 
                                                           
       
                                            
                                                        
                                                    
                                                          

        
                                 
                                               
                                   
                                                      
                                    
                                                                           
                                                 

        
                                 
                                               
                                   
                                                      
                                      
                                         
                                                                         
                                                    
                                                

        
                                 
                                                                 
                                    
                                                              
                                    
                                         
                                             
                   
              
                                                            
                                        
                                          
                                                                      
                              
                                                                   
                      
                                                             
                                       
                    
                                                    
                                                                         
                                                         
                                                   
                                     
                                    
                                                         
                                    
                                   
                                                                  
                                                 

        
                                 
                                                                     
                                                      
                                                        
                                                              
                        
                                          
                                                 
                                                     
                                                                  

        
                                 
       
                                        
                                                      
                                    
                                                                       
     

                                                                                
                                             
                                                                      
                                            
                                         
                                                            
                                                                

        
                                 
                                                   
       
                              
                                                                      
                                            
                                         
                                    
                                               
                          

        
                                 
                                                                         
                                                           
                                                 
                                                                      
                                            
                                         
                                                
                                                                     
                                                     
                          
                                  

                                                         
                                                
                                                        
                                                                
                                                               

        
                                 
                                                                                    
                                                   
                                                          
                                                              
                                                                 

        
                                 
       
                                     
                                                        
                                    
                                                                     
     

        
                                 
                                                                                             
                                                              
                                                                      
                                            
                                                                
                                             
                                                 
                   
              
                              
                                                                    
                        
                                                                    
                         
                                                                      
                                                                      
                                        
                                                 
                                          
                               
                                                                         
                        
                                                                    
                                                              
                                            
                                                          
                                         
                                                    
                                 
                                                      
                                             
                                                   
                
                                    
                                                  
                          
                                                    
                              
                    
                                                              
                                   
                                             
                   
                  
                                                      
                  
                                                       
                                         
                                       
                                                       
           
                                                             
                                                        
              
               
                                              
                                                 
              
               
                                                      
                                                   
                                                       
                                                                           
                        

        
                                 
                                                                                      
                                                                 
                                                          
                                
                                                                 
                                               
                   
              
                                                   
                                      
                                        
                                              
                          
                                     
                                                        
                                                         
                    
                                                    
                                     
                                                               
                 
                
                                         
                
                                                  
                                     
                                                     
                                                           
                                    
                                           
              
               
                                                            
                                                       
                        

omit    
     [IsProbabilityMeasure P]  in
/-- An elementary predictable process on an empty ordered interval is zero. -/
theorem elementaryPredictable_eq_zero_of_le [SFinite P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {a b : ℝ≥0} (hba : b ≤ a)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryPredictable 𝓕 a b Z = 0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [elementaryPredictable_coeFn 𝓕 a b Z,
    Lp.coeFn_zero ℝ 2 (nonnegativeLebesgueMeasure.prod P)] with p hp hzero
  rw [hp]
  simpa [Set.Ioc_eq_empty_of_le hba] using hzero.symm

omit    
     [IsProbabilityMeasure P]  in
/-- A Brownian elementary integral beginning after `s` is orthogonal to every
`𝓕_s`-measurable square-integrable random variable. -/
theorem inner_elementaryBrownianValue_adapted_eq_zero
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {s a b : ℝ≥0} (hsa : s ≤ a) (hab : a ≤ b)
    (Y : lpMeas ℝ ℝ (𝓕 a) 2 P) (Z : lpMeas ℝ ℝ (𝓕 s) 2 P) :
    inner ℝ (elementaryBrownianValue hB hsm hnat hab Y) (Z : RandomL2 P) = 0 := by
  have hZ : AEStronglyMeasurable[𝓕 a] (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.mono hsa) (lpMeas.aestronglyMeasurable Z)
  have hYZ : AEStronglyMeasurable[𝓕 a]
      (fun w ↦ (Y : W → ℝ) w * (Z : W → ℝ) w) P :=
    (lpMeas.aestronglyMeasurable Y).mul hZ
  have hind := indep_increment_of_natural_adapted hB hsm hnat hab hYZ
  have hDelta : AEStronglyMeasurable (fun w ↦ B b w - B a w) P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two.aestronglyMeasurable
  have hfactor := hind.integral_mul_eq_mul_integral hDelta
    (AEStronglyMeasurable.mono (𝓕.le a) hYZ)
  rw [L2.inner_def]
  calc
    ∫ w, ⟪elementaryBrownianValue hB hsm hnat hab Y w, (Z : RandomL2 P) w⟫_ℝ ∂P =
        ∫ w, (B b w - B a w) *
          ((Y : W → ℝ) w * (Z : W → ℝ) w) ∂P := by
      apply integral_congr_ae
      filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab Y] with w hw
      rw [hw]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = (∫ w, B b w - B a w ∂P) *
        ∫ w, (Y : W → ℝ) w * (Z : W → ℝ) w ∂P := by
      simpa only [Pi.mul_apply] using hfactor
    _ = 0 := by
      rw [integral_sub (hB.integrable_eval b) (hB.integrable_eval a),
        hB.integral_eval, hB.integral_eval, sub_zero, zero_mul]

        
                                 
                                                                                       
                 
                                               
                                                                      
                                      
                                                                                    
                                                                 
                                                         
                   
                              
                              
                                                       
                                                        
                                        
                                        
                                        
                          
                                                                 
                                                                             
                        
                                                          
             
                          
                 
                                                    
                                                     
                                                    
                   
              

        
                                 
                                                                                         
                             
                                                                      
                                            
                                         
                                                
                                                                           
                                                                         
                                                           

                                                                                      
                                                                          
                                           
                                                                      
                                            
                                         
                                                            
                                
           
                                                                             
                                
                            
                                             
                                     
                                            
                                        
                       
                                    
                                             
                                   
                                             
                                                  
                                                    
                                  
                                                                        
                                                  
                                                           
                                     
                                                                        
                            
                                                           
                                               
                                                 
                                                                        
                                     
      
                                                                           
                          
                                
                                                                            
                         
               
                           
                                                           
                                                                         
                                                             

                                                                                          
                                                      
                                              
                                                                      
                                            
                                         
                                              
                             
                                                         
                                                      
                                                                          
                                                   
                                              
                                               
                                 
                                                    
                                
                                         
                                                                       
                          
                                                      
                        
                                             
                                                                    
                                            
                                                
                 
                                                    
                                                          
                                                                              
                                             
                                            
                                                                 
                                                                     
                                 
                                                               
                             
                                                   
                                                              
                                
                                                             
                                  
                                    
                                                                     
                                            
                                               
                                                                             
                  
                              
                                             
                                             
                                                                
                        
                        
                                                                  
                                          
                                                  

                                                                   
                                                   
                                                                      
                                            
                                         
                                              
                           
                                     
                                                           

       
                                   
                                                                      
                                            
                                         
                                              
                                                            
                                          
     

                                                                                           
                                   
                                                                      
                                            
                                         
                                                              
                                                                
                                                   
                                                                          
                   
                                              
                                           
                                     
                                                           
                                                            
              
                                                                       

                                                                                            
                                                           
                                                                      
                                            
                                         
                                                       
                                                             
                                               

                                                                                     
                                                          
                                                                      
                                            
                                         
                                              
                           
                                                          
                                                                                

                                                                                           
                       
                                              
                                                                      
                                            
                                         
                                              
                                                     
                                                        
                                                                   

                                                                        
                                                                           
                                                                  
                                                                      
                                            
                                         
                                                
                                               
                                               
                                                                   
      
                                               
                                                 
                                      
                                                       
                                                         
                                               
                                                                     
                                                    
                                                                      
                                                                    

                                                                                          
                                               
                                                                      
                                            
                                         
                                                              
                                                                  
                                                           
                                             
                                             
                                                                   
                                                                   
                                                   
                                                                
                               
                    
                                                                  
                                                      
                                                 
      
                                                                  
                                                           
                                                               
                                       
                                                                 

                                                                      
                                                  
                                                                      
                                            
                                         
                                    
                                                                        
                                                                               
               
                                                                 

                                                                                              
                                                                                     
                                                     
                                                                      
                                            
                                         
                             
                                      
           
                                                                             
                                                   
                            
                
                                                                   
                                                                        
                               
                                                         

                                            
                              
                                                                      
                                            
                                         
                                              
                                                                               
                                             

                                                                          
                                 
                                                                      
                                            
                                         
                                              
                                                   
                             
                                             

end StochasticCalculus
