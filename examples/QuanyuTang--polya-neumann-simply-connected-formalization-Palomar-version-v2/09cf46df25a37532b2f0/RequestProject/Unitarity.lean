module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Star
                                   

/-!
# Unitarity of solutions of skew-adjoint linear Volterra equations

If `C : ℝ → A` is a bounded strongly measurable coefficient with values in a complete normed
star algebra and `C(s)^* = -C(s)`, then every continuous solution of
`W(θ) = 1 + ∫₀^θ C(s) W(s) ds` on `[0, L]` is unitary.  This is the unitarity part of
Lemma 10.2 of the paper.

The proof goes through the almost-everywhere derivative of the solution, using the
Lebesgue differentiation theorem for Banach-valued functions and the fact that an absolutely
continuous function with vanishing a.e. derivative is constant.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace PolyaNeumann

/-- The interval version of the Lebesgue differentiation theorem for Banach-valued
functions: if `f` is locally integrable then, for almost every `x` and every `c`,
`x ↦ ∫_c^x f` has derivative `f x` at `x`. -/
theorem ae_hasDerivAt_integral_of_locallyIntegrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun x => ∫ t in c..x, f t) (f x) x := by
  have hg (x y : ℝ) : IntervalIntegrable f volume x y :=
    intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have LDT := (IsUnifLocDoublingMeasure.vitaliFamily volume 1).ae_tendsto_average hf
  have {a b : ℝ} : ∫ (t : ℝ) in Ioc a b, f t = ∫ (t : ℝ) in Icc a b, f t :=
    integral_Icc_eq_integral_Ioc (x := a) (y := b) (X := ℝ) |>.symm
  filter_upwards [LDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_left)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : y ≤ x := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_ge, hy, this]
    rw [← neg_smul, ← inv_neg, neg_sub]
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_right)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : x ≤ y := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_le, hy, this]

                                                                                    
                                                            
                                                                           
                                                                            
                                                                        
                                    
                                                     
                                                           
                                        
                                                                      
                                                
                             
                                                                            
                                      
                                                  
                                                                 
                                                           
                                                                           
                 
                                                                          
                             
                                                                               
                                                                        
                                                  
                                                                                        
                                     
                                  
                                                              
                                                             
                                  
                                                                                  
                                                               
                                                                    
                                                                    
                                                                                          
                                       
                             
                              
                                                                    
                                 
                                              
                                                        
            
                                                             
                                                    
                                                                                 
                             
               
      

                                                                                     
                                                                                  
                                                          
                                                               
                                
                                                                 
                                                                                   
           
                    
                                             
                  
                
                              
                                          
                                                              
                                                                        
                                                                                    
                                     
                                                                         
                                                     
                                                                                            
                                                                         
                                                                   
                                                                
                                      
                                                                                        
                 
                  
            
            
                                                                                      
                    
                                                                               
                                    
                                                                   
                              

                                                             
                                                                               
                                                                      
                                                                                         
                                                                                    
                                                           
                                                     
                                     
                                     
                              
                                                                                           
        
           
                             
                                              
                                                    
                                                                                
                                                       
              
                        
                        
                    

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {C : ℝ → A} {M L : ℝ} {W : ℝ → A}

                                                                                 
                                                                                         
                                   
                                                                  
                                                        
                                  
                                                 
                                                 
                                                           
                               
                                                                                    
                                                         
                                                    
                                                   
                                                                                    
                  
                                                      
                                     
                                                                     
                                    
                                                       
                                    
         
                                                       
                                                                                          
                                 

                         
                                                                    
                                                                                       
                                   
                                                                  
                                            
                                                                 
                                                  
                                                                                     
                                                                                          
                                              
                                                                                                    
                                                           
                                                                          
                          
                               
                         
                          
                                            
                                            
                               
                                                                                 

variable [StarRing A] [StarModule ℝ A] [NormedStarGroup A]

                                                            
                                                                                   
                                                                    
                                                                  
                                                                    
                                  
                                                              
                                                  
                                                        
                                                                 
                                                               
                                                    
                                                                 
                                                      
                                                              
                                    
                                                                                            
                                               
                                
                                                                    
                                      
                          
                                          
            
             
                                                                                
                                                                      
                              
                                                  
                                       
                            
                     
                             
                                              
                                                         
                                                          
                                                                                   
                                                   
                                                                    
                                                                        
                                                                      
                                                                       
                                                               
                                        
                    
                                                                                        
                                    
                                                                                  
                        
                                          
                                               
                                                                             
                                                                                              
                 
                                                  
                                       
                            
                        
                     
                                     
                                                                     
                                                                             
                                                                                 
                                                        
                                                                             
               
                                                                                 
                                    
                                                                                                  
                                                                                        
                        
                                                                                            
                    
                                                                            
                                          
                                                              
                                                                          
                                                                       
                                                           
                                                                                            
                                   

end PolyaNeumann

end
