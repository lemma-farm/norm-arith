module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section


/-! # Changing the order of integration on the Volterra time triangle -/

open Set MeasureTheory

namespace Paper

noncomputable def parisiTimeMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

instance : IsFiniteMeasure parisiTimeMeasure := by
  unfold parisiTimeMeasure
  infer_instance

theorem integral_parisiTime_lower_triangle (F : ℝ → ℝ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s, if t < s then F s else 0 ∂parisiTimeMeasure) = ∫ s in t..1, F s := by
  change (∫ s, (Ioi t).indicator F s ∂volume.restrict (Ioc (0 : ℝ) 1)) = _
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    intervalIntegral.integral_of_le ht.2]
  have hs : Ioi t ∩ Ioc (0 : ℝ) 1 = Ioc t 1 := by
    ext s
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, lt_of_le_of_lt ht.1 h.1, h.2⟩
  rw [hs]

                                                              
                              
                                                                                     
                                                                          
                                                                                        
                                                                       
                                                 
         
                                                        
               
                                 
                                                  
         

                                                                           
                                                                        
                                              
                                                                          
                                                   
                                             
                                                       
                                                                  
                                                                
                                                         
                                                      
      
                                                                                        
                             
                                                                  
                                                                             
                                                                                     
                               
               
                             
                                                                  
                                                                                 

end Paper
