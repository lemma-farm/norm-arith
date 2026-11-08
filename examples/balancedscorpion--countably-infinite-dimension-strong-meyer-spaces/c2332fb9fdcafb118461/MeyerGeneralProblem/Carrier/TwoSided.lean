module

public import MeyerGeneralProblem.Basic
public import Mathlib
import all Mathlib.Order.Filter.AtTopBot.CountablyGenerated

@[expose] public section

/-!
# Enumerated two-sided carriers

The primary carrier interface records an increasing enumeration by `ℤ` together
with escape to both ends of the real line. This avoids making a noncanonical
enumeration choice inside every analytic construction.
-/

namespace MeyerGeneralProblem

open Filter

/-- A locally finite two-sided carrier with its increasing enumeration fixed. -/
structure TwoSidedCarrier where
  /-- The increasing enumeration. -/
  point : ℤ → ℝ
  /-- Carrier nodes do not repeat and respect the index order. -/
  strictMono : StrictMono point
  /-- The positive-index tail escapes to `+∞`. -/
  tendsto_atTop : Tendsto point atTop atTop
  /-- The negative-index tail escapes to `-∞`. -/
  tendsto_atBot : Tendsto point atBot atBot

namespace TwoSidedCarrier

variable (Λ : TwoSidedCarrier)

instance : FunLike TwoSidedCarrier ℤ ℝ where
  coe := TwoSidedCarrier.point
  coe_injective := by
    intro Λ Γ h
    cases Λ
    cases Γ
    simp_all

       
                                                  

                                                             
                  

                                                             
                           

                                                                
                                     

                                                                                    
                                                                   
                                                    

                                                                                   
                                                                   
                                                    

                                                                                 
                                         
                                            
                                                                                  
                                                                                  
                                     
            
                                                    
             
                  
                                           
                            
            
                  
                                           
                             
            

                                                                         
                                            
                                              
                                             
                                 
                         
                    

end TwoSidedCarrier

end MeyerGeneralProblem
