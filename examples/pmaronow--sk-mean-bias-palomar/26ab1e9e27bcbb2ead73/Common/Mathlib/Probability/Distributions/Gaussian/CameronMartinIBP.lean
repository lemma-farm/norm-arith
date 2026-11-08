module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinTilt
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/- Adaptation: declarations are placed in ColeHopfFoundation to avoid duplicate names when imported alongside the independently sourced RSAT library. -/
namespace ColeHopfFoundation
open _root_.MeasureTheory
open _root_.ProbabilityTheory


/-!
# Cameron–Martin IBP scaffold

Measure-level identity: `∫ F(y + cmCoe (t • x)) dμ = ∫ exp((t•x) y - ‖t•x‖²/2) * F(y) dμ`
for `x : cameronMartin μ`. Differentiate at `t = 0` for Gaussian IBP.
-/

open MeasureTheory Filter
open ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.Topology _root_.InnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

/-! ## Tilt = shift for Bochner integrals (real-valued) -/

/-- The shifted integral functional \(t \mapsto \int F(y + \mathrm{cmCoe}(t\cdot x))\,d\mu\). -/
noncomputable def cameronMartinShiftFun (x : cameronMartin μ) (F : E → ℝ) (t : ℝ) : ℝ :=
  ∫ y, F (y + cmCoe (t • x)) ∂μ

                                                                                     
                                                                                      
                                        

                                                                                  
                                                                                       
                                                      

                                                                                           
                                  
                                                                   
                                   
       
                                                                
           
                                                                            
                                             
                                       
                                                                                  
                                                                   
              
                                                                         
                                      
                                                                               
                                                                                           
           
                     
         
                                                                                           
                                                                                
                                                                                   
                                                                                           
                         
        
            
                                                                                                   
         
                                                                                          
               
                                                   
                
                                                                              
                     
                   
                          
                 
      
                                   
                                              
                                                                                                   
           
                   
                                                                                             
                                                                  
                        
                                                                             
                  
                                                                                     
                               
                                     
                               
                        
                                                                              
                                                           
                                             
              
                                                                                  
                                                                                              
                                      
                                                                  
                                

                                                                     
                                                     
                                                                   
                                                                                    
                                                                                    
                                                                       

                                                                                          
                                  
                                                                   
                                                                                                
                                                                                            

end ProbabilityTheory

end ColeHopfFoundation
