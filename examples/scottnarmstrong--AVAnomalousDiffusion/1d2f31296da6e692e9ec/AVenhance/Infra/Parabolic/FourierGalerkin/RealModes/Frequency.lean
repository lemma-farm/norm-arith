-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.Basis
public import AVenhance.Infra.Parabolic.FourierGalerkin.ODE
public import AVenhance.Infra.Torus.FourierCalculus
public import AVenhance.Statements.Roots.SpaceGrad
public import Mathlib

/-!
# Real sine/cosine modes for symmetric Fourier cutoffs

The integer frequency box is split into the zero frequency and one representative from each pair
`{k, -k}`. Each nonzero representative contributes its real and imaginary character. This module
builds the concrete real-valued modes and their smooth periodic ambient representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory

local instance realModesMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance realModesMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance realModesProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The lexicographically positive half of the nonzero integer pairs. -/
def positiveFrequencyPair (p : ℤ × ℤ) : Prop :=
  0 < p.1 ∨ (p.1 = 0 ∧ 0 < p.2)

/-- One representative from each pair `{p,-p}` in the symmetric frequency box. -/
noncomputable def positiveFrequencyRepresentatives (N : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact (symmetricFrequencyBox N).filter positiveFrequencyPair

                                                                                   
                                                       

                                                     
                                             
          
                                                     

                                                                    
                                                                              
                                
                                                    
                                               

                                                                
                                                   
                                                               
                                                   

                                                                          
                                                              
                                                           
            
                                                                               
                                     
                                                         
                                                    

                                                                                
                                                                       
                                                               
                                                
           
                                                     
                                         
                                                                             

                                                                                                   
                             
            
                
               
                                     
           
            
                
               
                                     
           

                                                                                  
                                      
                      
                                 
                                                                           

                                                                    
                                                   
                                                 
            
                                                                                   
                                                 

                                                    
                                 
                                                           
                                                     
             
            
                             
                      
                                             
                                                                                    
                                                    
                              
                                                                                 
                                         
                                
                                  
                                                         
                                
                              
                             
                                               
                                
                                 
                                                          
                                       
                                            
                                             
                              
                                                 
                                     
                                                         
                                                
                                
                                                                  
                         
             
                                  
                                                       
                                                                                         
                   


end AVenhance.Infra.Parabolic.FourierGalerkin

end
