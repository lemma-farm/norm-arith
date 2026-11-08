-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Parabolic.FourierGalerkin.RealModes
public import Mathlib
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# The spatial `L²` gradient space for real Fourier cutoffs

This module places the explicitly differentiated real modes in the vector-valued torus `L²`
space and packages their finite synthesis as a continuous linear map. The Euclidean norm on the
two gradient coordinates is the `PiLp 2` norm, matching the gradient energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

local instance gradientSpaceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance gradientSpaceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance gradientSpaceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

                                                               
                                                   

                                                                                      
                                                                       

def GradientSpace.closedCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem GradientSpace.isCompact_closedCell : IsCompact GradientSpace.closedCell := by
  simpa [GradientSpace.closedCell] using (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

                                                                          
                                                                                      
                                                                                  
         
                                                                                         
                                                               
                                            
                             

                                                                                    
                                                                                 
                           
                                                                     
                                      
                                           
                 
                                                                            
                              
                                                                                   
                                            
                                             
                                                             
                                                                                   
                                                                      
                                                           
                                                    
                                                   
                       
                                                                                                    
                                                       
                                                                  
                     
                                                                                
                                                     
                                                                      
                                                        
                                                       
                                            
            
                

                                                                              
                                               
                                                             
                                         
                                                                   

                                                            
                                                  
                                                                    
                                     
                                                                                  
                                 

       
                                            
                                                 
                                
                                                                                 
                                                

end AVenhance.Infra.Parabolic.FourierGalerkin

end
