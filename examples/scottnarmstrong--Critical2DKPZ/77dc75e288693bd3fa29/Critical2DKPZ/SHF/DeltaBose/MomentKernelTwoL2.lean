/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2
public import Critical2DKPZ.SHF.DeltaBose.Measurability
public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
public import Critical2DKPZ.SHF.DeltaBose.WeightedBlockL2
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Flow.CollisionTimeOrdering
public import Critical2DKPZ.SHF.Flow.CollisionTimeAction
public import Critical2DKPZ.SHF.Flow.WeightedCollisionAction
public import Critical2DKPZ.SHF.Flow.WeightedDiagramBounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # The complete two-particle moment kernel on squared L² -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

open Critical2DKPZ.SHF.Flow

                                                                       
                                                                                     
                                                    
                                         
                                             
           
                                                                   
                              
                                                                   
                                   
                            
      
                                         
                                             
                           
             
                                   
                           
             
                             
                                          
                                                  
                                               
                                   
                           
             
                                                         

                                                                            
                          
                                                             
                                                                                  
                                                                   
                                                    
                             
                                                     
                                
                                            
                                           
                                                                  
                                                                               
              
                      
                                                                         
                       
         
                                                                          
                                                                            










end Critical2DKPZ.DeltaBose

end
