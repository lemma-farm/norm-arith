/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Identifiability.EventKernel
public import Mathlib
public import Mathlib.Tactic.Ring

/-! # Event-checked lineage-size chain for five panmictic samples -/

@[expose] public section

open scoped Matrix
namespace Rhone.Statistics.Identifiability

abbrev PanFiveState := Fin 6

                                             
                                                           

                                                         
                                                                      
                                                                                                  

def panFiveGeneratorInt : Matrix PanFiveState PanFiveState Int :=
  ![![-10,10,0,0,0,0], ![0,-6,3,3,0,0], ![0,0,-3,0,2,1],
    ![0,0,0,-3,1,2], ![0,0,0,0,-1,0], ![0,0,0,0,0,-1]]

                                                      
                                                                                        
                                                                                
                                   
         
                        

                                                   
                                            
                                                                                  
        

noncomputable def panFiveGenerator (rate : ℝ) : Matrix PanFiveState PanFiveState ℝ :=
  fun i j => rate * (panFiveGeneratorInt i j : ℝ)

                                                                       
                                           

                                                                          
                                                                                     
                             
                                                                 
      

                                                                        
                                                                                     
                                           
                                                                 
      

                                                    
                                                                 
                                                       
      

end Rhone.Statistics.Identifiability
