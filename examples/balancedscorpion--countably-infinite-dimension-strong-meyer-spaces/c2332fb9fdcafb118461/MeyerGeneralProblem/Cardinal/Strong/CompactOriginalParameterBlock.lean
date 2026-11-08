module

public import MeyerGeneralProblem.Cardinal.Strong.DisjointOriginalParameterSlots
public import Mathlib
@[expose] public section

/-! Actual compact distinct finite parameter blocks, constructed from the coupled family. -/

namespace MeyerGeneralProblem.StrongParity

/-- The finite original parameter data in the accepted strict compact range. -/
structure CompactOriginalParameterBlock (s : ℕ) where
  /-- Every actual real parameter of the finite original block. -/
  parameter : Fin s → ℝ
  /-- Every parameter is strictly between one quarter and one half. -/
  range : ∀ i, parameter i ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)
  /-- Distinct sheet indices have distinct actual parameters. -/
  injective : Function.Injective parameter

                                                                                     
                                                              
                                                           
                                                       
                         
                                     

noncomputable section

                                                                               
                                                                                       
                                                                                    
                                                          
                                                                                                         
                                                                       
                 
               
                                                                             
                 
         

                                                                                             
                                                                        
                                                                   
                                                                                                             
                                                                                                   
                                                                                                  

end

end MeyerGeneralProblem.StrongParity
