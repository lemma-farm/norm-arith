module

import all Mathlib

public import MeyerGeneralProblem.Atomic.RieszSynthesis
public import MeyerGeneralProblem.Gram.Whitening
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import all Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

@[expose] public section

/-!
# Coefficient Gram and whitened cross models

The physical and Fourier atomic systems are first synthesized from the same
coefficient Hilbert space. Their raw Gram and cross operators are then
whitened globally. The results below prove that this construction is exact:
whitened synthesis is isometric and its cross operator is precisely the
two-sided whitened raw cross matrix.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped lp

variable {C H : Type*}
  [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

                                                    
                                                  
                  

                                                                 
                                                        
                  

                                       
                                                    
                                           

                                                             
                                                             
                                                              
                                    

                                                                                      
instance coefficientOperator_isScalarTower {ι : Type*} :
    IsScalarTower ℝ (CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
      (CoefficientSpace ι →L[ℂ] CoefficientSpace ι) := by
  constructor
  intro c A B
  change (c • A) * B = c • (A * B)
  exact ContinuousLinearMap.smul_comp c A B

/-- Real scalars commute with composition on coefficient operators. -/
instance coefficientOperator_smulCommClass {ι : Type*} :
    SMulCommClass ℝ (CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
      (CoefficientSpace ι →L[ℂ] CoefficientSpace ι) := by
  constructor
  intro c A B
  change c • (A * B) = A * (c • B)
  exact (ContinuousLinearMap.comp_smul A c B).symm

                                                                        
                                                                       
                                
                                                                       
                                                             
                                                           
                                       
                                                                          
                                                  
                                                              
                  

                                                                       
                                                                          
                                                                   
                                  
                                                         
                                        
                                                                        
                            
                                       

                                          
                              
                                                       
                                                           
                                                                  
                                       
                                                                          
                                                  
                                                              
                                                     

                                                                             
                 
                                                                          
                                                           
                                 
                                                           
                                                                  
                                      

       
                                
                                                       
                                                           
                                                             
                                                         
                                                                        
                       

                                                                            
                                   
                                      
                                                                          
                                                           
                                 
                                              
                                      
         
                               
     

                                                              
                                           
                                                                   
                                                                      
                                                          
                                  
                                                               
                                          
                                                     

                                                        
                              
                                                                 
             
                                    
                                                          
                                                

                                                   
                               
                       
                                                              
                                        
                                           
                                     
                                                            
                        
     

end

end MeyerGeneralProblem
