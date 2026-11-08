/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorBridge
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Iterated directional derivatives along a list of directions

`lineIter [d₁, …, dₙ] f = D_{d₁} ⋯ D_{dₙ} f`, where `D_d f = x ↦ f'(x) d` (`dirDeriv`).  For smooth
`f` this agrees with `iteratedFDeriv ℝ n f w (fun i => L.get i)`, and it interacts simply with
composition by continuous linear maps, sign changes and scalar rescalings of the directions.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace RegularityStructures

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

                                                    
                                       
              
                                          

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

       
                                                           

       
                                                        
                                                          

                                                                                 
                                  
                                                               

                                                                          
                                     
                  
                   
                                                           

                                                                                        
                                          
                  
                   
                                                              

                                                    
                                                         
                  
              
                            

                                                                                     
                                                   
          
                                                                                  
                                           
                                                
     

                                                                               
                                                                                          
                                                       
                  
              
                  
                                                
                                                        

                                                                               
                                               
          
                                     
                                                          
      

                                                       
                                               
          
                 

                                                                                    
                                               
                  
              
                  
                                 
                                                          

                                                                                                  
                                                                                               
                  
                                                                                       
                  
               
                  
                                                                
                                                                                             

                                                       
                                                                         
                                                                           
                                                                
                                                         

                                                                                       
                                                                                    
                  
                                                     
                  
            
                                                                   
                                                       
                                                    
                                                                                         
                                                                                  

end RegularityStructures

end
