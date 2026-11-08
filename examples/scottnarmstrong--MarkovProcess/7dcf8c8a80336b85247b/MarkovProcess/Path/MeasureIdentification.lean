/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Continuity.DenseTimeContinuousExtension

/-!
# Identifying continuous-path measures from dense-time restrictions

A measure on continuous-path space is determined by its pushforward to the fixed dense time
carrier. This is the measure-level counterpart of continuous-path kernel identification and is a
deterministic property of continuous paths.
-/

open MeasureTheory

namespace MarkovProcess
namespace Measure

noncomputable section

variable {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

                                                                                               
           
                                        
                      
                                                              
                                                     
               
          
                                                                       
                                                                               
                       
                                                          
                                                   
                    
                                                                                        
                                                                                              
                                                                                  

                                                                                                 
                      
                                   
                                                            
                                                                                     
                   
             
           
                                                           
           
                  
                                                               
                                                  

end
end Measure
end MarkovProcess
