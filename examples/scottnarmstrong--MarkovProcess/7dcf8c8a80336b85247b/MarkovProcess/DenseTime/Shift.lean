/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Path.Shift
import MarkovProcess.Continuity.DenseTimeContinuousExtension

/-!
# Shifts of dense-time paths

This file defines addition by a nonnegative rational time on the fixed dense carrier and the
induced shift of dense-time paths.  Restriction of a continuous path commutes with this shift.
No probability law or Markov property is asserted.
-/

namespace MarkovProcess

noncomputable section

namespace DenseTime

                                                                                      
                                                                 
                                                            
                                                   

       
                                                                                        

                                                                                            
       
                                                  
                                                                                  
                                                                     
           

end DenseTime

namespace DenseTimePath

variable {alpha : Type*}

                                                                    
                                                                           
                                      

       
                                                                  
                                        

       
                                                                         
          
                                   

                                                                
                                                     
          
                                    

variable [MeasurableSpace alpha]

                                                                                                
                                          
                                                                        
                        
         
                                   

end DenseTimePath

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

                                                                                       
                          
                                                                               
                    
                                                        
                                                          
          
                                                                            
                                     

end ContinuousPath
end
end MarkovProcess
