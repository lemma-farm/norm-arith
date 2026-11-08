/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Trajectory.FiniteMarginals

/-!
# Reindexing finite rational coordinates by physical time

A finite set of dense rational times is canonically equivalent to its image in `NNReal`.  This
file records the induced measurable path reindexing and its compatibility with continuous-path
evaluation.  No probability-law or Markov claim is made.
-/

namespace MarkovProcess

noncomputable section

namespace DenseTime

open SubMarkovKernelSemigroup

                                                                                                   
                                                                           
                   
                                      
                                               
                                  
       
                 
                       
                                                                  
      
             
                           
                                                               
                               
                                
                                        

       
                                                               
                                                                 

end DenseTime

namespace DenseTimePath

open SubMarkovKernelSemigroup

variable {alpha : Type*}

                                                                                           
                                              
                                                          
                                               

       
                                                        
                                                     
                                                                               

variable [MeasurableSpace alpha]

                                                                                
                                                               
                                                             
                        
         
                                                            

                               
                                                                                               
                       
                                                             
                                                             
                         
                                                    
                                                              
          
     

end DenseTimePath
end
end MarkovProcess
