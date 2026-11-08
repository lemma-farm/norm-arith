/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
                                                           
import MarkovProcess.Path.KernelIdentification
import MarkovProcess.Path.Polish
import MarkovProcess.Trajectory.DenseRestrictionMarginals
import MarkovProcess.Trajectory.FellerConditional
import MarkovProcess.Trajectory.FellerCountableStoppingRestart
import MarkovProcess.Trajectory.FellerFiniteMarginals
import MarkovProcess.Trajectory.FellerRestrictedRestart
import MarkovProcess.Trajectory.FellerShift
import MarkovProcess.Trajectory.FellerStoppingConditional
import MarkovProcess.Trajectory.FellerStoppingRestart
import MarkovProcess.DenseTime.TwoPointMarginals

/-!
# The continuous-path Markov process of a Feller semigroup

This is the entry point of the library: for a conservative sub-Markov kernel semigroup `P` on a
nonempty, locally compact Polish state space it names the continuous-path process
`continuousProcess P hP`, restates under quotable names the properties proved for that process
elsewhere in the library, and proves that it is the unique Markov kernel into continuous paths
with the finite-dimensional distributions of `P`.

Every statement carries the Kolmogorov regularity hypothesis `P.KolmogorovRegular hP`, which is
what gives the dense-time trajectory of `P` a continuous modification.  The shift and restart
statements carry in addition the Feller hypothesis `P.IsFellerKernelSemigroup`; the uniqueness
statements carry neither Feller continuity nor local compactness.

Nothing here asserts a Hunt-process property, and no statement covers a stopping time that can be
infinite.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

section FinsetEvaluation

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

                                                                                          
                                          
                                                                                   
                                             

end ContinuousPath

end FinsetEvaluation

namespace Kernel

noncomputable section DenseFiniteEvaluation

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [MeasurableSpace beta]

                                                                                             
                                                                  
                                         
                                                                         
                                                                
                                                 
                                                               
                                                     
                                                                               
                                                              
                          
           
                                                                                   
                                                                             
                                                                           
                                                               
               
                                                                    
                                                                              
                                           
                                                                                           

section Identification

variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

                                                                                             
                                                     
                                          
                                                                           
                                
                                                
                                                              
                                                
                                                               
                     
                                                                    
                                      
         
                                                                                              

end Identification

end DenseFiniteEvaluation

end Kernel

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

                                                                                                
                                                                                                
                                   

                                                                                       
                                                                               
                               
                                  
                                               
                                                       
                                                             
                                     

                                                                                            
                                                                                                 
                                                                                          
                                                   
def IsConservative.continuousProcess : Kernel alpha (ContinuousPath alpha) :=
  continuousPathTrajectory P hP (ContinuousMap.const NNReal (Classical.arbitrary alpha))

/-- The continuous-path process of a conservative semigroup is a Markov kernel: it assigns total
mass one to path space from every starting point. -/
instance isMarkovKernel_continuousProcess : IsMarkovKernel (continuousProcess P hP) := by
  unfold IsConservative.continuousProcess
  infer_instance

                                                                                            
                            
                                                                    
                                                                    
                                                                     
                                               

                                                                                              
                              
                                                 
                                                   
                                                                                       
                                           
                                               

                                                                                                
                                                                         
                                                                                      
                                                                        
                                                                                
                                                                                      
                                                                   
                     
            
              

                                                                                                  
                                           
                                                                       
                                                          
                                
                                                                    
                                                   
                                                             

                                                                                               
                                                                                   
                                                                          
                                                          
                                                                                   
                                                                                               
                                                                        

                                                                              
             
                                                                                           
                                                                                              
                                                                                          
                                      
                                                                   
                                             
                                                                                        
                            
                          
                                                                 
                                         
                         
                                                                                  
                          
           
                                                                                   
                       
                                                                                            
                                                                              
         
                    

variable [LocallyCompactSpace alpha]

                                                                                                 
                                                               
                                                                      
                                                                                             
                                                                                             
                                                                

                                                                                             
                                                                                             
                                             
                                                           
                                                                                      
                                                                                                  
                                                        

                                                                                                 
                                                                                        
                                                                    
                                                                       
                                                             
                                                                                   
                                                                            
                                           
                                                               
                                                            
                                                    
                                                                        

                                                                                              
                                                                                           
                                               
                                                                                 
                                                                       
                                                   
                                                                              
                                               
                                                                                 
                                                 
                                                            
                                                                         
                                                                     
                                                    
                                                                                        

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

                                                                                               
                                                                                              
                                                                                  
                                                               
                                                                       
                                                                                       
                                        
                                                                              
                                                                  
                                 
                                                                     
                                                                         

                                                                                               
                                                                                                 
                                                                                                  
                 
                                                                            
                                                                       
                                                   
                                                                              
                                               
                                                              
                                        
                                            
                                                                        
                                 
                                                                             
                                                                                         

                                                                             
                                                                                             
                                                                
                                                                                     
                                                                       
                                                   
                                                                              
                                               
                                       
                                                              
                                        
                                            
                                                                        
                                 
                                                                             
                                                                                               
              

                                   
                                                                                              
                                                                                                 
                                                                                                
                                                                             
                                                                                              
                                 
                                                                        
                                                     
                                 
                                                       
                                                                                  

                                   
                                                                                                  
                                                                                               
                                                           
                                                                   
                                                                                              
                              
                                                                        
                                 
                                                                                         
                               

                                   
                                                                                                
                                                                                                
                                                                                   
                                                           
                                                                                               
                                                                  
                             
                                                                          
                                                          
                                 
                                                                                  
                      
                              
                                                                                             

                                                                                                
                                                                                               
                                                                                               
                                                                                                 
                                   

                                                                                                
                                                                                             
                                                                                             

                                                                                                  
                                                                                        
                                                              
                                                                         
                                                                  
                          
                                                                             
                                 
                                                                                
                      
                              
                                                                                   


                                   
                                                                                          
                                                                     
                                                                     
                                                                    

             
                                                                                         
                                                                                       
                                                                                              
                                                                                            
                                                                                               
                                                                               
                                                                
                                                                                      
                                                             
                                           
                                                                  
                          
                                                                          
                                                                                                   

end


end SubMarkovKernelSemigroup

end MarkovProcess
