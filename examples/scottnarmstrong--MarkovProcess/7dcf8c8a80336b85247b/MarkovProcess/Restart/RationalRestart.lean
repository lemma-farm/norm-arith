/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Restart.RationalRestrictedRestart
import MarkovProcess.Restart.FinitePastRestart
import MarkovProcess.Restart.MixedPastFuture
import Mathlib.Probability.Kernel.Composition.KernelLemmas
                                           
import MarkovProcess.Path.MixedFiniteMarginals

/-!
# The rational-time restart kernel and its joint law

This file merges the following former modules, one section each:

* `RationalJointKernel`: The rational past/future restart kernel
* `RationalRestartFiniteMarginals`: Finite marginals of the rational restart kernel
* `RationalJointLaw`: Rational-time joint restart law
-/

namespace MarkovProcess

section RationalJointKernel

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- The complete rational-past restriction is Borel measurable. -/
theorem measurable_densePastRestriction (S : DenseTime) :
    Measurable (densePastRestriction (alpha := alpha) S) := by
  apply Measurable.of_comap_le
  rw [comap_densePastRestriction_eq_canonicalFiltration]
  exact (canonicalFiltration (alpha := alpha)).le (DenseTime.castOrderEmbedding S)

                                                  
                                                                                              
                                             
       
                                                        
                                                    
                                
                                      
                                                         
                                               
          
                     
       
       

                                                                                                
                                        
def rationalPastFutureRestartKernel
    (Q : Kernel alpha (ContinuousPath alpha)) (S : DenseTime) :
    Kernel alpha ((Set.Iic S → alpha) × ContinuousPath alpha) :=
  Q.map (densePastRestriction S) ⊗ₖ
    Kernel.prodMkLeft alpha
      (Kernel.comap Q (densePastTerminal S) (measurable_densePastTerminal S))

/-- If `Q` is a Markov path kernel, then so is its rational past/future restart kernel. -/
instance instIsMarkovKernelRationalPastFutureRestartKernel
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q] (S : DenseTime) :
    IsMarkovKernel (rationalPastFutureRestartKernel Q S) := by
  unfold rationalPastFutureRestartKernel
  let : IsMarkovKernel (Q.map (densePastRestriction S)) :=
    Kernel.IsMarkovKernel.map Q (measurable_densePastRestriction S)
  infer_instance

                                                                                           
                                                                                             
                                             
                                                                
                                 
                                           
                                             
                                                                                   
          
                                                                
                              
                                                             
                    

end
end ContinuousPath

end RationalJointKernel

section RationalRestartFiniteMarginals

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open scoped NNReal


noncomputable section

namespace MixedPastFuture

                                                                    
                                                                     
                                         
                                                                            

                                                                           
                                                        
                                                                       
                                               

                                                          
                                        
                                                        
                                         
                                        

                                                                 
                                        
                                                          
                                       
                                               

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

                                              
                                                                   
                                          
                                                                    
                        
         
                             

                                                                 
                                          
                                                                  
                        
         
                                                     

                                              
                                                         
                                          
                                                          
                        
         
                             

                                              
                                                                
                                          
                                                                 
                        
         
                             

                                                                      
                                                     
                                          
                                                 
                                                                      
                                                                               
             
     

                                                                      
                                                       
                                          
                                                 
                                                                      
                            
                                                             
                                                        
             
                     
                                                   
                                                    
                                     

end MixedPastFuture

namespace SubMarkovKernelSemigroup.IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

                                            
                                                                
                                    
                                          
                                                 
                                                         
                                                               
                                        
                                                          
                                                
                                                  
                                                        
                                                                                
                                                  
                              
                                                       
                                                                    
                         
                                
                            
             
                                                         
               
                                                      
                                                   
                                                       
                   
         
                                    
                                                                            
                                 
                                                                  
                                                                          
                             
                                                             
                                                  
                                                                           
                                                                
                                                                                          
                 
                                                     
                                                         
               
                                                          
                                                           
                                                 
                                                            
              
                                                          
                                                          
                                                                 

                                          
                                                                
                                    
                                          
                                                 
                                                         
                                                               
                                        
                                                          
                                               
                                                      
                         
                                                                     
                                                           
                                                   
                                                                  
                       
                              
                          
           
                                                       
                                                          
                                                   
                 
       
                                  
                                                                          
                               
                                                                  
                                            
                           
                                                                               
                                                                     
                                                                      
                                                   
                                                       
             
                                                        
                                                                
                                               
                                                          
            
                                                        

                                                          
                                                
                                                           
                                                                
                                                        
                               
                              
                                                            
                                                     
                                                              
                                                     
                                                                 
                                                               
                       
                                                                      
                                                                        
                                                           
                                                  
                           
                                                                               
                           
                                                                
                                                                        
                                                                
                                                                     
                                                              
            
                                                               
                                                   
                                           
                                           
                    
                                                         
                                      
                                                                                     
                                
          
                       
                     
   
                                                                    
                                                                                   
                                                                 
   
                         
               
                                                                           
                                                            
                               
                                                                                 
                                                                       
                                                                                     
                                                                   
                                                                                  
                      
                                                                      
                                                                                     
                                                                     
                                                

                                                                                                
                                                                                      
                                                                          
                                                                
                                    
                                          
                                                 
                                                         
                                                               
                                        
                                                          
                                                   
                                                    
                                                     
                                                                                
                           
                                                                         
                                               
                                                             
                                             
                                                     
                                                                 
                                                
                                                                        
                                                                      
                                                                                 
                                                                               
                                                                 
                                                                      
                                             
                      
                                                                               
                                                                  
                                                                              
                                                       
                                              
                                                       
                                                                 
                                                                 
                                                                     
                                                                                
                              
                                                            
                            
                                        
                                                       
                            
                                        
                                                              
                                                               
                                                                      
                                                                                   
                                                                        
                                                       
                                          
                                               
                     
                      
                                           
                                                         
                                          
                                                              
                      
                                                                                
          
                                                               
                              
                                                                   
                                                                   
                                                                        
               
                                                                               
                        
                                             
                                                           
                                            
                                                                    
                      
                                                       
                                                     
                   
                                                             
           
                                                                    
                                           
                                                   
                                                                  
                                                           
                                                             
                                                                                    
                                                                               
                             
                                                  
                                                               
             
                                                                             
                                 
                                                  
                                                                        
        
                                                              
      
                                                            
                                                                     
                                                               
                                                                              
                                     
                                                                            
                                                                    
                                                                 
                         
                                             
                                                           
                                            
                                                                   
                                                                      
                                     
                                                                   
                                                                   

end SubMarkovKernelSemigroup.IsConservative
end

end RationalRestartFiniteMarginals

section RationalJointLaw

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

                                                                                             
                                   
                                                                    
                                                                
                                    
                                          
                                                 
                                                         
                                                               
                                        
                     
                                                            
                                                     
                                                                         
                                                    
                                                       
                                                                    
         
                              
                       
                                                  
                                                               
                                                         
                                                                             
                                                                         
                    
                                 
                                                                                   
                     
                                                                         
                          
                                                                               
                                                                             
                               
                                                                   
                                                                              
                                             
                                              
                                              

end
end IsConservative
end SubMarkovKernelSemigroup

end RationalJointLaw

end MarkovProcess
