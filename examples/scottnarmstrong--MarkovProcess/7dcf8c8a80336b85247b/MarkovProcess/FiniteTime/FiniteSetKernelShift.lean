/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.FiniteTime.DenseTimeFiniteShift
import MarkovProcess.FiniteTime.KernelShift
import MarkovProcess.FiniteTime.ProjectiveFamily

/-!
# Translation of finite-set kernels

This file translates finite sets of nonnegative observation times, reindexes paths on the
translated set back to the original coordinates, and proves the corresponding translation law
for conservative transition-kernel semigroups.  It is finite-dimensional kernel infrastructure;
it does not assert a path-space Markov property.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

                                                                               
                                                                          
                            

       
                                                                              
                                                         
                                         
     

                                                                                     
                                                                                            
                   
                                                                                    
       
                 
                       
                                                     
      
             
                                                                          
                                        

       
                                                                                
                                                       
     

                                                                          
                                                                               
                                                          
                                              

       
                                                                                         
                                                     
                                                                                   
     

                                                                                     
                                      
                                                                   
                                                                                   

                                                                            
                                                      
                                                                       

                                                                           
                                                      
                                                              
                                          
                                                               
                                                           
                                                   
              
                                                                            
                                                          
                                           
             
                                                
                                                                                  
               
                                                     
                                                          
                                           
             
                                                      
                                          
                   
                                                                                       
                        
         
                                            

                                                               
                                      
                                                     
                                                                      
                                                                
                                                                  
               
                     
                                                           
                 
                                             
                                                            
                                              
                   
                                                       
                                                        
                                                                                    
                                  
                                             
                         
                                            
                                           
                                  
                                                                            
                                                                                    
                                                                         
                                                
                                                           
                                         
                                                                 
                          
               
                   

namespace IsConservative

variable {alpha : Type*} [MeasurableSpace alpha]

                                                                                          
                                                                                  
                                              
                                                                
                                      
                                                    
                                                           
                                            
                                                                              
                                                               
                                                
                                                   
                                                               
                                                                    
                        
                                                      
                                                            
                                               
                                                                    
                                                   

end IsConservative

end
end SubMarkovKernelSemigroup

namespace DenseTime

                                                                                           
                                
                                                                                 
                                                        
                                                                        
                                                    
       
                                                                                    
             
                                  
                                                                                  
                                  
           
                                                                        

end DenseTime
end MarkovProcess
