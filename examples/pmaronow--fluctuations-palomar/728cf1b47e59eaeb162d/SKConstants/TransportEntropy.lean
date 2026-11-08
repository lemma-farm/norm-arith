module

public import SKConstants.TransportStrongConvex
public import Mathlib
/-!
# Sharp transport from the proved Gibbs infimal-convolution inequality

The scalar entropy and variational argument is adapted from OpenAI/math,
`lean/OAI/Probability/SKGap/Entropy/EntropyTransport.lean`, commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (Apache-2.0).
The coupling is constructed by the proved Hopf-duality theorem; no transport
inequality or coupling-cost bound is a hypothesis.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace SKConstants.Transport
open WeakHessianTransport
set_option backward.isDefEq.respectTransparency false

                                                      
                                     
                                  
                                      
                                                                          
                                                           
                
             

                                                           
                                                                       
                                                          
                                              
                                                                      
                                              
                                                        
                                                            
                                                                      
                                                          
                                               
                                      
                                                                         
                                                               
                                                                    
                 

                                                               
                                                     
                                                                             
                                                               
                                          
                                   
                                                             
                                                
                            
                      
                        
                                                  
                                                                            
                                                                     
                                    
                                                       
                                                   
                                                           
                                         
                                                                         
              
                              
                                            
                                
                                                                
             
                                                                 
                               
                                                       
                                                             
                                
                                                           
            
               
                                        
          

                                                                            
                                                                               
                                         
                                                                              
                                                     
                                                                             
                                                                 
                                                            
                                                   
                                          
                                                                          
                                               
                                                                  
          
          
               
                                        
                                                                     
                                                                 
                                                                                  
                                                            
                                  
                                                               
                                                                 

end SKConstants.Transport
