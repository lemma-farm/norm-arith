module

public import GeneralDepthPaper.CompactTiltKernel
public import GeneralDepthPaper.TerminalReconstruction
public import GeneralDepthPaper.GaussianNormalizerUnits
public import Mathlib

@[expose] public section


/-! Normalized compact-tilt responses are actual Gaussian increment averages,
with joint smoothness in all Banach parameters. The proof differentiates the
analytic bounded kernel and uses its genuinely positive uniform normalizer. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

                                                                                     
                               
                                                                                                      
                                                           
                         
                                                            

                                                                
                                                                

                                                                                       
                                                                                          
                                                            
                                                                       
                              
                                                  
                                   
                                                                                                
                                               
               

                                                                                
                                                                                   

                                                                             
                                                                                      
                                                                          
                                                  
                                                          
                                                                           
         
            
                                         
                           
                                     
                               
                                                                 
                                                     
                                        
                                                                                        
                                                                                            
                                                                                 
                       
                               
                                                               
                                                                              
                                                                                                  
             
                                                                             
                      
                              
           

                                                                                        
                                            
                                    
                               
                                              
                                                  
                                                     
         
                                                  
         
                                                  

                                                                              
                                                            
                                       
                                                                                
                                                                             
                                                                               
                                                                   
                                          
                                                        
                                                   
                                                                   
                                                                                       
                                                                           
                              
                                                           

                                                                                            
                                                          
                                               
                                                                                     
                               
                                                                             
                                                                                  
                                              
                                                                                    
         
                                                                        
                         
                                                                     

                                                                                
                                            
                                                                                    
                                                                                                      
                                                              
                                                                                       
                                            
                                                                                
                           
                         
          

                                                                                                        
                                             
                                                        

                                                                                    
                                              
                              
                                                        
                                                                             
                                                                                
                                                      
                                                            
                                                     
                                                                                     
                                                                                      
                               
      

                                                                                         
                                                                   
                                                                                                   
                                                                           
                                                                                               
                                                                       
                                       
                                                                             
                                                                        
                                                      
                                                                                                           
                                                                      
                                                        
                                                                       
                                                              
                                                                                                                     
                                                                                                 
                    

end GeneralDepthPaper
