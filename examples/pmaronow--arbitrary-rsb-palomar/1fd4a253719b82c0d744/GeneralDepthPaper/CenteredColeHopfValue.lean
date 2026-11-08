module

public import GeneralDepthPaper.CompactTiltResponse
public import GeneralDepthPaper.UnitTiltAverage
public import GeneralDepthPaper.GaussianVarianceRatio
public import GeneralDepthPaper.ColeHopfCentered
public import Mathlib
@[expose] public section


/-! The actual centered Cole–Hopf value is jointly C∞ as a bounded spatial
function, including at mass zero. The auxiliary-tilt response supplies its
removable extension and the exact Gaussian precision identity handles variance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

                                                                              
                                                           
                                                                          
                                                        
                                                                                                
                                                                                                       
                               
                                                                                           
                                       
                                                                                       
                      
                                                                   
                                                  
                                                                      
                                                           
                                                     
                                                                    
                                                 
                                                                          
                                                                         
             
           
                           
                              
                 
                                                    
                                                                          
                                                                            
             
                         
          
                                             
                                                                          
                                                                     
             
           
                           
                              
                 
                                                    
                                                                          
                                                                            
             
                         
          
                                                                    
            
                                      

                                                                              
                                                    
                                                              

                                                             
                                            

                                                                            
                                            
                                         
                                                                                   
                               
                                         
                                                                     
            
                                             
                                                                               
             
                                                                      
                                                       
                                 
                               
                                       
            
                                                                             
                                                                                             
                                 
                                                                  
                                                           

                                                                                    
                              
                                                                                
                                                                     

                                                                                 
                                    
                                                             
                                                                             
                                                                                                  
                                      
                                
                                                       
                                                                                        
                                                                                                               
                                                              
                                                                             
                                                         
                                                               

                                                                                 
                                                
                                                                       
                                                                       
                                                                                     
                                                                                                      
                                   
       
                                                                                            

end GeneralDepthPaper
