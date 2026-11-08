-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CrisantiSommers
public import SlowEquilibration.CSVariation
public import SlowEquilibration.NonconvexCertificate

@[expose] public section

namespace SlowEquilibration.CrisantiSommers

open MeasureTheory Set

/-- The manuscript's admissible measures, with their ordinary probability law.
The cutoff is a witness of compact support below one, not a parameter of the value. -/
structure Admissible where
  law : Measure ℝ
  probability : IsProbabilityMeasure law
  cutoff_exists : ∃ q, HasCutoff law q

instance (ζ : Admissible) : IsProbabilityMeasure ζ.law := ζ.probability

                                                           
                                  

                                                                           
                                       

                                                                              
                                                                              
                               

                                                                
                                      
                                           
                                                        

                                                                          
                                                         
                                                                         
                                             

                                                                   
                                                               
                                                              
                                                              
                           
         
                                                                    
                                              

                                                          
                                                  
                                                                             

                                                              
                                            
             
                                                                                       
            
                                                      
          

                                                            
                                   
                       
                                  
             
                                 
                           
                          
                                 
                           
                          

                                                                       
                                                   
                                                                    
                                                                   
                                                                    
                                                                   
                                                                                        
                                                                               

                                                                            
                                                     
                          
                          
                                                
             
                          
                            
                  
                       
        
                                     
        

                                             
                                                                 
                                                               

end SlowEquilibration.CrisantiSommers

namespace SlowEquilibration.NonconvexCertificate

open MeasureTheory Set CrisantiSommers

                                                                                       
                                            
                                                                        

                                              
                                                        
                                                 
                                                                         
     

                                                                  
                                                        
                         
              
                                                                                 
                                             
                                         
              
                              
              
                             
          
      

                                                                     
                                                              
                                                                   
                                                                     
                                        
                                                                                                 
              
                                     
                     
                         
                     
                             
                                                    
                                                
            
                                                                      
                                   
               
                                   
                      
                                                              
                                                                    
                                   
                      
                                                                    
                                                                        

end SlowEquilibration.NonconvexCertificate
