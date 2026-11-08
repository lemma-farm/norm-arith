module

public import SphericalAging.FiniteModel
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Pi

public section

/-!
# Gaussian integration by parts for the actual ordered tensor law

The one-dimensional identity is derived from the actual Gaussian density and
improper integration by parts. The finite product identity uses Fubini and a
measure-preserving separation of the selected tensor coordinate. The hypotheses
are differentiability and integrability, rather than a Stein-identity premise.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SphericalAging.GaussianIntegrationByParts
open FiniteModel

                                                     
                                     
                                                                  
                                                                  
                                                   
                                                                             
                                                   
                                                           
                                                                      

                                                     
                                                                       
                        
                                     
                                                                          
                                        
            
                                                       
                                                       
        

                                                                                     
                                                            
                                     
                                          
                                            
                                                            
                                                                      
                                                   
                                                     
                                                     
                                                                           
                                                                           
                                                    
         
        
                                                                         
                                                            
                                                                                 
                                                                           
                                                                         
                              
                                                    
                                                     
                       
                           
                                        
                         
                 

section FiniteProduct
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

                                                             

                                                                                          
                      
                                             

                                                                              
                                                                                  
                                                         
                                                                              
                                                                                       
                                                      

                                                   
                                                                                      
                                                                                                   
                                                        
                                                                                      
                                                                                   
                                                                                      
                                                                                           
           
                               
                                                                                                           
                                                                                           

                   
                                                                                      
                                            
                                                                                                                                                          

                   
                                                                                    
                                                                                             
          
                   
           
                                          
                                                                                                                                                               

                                                                                            
                                                                        
                                                                               
                                     
                                                                    
                                                                      
                                                                                                
                                                                       
                                                                           
                                                                                    
                                                       
                                                                 
                                                                    
                                                                    
                                                                    
                                                                          
                                    
                                                                           
                                                          
                         
                                                                                         
                                                                                
                                                   
                                                                                        
                                                                
                                                                                   
                                                                           

end FiniteProduct

                                                                                              
                                                                     
                             
                                                                                      
                                     
                                                                                 
                                                                            
                                                   
                                                    
                                                     

                                                                                              
                                                                           
                                                                         
                                 
                                               
                                                                                         
                                                  
                                                    
                                                                                           
                                                                  
                                                                    
                                                        
                         
                                                                                      
                                                         

                                                                                  
                                                                                          
                                      

                                                                                     
                                                                                   
                                           
                     
                            
           
      

                                                                                                     
                                                                                                  
                                                                  
                                                   
                                                                                   
                                                                      
                                                                                  
                                           
                                
                                                                                      
                                                                               
                                 
                                                                                   
                                     
                                                                                                   
                                                                                    
                                                                                             
                                                   
                                                                                                
                                                       
                
                                                         
                                             
                                                
                              
             
                                                                                         

end SphericalAging.GaussianIntegrationByParts
