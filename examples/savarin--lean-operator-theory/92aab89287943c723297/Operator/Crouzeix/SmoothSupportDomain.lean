/-
# Smooth Jordan domains from rounded finite support functions

The rounded log-sum-exp support curve and its open halfspace envelope provide
all fields of `SmoothJordanDomain`.  This file packages that construction and
uses arbitrarily tight scale choices to discharge the remaining planar outer
approximation problem, culminating in the exact polynomial
Crouzeix--Palencia theorem.
-/
import Operator.Crouzeix.SmoothSupportCurveRange
import Operator.Crouzeix.SmoothSupportEnvelopeTight
import Mathlib
open Complex Metric Set
open scoped ContDiff InnerProductSpace

                                                                         
                                                                
                                                     
                                                    
                                         
                                                                   
                                         
                                                
                            
                                      
                                        
                                                      
                                                                  
                                                          
                           
                                                    
                           
                                                     
                               
                           
                                      
                               
                                  
                                                      
                                                     
                        
                                             
                                                          
                                 
         
                          
                                                      

                                                           
                                                    
                                         
                                                                   
                                         
                                                
                                        
                                      
                               
                                                   

                                                                              
                                                       
                  
                
                                                       
                    
                
                                                             
         
                             
                                                                      
          

                                                                           
                                                                 
                                                                           
                                                                  
                           
                                                           
                                           
                                                  
                                                       
                   
                         
                                                             
                        
                                                 
                                                           
                                   
                                                      
                             
                        
                                                                             
                                                                              

                                                                           
                           
                                              
                                                    
                                           
                         
                                                    
                                                                  

                                                    
                                                    
                                           
                                                           
                               
                                                   

                                                          
                                                    
                                           
                                                                 
                                                    

                                                                          
                               
                                                       
                                                       
       
                                                                       
                                  
                                                                    

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

                                                                         
                                                                            
                 
                                           
                                                
                                        
                                                  
               
               
                                                    
             
                                                                    
                           
                      
                                                     
                                                                 
               
         
                                                                       
                                                       
