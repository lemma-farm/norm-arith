module

public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Sobolev.W1p.Basic
public import Mathlib
/-!
# Smooth functions on bounded Sobolev domains

This file packages globally `C¹` scalar functions as representative-level
`W^{1,p}` functions on bounded measurable domains. Compact support is not
required: continuity on the compact closure of the domain supplies uniform
bounds for the function and each coordinate of its classical gradient.

The stored weak gradient is exactly `classicalGradient`, so later smooth
approximation arguments can use the same gradient API as the quantitative
regularity estimates.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace W1pFunction

                                                                       
                             
                                                    
                                        
                                                   
                                                 
            
                             
             
                                                        
                                 
                                       
                                              
                                                   
                                                    
                
                      
                                                     
                                    
                                           
                           
                                                     
                                    
                                       
                                                              
                                                        
                                                 
                              
                 
                                                        
                                 
                                                   
                                                    
           
                          
                                                           
                                                
                                                                   
                
                      
                                                     
                                       
             
                                                         
                           
                                                     
                                       
                                       
                                                                 
                                                        
                                                 
                              
                    
                                    

       
                                                
                                        
                                                   
                           
                                       
                                  
     

       
                                               
                                        
                                                   
                           
                                       
                                                   
     

                                                                 
                         
                                                       
                                        
                                                      
                                              
                                    
                                

       
                                                   
                                        
                                                      
                           
                                          
                                  
     

       
                                                  
                                        
                                                      
                           
                                          
                                                   
     

end W1pFunction

end PDE
