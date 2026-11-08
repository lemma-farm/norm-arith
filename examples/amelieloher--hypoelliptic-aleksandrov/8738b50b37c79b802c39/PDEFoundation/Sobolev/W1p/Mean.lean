module

public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Sobolev.W1p.Algebra
public import Mathlib
/-!
# Means of representative-level `W^{1,p}` functions

This is the compatibility layer needed by mean-zero Poincaré estimates.  The
arithmetic mean is the scalar definition from `PDEFoundation.Sobolev.Mean`;
subtracting it changes only the value representative and leaves the chosen
weak gradient exactly unchanged.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

                                                                     
           
                                   
                                  
                           
                                       
                                           
                               

                                                           
                                                      
                                   
                     
                    
             
               
                                                       
                 
           
         
                                                           
                       
                                         
                                                               
              
        

       
                                                  
                         
                                        
     

       
                                                 
                         
                                             
     

                                                                
                                         
                                  
                                   
                      
                               

       
                                     
                                  
                                               
                               
     

       
                                    
                                  
                                               
                                          
                                                      

                                                                              
                                           
                                  
                                              
                                         

       
                                       
                                  
                                       
                                                          
                                                        

       
                                      
                                  
                                       
                                        
                                       

                                                                   
                                            
                                  
                         
                                                   
                                         
               
                                  
                                
                      
                                               
                         

end W1pFunction

end PDE
