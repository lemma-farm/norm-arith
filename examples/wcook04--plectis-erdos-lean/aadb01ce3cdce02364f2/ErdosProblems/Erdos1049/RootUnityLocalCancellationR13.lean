import ErdosProblems.Erdos1049.SourceFiniteTransformR12
import ErdosProblems.Erdos1049.SourceHomogeneousR12
import Mathlib

/-!
# Root-window cancellation for the actual Omega carry pattern



The two independent variables are important. The second Gaussian's lower
argument may exceed its upper argument in a residue block. Replacing the
integer exponent w-a+1 by truncated natural subtraction is incorrect.
This file proves the finite local identity with the integer exponent,
including these zero terms. It does not assume a local vanishing conclusion.
The remaining passage from source summands to residue blocks is separately
recorded, and is not smuggled in as an axiom here.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Finset
open scoped BigOperators

section CommRing
variable {R : Type*} [CommRing R]

                                                                   
                                                                  
                         
                                                            
                        
                                                               
                                       
                      
                     
            
                     
            
                                            
                                           
                                         
      

                                                                              
                                                     
                                                          
                                     
                                                              
         
                                            

                                                                         
                                                                          
                               
                                                                   
                                                                
                         
                                                                                
                                         
                   
            
                                                       
                                                           
                  
                                                            
                   

end CommRing

section Field
variable {K : Type*} [Field K]

                                                                          
                                                                           
                                                                   
                 
                                                
                                                           
                         
                                           
                                             
                                                                       
                                                               
           
                                         
                                     
                                                  
        
                                                                  
           
                                             
                                                     
                                                                 
                                                      

                                                                         
                                                         
                                                         
                                                  
         
                  
                
                
              
                           
                                       
                      
                                                                   

                                                                      
                                                     
                      
                                                   
                                               

                                                                           
                                                                         
                                                        
                          
                                                     
                                                     
                                           
                             
              
                     
            
                                                           
                                                                       
                                         
                                                          
                                               
        
                                                      

                                                                             
                                                                           
                         
                                                       
                                             
                                            
                                    
                                                             
                                                              
                                                      
                                        
                   
            
                                                       
                                                           
                  
                                                               
                   

                                                                              
                                                                     
                                           
                                                       
                                                           
                                         
                                                                   

end Field
end ErdosProblems.Erdos1049.PaperR13
