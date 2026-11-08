module
public import SpectralPerturbation
@[expose] public section

/-!
# Positive spectral energy of a signed bipartite block

The block retained by singular truncation can have signed entries. Its two
largest positive eigenvalues have squared sum at most the squared Frobenius
mass of the rectangular block. The argument uses PSD reflection and the
actual selected spectral lift, without assuming entrywise nonnegativity.
-/

namespace KKPAsymptotic
open Matrix
open scoped Classical
variable {H R : Type*} [Fintype H] [DecidableEq H] [Fintype R] [DecidableEq R]

                                                                 
                                                                          
                                                                                         
                                                                         
                                            
                                                                
                                                             

                                                                                           
                                                                                   
                                                                              
                                                                                    
                                 
                                                 
                                                         
                                                          
                                                                                      
                                                        
                                                                   
                                                           
                  
                         
                                          
                                                         
                                                         
                                                                 
                                                                                    
                                                                
                                                                         
               
        
                             
                                                         
                                                         
                                                                 
                                                                           
               
        
                         
            
          

                                                               
                                                                       
                                                       
                                                  
                                  
                         
           
                                                     

                                                                                              
                                                          
                                                                           
                                     
                                        
                                          
                  
                                                                      
                                                                 
                                     
                                                       
               
                                                                                      
                                                        
                                                                                            
                                                                            
                                                                                              
                                                                       
                                                                    
                                                                                 
        
                                                                        
                                     
                                                             
                                            
                                                                   
                                                                     
                                          
                      
                                              
                                                                         
                                                   
                                   
                      
              
           

end KKPAsymptotic
