module
public import SpectralPerturbation
@[expose] public section

/-!
# Orthogonal compression of the positive-two energy

Symmetric idempotent matrices act as orthogonal projections. Their two-sided
compression contracts Frobenius mass, and the variational characterization
then bounds the actual padded positive-two energy by the original energy.
-/

namespace KKPAsymptotic
open Matrix
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A X Y P : Matrix V V ℝ}

                       
                                                                     
                    
                                                                             

                       
                                               
                                                          
                                                    

                       
                                                
                                                          
                                     

                       
                                                                                     
                                            
                       

                       
                                                                                     
                                                                                   
                                                       
                                                            
                                    

                       
                                                                                
                                                                                      
                                                 
                                          
                                                       
                                                                     
          

                       
                                                                                 
                                                                                       
                                                 
      
                                                                   
                                                                
                                                             
                                   

                       
                                                                 
                                                                                  
                                                      
                                                                                        

                       
                                                                       
                                                         
                                                            
                                             
                              

                       
                                                                      
                                                                                        
                                 
                                           
                                                                        

                                                                                             
                                                                          
                                      
                                                           
                                            
                                          
                    
                  
                                                                      
                                           
                                                                                       
                         
                                                               
                                                                                
                                                                 
                                                                                  
                                     
                                                                                            
               
                                                  
                  
                                   
                            
                                                        
                                                                                       
                                          
                                                        
              
           

end KKPAsymptotic
