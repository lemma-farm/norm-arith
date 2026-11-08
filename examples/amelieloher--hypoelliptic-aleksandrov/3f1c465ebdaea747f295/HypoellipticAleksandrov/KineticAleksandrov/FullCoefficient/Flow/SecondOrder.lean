module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Derivs

/-!
# First and second derivatives of the Gaussian kernel

For `Φ = K * gaussExp a b c` the first and second coordinate derivatives are the explicit
polynomial multiples
`∂_δ Φ = -K * gen δ * G` and `∂_δ' ∂_δ Φ = K * (gen δ * gen δ' - genCoeff δ δ') * G`.
These give the Laplacians and the mixed divergence of the flow kernel.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

                                                                                    
                                         
                   

                                                                       
                                   
                                                                                                
                                                                                               
                                      
           
      

                                                                     
                                   
                                                                                
                                                 
                   
                              
           

                                                                           
                                   
                                                                    
                                                                                         
                                                          
                                                            
            
                                      
         
                                                                 
                                                   
                                                                    
      

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
