module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib
/-!
# Coordinate basis of the native ambient space

The coordinate basis and its exact dot-product and Euclidean-length formulas.
-/

@[expose] public section

namespace PDE

/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

       
                                              
                                               
                    
           
                   
                      

                                                              
                                     
                        
                             
        
                   
              
            
              

                                                               
                                     
                        
                             
        
                   
              
            
              

                                                
                                    
                                      
                 

                                                       
                                           
                                                          

                                                     
                                               
                                           
          
                       

end PDE
