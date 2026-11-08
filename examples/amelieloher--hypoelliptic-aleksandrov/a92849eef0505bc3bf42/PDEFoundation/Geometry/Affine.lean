module

public import PDEFoundation.Ambient.Basic
public import Mathlib.Data.Set.Basic

/-!
# Affine set operations on native vectors

Pure set-theoretic translation identities. Measure-preserving and integral
transport statements belong in the later measure layer.
-/

@[expose] public section

namespace PDE

/-- Translate a set of native vectors by `z`. -/
def translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) : Set (Vec d) :=
  {x | ∃ y ∈ U, x = y + z}

                                            
                                     
                                          
             
                       
                                     
            
                          
         
                                    

                                                 
                                   
                                                           
       
                                     

                                               
                                   
                                                            
       
                                                     

                                                 
                                   
                                                           
       
                                                                

                                              
                                   
                                                          
       
             
                       
                      
                       
                      

                                  
                                     
                                                                      
       
                                     

       
                                                     
                                        
       
                     

                                         
                                     
                                                                    
       
             
                                 
                                      
                       
                                                    

end PDE
