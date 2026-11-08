import Mathlib

/-!
# The 4-bit Walsh transform

This file isolates the finite Fourier algebra used by the hyperplane
partition argument.  It contains no geometric or measure-theoretic input.

The key point is that for four signs, equality of all 16 cell masses is
exactly equivalent to vanishing of the 15 non-trivial Walsh coefficients,
provided the trivial coefficient is the total mass.
-/

noncomputable section

namespace SoberonConvexBody
namespace Walsh4

open scoped BigOperators

set_option maxRecDepth 200000
set_option maxHeartbeats 0

abbrev Pattern := Fin 4 → Bool
abbrev Index := Finset (Fin 4)

/-- The ±1 character of the Boolean cube associated with `I`. -/
def charZ (I : Index) (s : Pattern) : ℤ :=
  ∏ i ∈ I, if s i then 1 else -1

/-- The same character, viewed as a real number. -/
def char (I : Index) (s : Pattern) : ℝ := (charZ I s : ℝ)

                                                               
              

                                                             
                    

                                                               
                                 
                                                                    
        

                                                            
                                                                         
                                                                  

                                                                          
                            
                                                                  
        

                                                
                             
                    
                                                                          
        

                                                                         
                                                  
                               

                                                   
                                            
                        

                                            
                                            
                                                                      
                                   
                                                                                           
           
        
                   

                                                         
                                                   
                                                                    
           
      
                  
      
                                                                          
                                       
                                                          
                     
                                      
                                  
                                        
                       
                                 
                                        
                       
                  
                                     
                                               
                   
                                      
                     
                                   
                 
              
  
                                                                                
                                     
                                                   
                                                     
            
                  
              
                       
                                               
               
                                          
         
      

                                                                              
                                    
                                           
                                 
                                
                                                       
                                         
         
                    
             
                                                           
             
        
                                             
                                          
                                        
                              
                                                                                     
                                     
                    
                               
           
      

                                                                       
                                               
                                 
                                             
                                       
                                                         
             
            
                                                         
                 
                                                     
                                          
                 

end Walsh4
end SoberonConvexBody
