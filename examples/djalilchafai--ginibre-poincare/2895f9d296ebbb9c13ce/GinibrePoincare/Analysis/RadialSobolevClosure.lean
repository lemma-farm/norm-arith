module

public import GinibrePoincare.Analysis.EntropyL2Closure
public import GinibrePoincare.Analysis.GaussianRadialLift
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- The actual real Euclidean gradient, as a vector with `2n` coordinates. -/
def ginibreEuclideanGradient {n : ℕ} (f : Configuration n → ℝ) (z : Configuration n) :
    EuclideanSpace ℝ (Fin n × Fin 2) :=
  WithLp.toLp 2 (fun k => if k.2 = 0 then fderiv ℝ f z (realCoordinateDirection k.1)
    else fderiv ℝ f z (imaginaryCoordinateDirection k.1))

                                                                                                  
                                                                     
                            
                                                                            
                                               

                                                                             
                                                                         
                                                                  
                     
         
                      
                                 
                                                                                                      
                                  
                                                                                                           

                                                                                 
                                                                                     
                                 
               
          
                                     
     

                                                                   
                                                     
                                                

                                                                                 
                                        
                                                                                               
                                                         
                                                        
                                                                                   
                                 

                                                                                                   
                                                                      

                                                                              
                                                       
                                                            
                                   
                                                          
                                                                                     
                                        
                                                
                                           
                                                         
                                                                      
                                                                             
                                                          
                                                                        
                                               
                       
                       

                                                                      
                                                                              
                                                                               
                                   
                           
                                                
                           
                                                

                                                                        
                                                                                   
                                       
                                                 
                                        

                                                                        
                                                                             
                                                             
                                                               
                                                           
                                 
                                                                                 
                                                                              
                                                
                                
            
                              
                                                                              
                               
                                                                              
                                         
                           
                                 
                                             
             
                                                                                 
                                                      
                  
                    

end
end GinibrePoincare
