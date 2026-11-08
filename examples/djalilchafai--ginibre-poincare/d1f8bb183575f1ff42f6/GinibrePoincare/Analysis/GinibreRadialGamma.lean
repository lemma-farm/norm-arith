module

public import GinibrePoincare.Analysis.EquilibriumProbability
public import GinibrePoincare.Analysis.HomogeneousRadialMeasure
public import GinibrePoincare.Analysis.GlobalPhaseAction
public import Mathlib
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-!
# Gamma law of the recentered Ginibre radius

The polynomially weighted hyperplane Haar measure is homogeneous of degree
`2 * recenteredGammaShape n`. Its quadratic-radius pushforward is therefore
a power-law measure on `(0,∞)`. The Gaussian factor tilts that power law into
the rate-one Gamma density; probability normalization fixes the constant.
The final theorem concerns `radialObservable` under the actual `ginibreMeasure`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Pointwise

namespace GinibrePoincare
noncomputable section

                                                               
                                                                     

                                                                   
                                                             
                                     

                                                                                    
def recenteredPolynomialMeasure (n : ℕ) : Measure (zeroSumHyperplane n) :=
  (recenteredVolume n).withDensity (fun w => vandermondeDensity w.val)

instance (n : ℕ) : SigmaFinite (recenteredPolynomialMeasure n) := by
  unfold recenteredPolynomialMeasure vandermondeDensity
  infer_instance

                                                                
                                                        
                                                    
                                                                      
                             
       

                                                             
                                                              
                                                             
                                                                         

                                         
                                               
                                        
                        
                                
                                              
                                                          

                                                       
                                    
                             
       

                                                                          
                                                      
                                                                          
                                      
                                                                              
                     
                             
                 
                             
                                    
           
           

                                                                             
                                                                     
                            
                                                                              
                              

                                                                         
                                                                   
                         
                                                                         
      

                                                                   
                                                                                             

                                                                                   
                                             
                                                                          
                                                                    

                                                                 
                           
                                
                                                                                 
                                                                                            
         
                                             
                                                                   
                                            
                                                                 

                                                         
                                                                      
             
            
                                                      
                                                            
                                          
                     
         
                                                
                                                                                 
                                      
              
                                                

                                                                               
                                         
                                                                      
                                                                        
                                               
                                                         
                                                                             
                                                                  
            
                                             
                    
                                                                  
         
                                             
                                                
                                                         
                                                                   
                                                                                         
                                      
                                     
           

                                                                              
                                                                            
                                                         
                                                                                  
                                                                                       
                                                                                 
                                                              
                                           
                                    
                                                                                         
                           

                                                                      
                                                                          
                              
                                                                             
                                                             
                                                 
                                                      
         
                                                                                   
           
                                    
                                                                  

                                                             
                                                          
                                           
                                                                                               
                                    
                                                                                   
                                                                        
                                                         
                                        
                                                                                       
                
                                             
                                                      
                                                               
                                                                         
                                                                                   
                                      
                                                                
                                         
                                               
                                                                                    
                               
         
              
         

                                                                            
                                                                 
                                                              
                                        
                                                                         
                                                       
                              
                                         
                                                        
                                                                          
                                                            
                                              
                                                                 
                                                  
                                                           

                                                                        
                                                                     
                                                                     
                                                
                                                 
                                                                          
                                                                      
                                                                        
                                   
         
                                    
                                                                                   
                                                                        
                                                                                      
                                                                                                              
                                
                                       
         
          
                                                      
                                                                      
                                        
                                             
                                                       
             
                                           
                                                                                    
                                               
                                                                                                      
             
        
                                                          
                                

                                                                                 
                                                             
                                                           
                                                       
                              
                                                                
                                                                     
                                             
                                                                          
                                                                 
                                                         
                                                                                       
                                                                              
                                                                             
                                                 
                                                                 
                                                                                   
                                   
                                                                   
                                                               
                             
                      
                                                                                

                                                                              
                                                                   
                                                             
                                                 
                                                              
                              
                                                                                      
                                                                         
                                        
                                                                  
                                                                         

end
end GinibrePoincare
