module

public import GinibrePoincare.Concrete.Weights
public import GinibrePoincare.Concrete.GaussianProbability
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Data.ENNReal.Real

@[expose] public section

/-!
# Concrete Gaussian density and Ginibre measure

The Gaussian reference measure `complexGaussianMeasure n` is constructed in
`GaussianProbability.lean` as a genuine finite product probability measure.
This file also defines the explicit density measure

`(n / π)^n exp (-n |z|²) dz`.

Equality of these two descriptions is stated explicitly as
`ComplexGaussianDensityIdentificationStatement`; it is not hidden in a
definition.  The unnormalised Ginibre measure is then `|V_n|² γ_n`, and its
actual total mass is used for normalization.
-/

open MeasureTheory
open scoped ENNReal

namespace GinibrePoincare

noncomputable section

                                                                                
                                                              
        

                                                                             
                                                                  
                
                                                    

                                                                 
                                                                        
                                                                

                                                                         
                                                             
                                                           
                  
                                                              

                                                                      
                                                                              
                                                            
                                                       
                          
                                                      
               
                                     

                                                           
def vandermondeDensity {n : ℕ} (z : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal (vandermondeWeight z)

                                             
                                                            
                                                           

                                                             
                                            
                              

                                            
                                                         
                                                    

                                                                
                                        
                                                             

                                                                                  
                                            
                                       

                                                                          
                                                  
                  
                                 

                                                                         
                                                 
                                
                                       
                            
                                                                        
                                               

                                                                             
                                       
                                                                 
                                
                                              
                                         

                                                                         
                                                      
                                          
                                              
            
                                                    

                                                                        
                   
                                                              
                                                               
                                              
                                                              

end

end GinibrePoincare
