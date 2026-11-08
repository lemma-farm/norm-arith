module

public import FalconerThetaGauge.DistanceMeasure
public import FalconerThetaGauge.RadialProjectionDefinitions
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# The manuscript's weighted filtered distance measure

The density is the extended inverse square root of the Euclidean distance.
It is infinite on the diagonal, as required by the actual singular weight;
the separated carriers used later make it bounded almost everywhere.
The mask is a real Borel function with values in `[0,1]`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerThetaGauge

/-- The true weight `|x-y|^(-1/2)`, retaining its infinite diagonal value. -/
def crossDistanceWeight (p : Plane × Plane) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.sqrt (dist p.1 p.2)))⁻¹

           
                                                                             
                            
          

       
                                                                                       
                            

                                                                                     
                                                 

                                                                   
                                                                                
                                                                             

                                                                                      
                                                                     
                                                  
                                          

/-- The actual weighted pushforward after multiplying by a pair mask. -/
def filteredCrossDistanceMeasure (μ ν : Measure Plane) (m : Plane × Plane → ℝ) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun p ↦ crossDistanceWeight p * ENNReal.ofReal (m p))).map
    (fun p : Plane × Plane ↦ dist p.1 p.2)

                                                                                   
                                                                                   
                                                                 

           
                                                                                    
                                       
                                       
                              
                                                                                              
                                                    

                                                                       
                                                                                     
                                                
                            
                                                                      
                                                              

                                                                    
                                                                 
                                                                     
                                                     
                                                     
                                                                       

                                                                                  
                                                                                     
                                    
                                                                               
                                                     
                        
                               
      
                                                                               
                                                                     
                                          

       
                                                                 
                                                                                       
                                                                                
                                                                              
                          

       
                                                                                         
                                             
                                                                        
                                                                                
                                                                              
                          

                                                                           
                                                                  
                                                                
                                                      
                                                   
                                        
                                  

                                                                                          
                                                                                
                                                                       
                                                                         
                                     
                                                    
                                               
                                                                                     
                          
                             
                                                                           
                               
                             
                                                                                      
                                           
                       
                                                                  
                                          
      
                                           
                                                            
                                                                         
                                                                        
                            
                                                                                       
                
                                
                                                   
                                                                                        
                  

end FalconerThetaGauge
