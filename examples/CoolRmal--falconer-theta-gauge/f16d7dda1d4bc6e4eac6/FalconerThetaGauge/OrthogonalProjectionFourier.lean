module

public import FalconerThetaGauge.OrliczEnergyFourier
public import FalconerThetaGauge.RadialProjectionPolar
public import FalconerThetaGauge.OrthogonalProjectionFourierDensity
public import Mathlib
/-!
# Orthogonal Fourier slices at the logarithmic endpoint

The projection is the actual inner-product pushforward. Polar coordinates
give its averaged weighted Fourier energy, and reflection yields square
integrability on almost every full line. No power Frostman exponent is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace FalconerThetaGauge

def orthogonalProjection (v x : Plane) : ℝ := ⟪x, v⟫

def orthogonalProjectionMeasure (μ : Measure Plane) (v : Plane) : Measure ℝ :=
  μ.map (orthogonalProjection v)

@[fun_prop]
theorem continuous_orthogonalProjection (v : Plane) : Continuous (orthogonalProjection v) := by
  unfold orthogonalProjection
  fun_prop

instance orthogonalProjectionMeasure.instIsProbabilityMeasure (μ : Measure Plane)
    [IsProbabilityMeasure μ] (v : Plane) : IsProbabilityMeasure (orthogonalProjectionMeasure μ v) := by
  unfold orthogonalProjectionMeasure
  infer_instance

                                                                            
                         
                                                                         
                                                                                           
                  
                         
                                       
                                                                            
                                                 

                                                                                  
                         
                                                        
                                                                 
                                                                                             
                                       
                                                                     
                                                                 
            
                                                                           
                                
                          
                                                                                       
                           
                                                                            
                                                                    
                                                                                         
      
      
                                                       
                                                                        
                                                                   
            
                                

                                                                                      
                         
                                                        
                                                                                                    
                                                       
                      
         
                         
                                                              
                                                 
                                              
                                                                          
                                     
                                                                               
                             
                                                             
                                                                                        
                             

                                                                              
                                                             
                                                                                   
                                                            
                                                   
                                                                 
                                    

                                                                               
                                                               
                                              
                                                           
                                             
                                           

                                                                  
                                                                                               
                                                   
                                                                                         
                                                                            
                                   
                                                        
                                                                               
                                                 
                                                                                                
                                        
                                                               
                                              
                                                                                     
                                                                     
                                                       
                                                    
                                                     
                                                            

                                                                         
                                                                                               
                                         
                                                                                
                                                      
                                                                        
                                                     
                                                                         
                                                                         
                                                                                   
                                                                                         
                    
                                                
                                                             
                                                                   
                                                     
                                                       
                                                              
                                                                
                                                                  
                                                                                        
                                             
                
                                    
                                                                                       
                                        
                                                               
                                              
                                                     
                                                             

end FalconerThetaGauge
