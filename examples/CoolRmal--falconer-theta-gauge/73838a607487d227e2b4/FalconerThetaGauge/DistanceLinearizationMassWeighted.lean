module

public import FalconerThetaGauge.DistanceLinearizationMassPassing
public import Mathlib
/-! # Genuine weighted and unweighted passing distance pushforwards -/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

/-- The literal unweighted passing distance measure used in Estimate 7.7. -/
def passingUnweightedDistanceMeasure (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (Z : Set (Plane × Plane)) : Measure ℝ :=
  (((ρ₁.restrict X).prod (ρ₂.restrict Y)).restrict Z).map
    (fun z : Plane × Plane ↦ dist z.1 z.2)

instance (ρ₁ ρ₂ : Measure Plane) [SFinite ρ₁] [SFinite ρ₂]
    (X Y : Set Plane) (Z : Set (Plane × Plane)) :
    SFinite (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z) := by
  unfold passingUnweightedDistanceMeasure
  infer_instance

instance (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    (X Y : Set Plane) (Z : Set (Plane × Plane)) :
    IsFiniteMeasure (passingUnweightedDistanceMeasure ρ₁ ρ₂ X Y Z) := by
  unfold passingUnweightedDistanceMeasure
  infer_instance

                                                                                    
                                                                        
                                                
                                                                      
                                                                             
                                                                                           
                                           
         
                                     
                                                                        
                             

                                                                             
                                                                                 
                                                                      
                                                                                      
                                                             
                                                
                                                            
                                                                        
                                                                                                   
                        
                                                     
                        
                                                                                           
                            

                                                                          
                                                                                 
                                                                      
                                                                                      
                                                             
                                                      
                                                      
                                                                        
                                                                                                   
                        
                                                     
                        
                                                                                           
                            

                                                                                 
                          
                                                                       
                                                                          
                                                                               

                                                                                
                                                                                   
                                                                                             
                                                                                      
                                             
     

                                                               
                                                                                      
                                                                                      
                                                                       
                                                                    
                                                          
                                                                                      
                                                                
                                                                                 
                                                                  
                                                                          
                  
                                 
                                                                                          

                                                                 
                                                                                      
                                                                                      
                                                                       
                                                                                    
                                                            
                                                                      
                                                              
                                                                                 
                                                                  
                                                                          
                  
                                 
                                                                                          

end FalconerThetaGauge
