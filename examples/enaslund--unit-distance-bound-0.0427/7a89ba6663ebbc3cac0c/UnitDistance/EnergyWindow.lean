module

public import UnitDistance.Concentration
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section
set_option backward.privateInPublic true


/-!
# Removing the overlap density on the common energy window

`X` and `Y` are the two endpoint energies on the overlap space. Its ordinary
measure includes positions and displacements; the probability density is
`exp (-(X + Y)) / Z`. Zero-profile points are omitted from that space.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UnitDistance

noncomputable def overlapLaw {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) (Z : ℝ) : Measure Ω :=
  m.withDensity (fun ω => ENNReal.ofReal (Real.exp (-(X ω + Y ω)) / Z))

                                                       
                                                      
                                                          
                                        
                                 
                                                    
                                                          
                                         
                                                                                     
                                                            

theorem overlapLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (X Y : Ω → ℝ) {Z : ℝ} (hZ : 0 < Z)
    (hI : Integrable (fun ω => Real.exp (-(X ω + Y ω))) m)
    (hnorm : ∫ ω, Real.exp (-(X ω + Y ω)) ∂m = Z) :
    IsProbabilityMeasure (overlapLaw m X Y Z) := by
  constructor
  rw [overlapLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hI.div_const Z)
      (Filter.Eventually.of_forall (fun _ => div_nonneg (Real.exp_pos _).le hZ.le)),
    integral_div, hnorm, div_self hZ.ne', ENNReal.ofReal_one]

                                                                              
                                                                            
                                                         
                                                        
                                                 
                                                                       
                                                                        
                                                           
                                               
                                                 
                                                            
                                                    
                                     
              
                                            
                             
                               
                                                                  
                                      
                                                          
                                          
                                         
                                                                        
                                                          
        
                                              
                                                                                    
                                                          
                                                    
                                                                    
                                                                                     
                                                                
                       
        
      
                                                                        
                                                                                 
                      
                
                                      

                                                                             
                                                             
                                                                    
                                                    
                                                                       
                                                 
                                             
                                         
                                         
                                                  
                                                  
                             
                                                 
                                                 
                          
                                                               
                                               
                                                            
                             
                                                                           
                                                                                  
                           
                                                        
                                                     
                                                                 
                                                     
                                                                 
                                 
                                                                              
                                                                                               
                                                                                        
                                                      
              
                         
                                
                                
                            
              
                                
            
              
                                
            

                                                                          
                                                            
                                                      
                                                                         
                                  
                                                                           
                                                                                
                                                                              
                                                                     
                
                               
                          
                
                                                                                 
                                                              
                                  
                                                           
                                            
                                                      
                       
                                                   
                                                                                 
                                                                           
                                                                         

                                                                          
                                                                           
                                                                 
                                                    
                                                                    
                                                                                
                           
              
                       
                                 
                       
                                                                                

end UnitDistance
