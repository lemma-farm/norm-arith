module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Additive local ball overlaps

The ball axioms below are the elementary properties of `π⁻ᵃ O` in a discretely
valued local field with normalized additive Haar measure.  In particular, no
overlap formula is assumed.  They also make explicit the outstanding bridge
to a chosen construction of local completions.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace UnitDistance.Local

attribute [local instance] Classical.propDecidable

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

/-- A nested family of measurable additive balls with its ordinary Haar volume.
The positive real `Q` is the residue cardinality in the intended application. -/
structure BallSystem (G : Type*) [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (Q : ℝ) where
  ball : ℤ → AddSubgroup G
  mono : Monotone ball
  measurable : ∀ a, MeasurableSet (ball a : Set G)
  volume : ∀ a, μ.real (ball a : Set G) = Q ^ a

namespace BallSystem

variable {μ : Measure G} {Q : ℝ} (B : BallSystem G μ Q)

                                                                                   
                                            
                                       

                                                  
                                          
                                                                                

omit [MeasurableAdd G] in
                                                          
                                                              
       
                                                                       

omit [MeasurableAdd G] in
                                                                   
                         
                                                                       
       
             
                   
            
                   
                                               
                    

omit [MeasurableAdd G] in
                                              
                                                               
                                          
                    
          
                                    
                                                                 
                  

                                                                         
                                                                                   
                                                                      
                                  
                                                           
           
                   
                                  
                               
                                                               
                              
                                                                
                                                                                
                                  
        

                                                                    
                                      
                                                                   

omit [MeasurableAdd G] in
                                                                           
                                                 
                                                                                     
           
                                                                                   
                               
                        

                                                                           
                                                  
                                                             
                               
                                                                  
                                                        
                                                 
           
                                         
                                
                                                                                 
                                                  
                                               
                        

                                                                           
                                                                                 
structure ReciprocalSteps (U : Type*) where
  step : ℤ → U → G × G
  fst_mem : ∀ n u a, (step n u).1 ∈ B.ball a ↔ -a ≤ n
  snd_mem : ∀ n u b, (step n u).2 ∈ B.ball b ↔ n ≤ b

variable {U : Type*} [MeasurableSpace U] (S : B.ReciprocalSteps U)
    (ν : Measure U) [IsProbabilityMeasure ν]

                                                                       
                                                          
                                      
                                         
                                                 

                                                                  
                     
                                                                   
                     
                                            
                                                 
                                                     
      

                                                                              
                                                                                
                                                            
                   
                                 
                                                                           
           
                      
                                        
                                                         
                                                                                     
                     
                                                                    
        
              
             

end BallSystem
end UnitDistance.Local
