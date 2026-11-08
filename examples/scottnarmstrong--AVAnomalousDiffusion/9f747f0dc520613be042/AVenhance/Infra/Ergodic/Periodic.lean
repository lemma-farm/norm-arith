-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Homogenization.Ambient.Basic
public import AVenhance.Statements.Roots.IsZ2Periodic
public import Mathlib

/-! # Periodicity for functions on Euclidean space

This local predicate records invariance under the integer lattice.  The
ergodic lemmas use it for scalar functions on `Vec d`.
-/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open MeasureTheory

noncomputable section

local instance avInfraErgodicPeriodicMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance avInfraErgodicPeriodicMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance avInfraErgodicPeriodicIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A function on `Vec d` is `ℤ^d`-periodic when it is invariant under every
integer lattice translation. -/
def IsZPeriodic {d : ℕ} {α : Type*} (f : Homogenization.Vec d → α) : Prop :=
  ∀ (x : Homogenization.Vec d) (k : Fin d → ℤ),
    f (x + fun i => (k i : ℝ)) = f x

/-- The Euclidean vector represented by an integer lattice vector. -/
def latticeVector {d : ℕ} (k : Fin d → ℤ) : Homogenization.Vec d :=
  fun i => (k i : ℝ)

                                                                         
                        
                                                                                 
                                                  
             
                
                
                
                

                                                 
                                                                           
                                               
                                              

                                                                                 
                                                                
           
                                                                
                                
            
                                                         
                                              
              
                                                         

                                                          
                                                

                                                                
                                                       
                                    

                                                                    
                                                                              
                                                                           

                                                                          
                                                               
                                                                     

                                                                                
                                                 

                                                                            
                                                                         
                                                                         
                                                                    
                            
                              

                                                          
                                                          
                    
                                                       
                                           
                                                                                    
           
                                   
                                                          
                                                    
                                                    
           
                            
                                                                                      
                                      
                                                              
           
                                                                                             
                                      
          
                                                                  
                  
                                                                         
                                   
            
                           
                
          
                    
                                                                          
           
                      
           
                                 
                                                         
              
        
                                      
                                                         
              

                                           
                                                         
                                                             
                                                                      
                                                                             
                        
                                                      
                                               
                                                        
                                                                    

                                                                       
                                                            
                                                             
                                      

       
                                           
                                                             
                                   

                                                                              
                                                               

                                               
                                    
                                                   
                    
                                                            
      
                            
                                           
                                                              
                                                     
                                                                    
                                       
                                 
                                                           
                
                                                                                   
                
                                                            
                          
                                            
                                                                         
                                                                              
                           

end

end AVenhance.Infra.Ergodic
