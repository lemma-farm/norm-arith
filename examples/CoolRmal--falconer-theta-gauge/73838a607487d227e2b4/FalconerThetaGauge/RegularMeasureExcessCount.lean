/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureExcessGauge
public import FalconerThetaGauge.RegularDecompositionMeasures
public import Mathlib
/-!
# Actual excess properties and occupied-cell counts of retained parts

The normalized retained carriers satisfy Lemma 5.10, and their occupied
descendants satisfy the counting estimate (5.2).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped Classical

namespace FalconerThetaGauge

open GaugeFrostman GaugeSeparatedMeasures

theorem measurableSet_unitSquare : MeasurableSet unitSquare := by
  rw [← biUnion_unitCellIndices 0]
  exact measurableSet_cellUnion 0 _

                                                                                       
                                                                                      
                                                                                  
                                  
                                                                 
                                                                                           
                            
                                                
                  
                                               
                                      
                                                                                      
                
                                                                                      

                                                                                      
                                                                                      
                                                     
                                                
                                     
                                              
                                                    
                                

                                                                                 
def occupiedCellDescendants (ρ : Measure Plane) (g p : ℕ) (q : Fin 2 → ℤ) :
    Finset (Fin 2 → ℤ) :=
  (unitCellIndices p).filter
    (fun k ↦ ancestor (p - g) k = q ∧ 0 < unitCellWeight ρ p k)

                                                                                    
                                                                              
                                             
                                                                   
                                
                                               
                                                                       
              
                                                         
                                                
      
                                                                          
                               
                                                                                          
                                                                               
                                                         
               
                                        
                                                                
                                                                                     

                                                                                    
                                                                                             
                                               
                                                                                
                                                                    
                                               
                                                                    
                                                                              
                         
                                                                         
        
                                                                            
                                                
                                                        
                               
                  
                 
                                                            
                                          
                                             
                                                   
                                                                                       

                                                                                             
                                                                                     
                                                            
                                                                                
                                                                      
                               
                                                                                             
                                                           
                                                                 
                        
                                                                                   
                                                         
                                                  
         
      

                                                                                         
                                                  
                                                              
                                                                            
                                                                          
                                                            
                                                                     
                                                                                
                                                                                           
                                       
                                                                      
                                                                                                
                                                                       
                                                                                          
         
                                                                                
                                                              

end FalconerThetaGauge
