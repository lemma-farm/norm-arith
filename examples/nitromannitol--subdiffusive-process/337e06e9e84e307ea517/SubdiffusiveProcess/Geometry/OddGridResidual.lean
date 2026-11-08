module

public import SubdiffusiveProcess.Geometry.OddGridPartition

@[expose] public section

/-!
# The unresolved volume on a centered odd grid

Unresolved labels are precisely those whose actual open cells meet at least
one selected coordinate midplane. Count the middle-coordinate fibers and
use their actual cell volumes. No independence, coefficient estimate, or
assumed geometric remainder enters this argument.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- Labels whose `i`th coordinate is the middle child. -/
def oddGridPlaneCells (m : ℕ) (i : Fin d) : Finset (OddGridIndex d m) :=
  Finset.univ.filter (fun k => (k i).val = m)

/-- Cells unresolved by the selected coordinate midplanes. -/
def oddGridUnresolved (m : ℕ) (I : Finset (Fin d)) : Finset (OddGridIndex d m) :=
  I.biUnion (oddGridPlaneCells m)

                                                                  
                                                                                 
                                                         
                                        
                                                                                  
                                                                      
                                                                                 

                                                                          
                                                    
                                                              
                                            
                                                        
                                                                    
                                                                    
                                                    

                                                                                   
                                                                
                                                                       
                          
                                    
                                                                                          

                                                                                         
                                                     
                                                                                  
                                             
                                                              
                                                    
                                                
                                                      
                                                
                                   
                                                           
                                          
      
                                                
                                                                
                                       
                                            
                                         
                                                                         
                                                      
                                      
                                                   
               
                      
                

                                                                            
                                                         
                                                                                  
                                             
                                                              
                                                                      
                                              
                                                        
      
                                                   
                                                  
                                                   

end SubdiffusiveProcess
