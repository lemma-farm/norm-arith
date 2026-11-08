module

public import AmbidextrousSofa.Analysis.AxisVariation

@[expose] public section

/-!
# Actual finite support circumscription

Intersecting the sampled support halfplanes with the actual projection
box produces a larger downward cap. Every sampled support remains exact,
and the actual projection is unchanged. Consequently the sampled physical
barrier and any sampled support penalty remain unchanged while the charged
exterior roof can only increase. These are the recovery competitors for
finite selected spatial maximizers.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

def circumscription (U : Set Plane) (normal : ι → Plane) : Set Plane :=
  upperPolygon (horizontalLeft U) (horizontalRight U) normal (fun i => support U (normal i))

theorem circumscription_baseline {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) :
    ∀ x ∈ Icc (horizontalLeft U) (horizontalRight U), ∀ i,
      coordDot (x, 0) (normal i) ≤ support U (normal i) := fun x hx i => by
  obtain ⟨p, hp, rfl⟩ := hU.horizontalProjection_eq_Icc.ge hx
  exact coordDot_le_support hU.isCompact (hU.baseline_mem hp) (normal i)

theorem eqOn_roofEnvelope_of_circumscription [Fintype ι] {U : Set Plane}
    (hU : IsDownwardCap U) (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hpoly : U = circumscription U normal) :
    EqOn (roofEnvelope normal (fun i => support U (normal i))) (capRoof U)
      (Icc (horizontalLeft U) (horizontalRight U)) := fun _ hx =>
  ((congrArg (capRoof · _) hpoly).trans
    (capRoof_upperPolygon _ _ normal _ hnormal (circumscription_baseline hU normal) hx)).symm

                                                                     
                                                                      
                                      
                                                    
                                                                             

                                                                            
                                                            
                                               
                                    
                                                                
                                                

                                                                                   
                          
                                                                                  
                                     
                                                                                      

                                                                      
                                  
                                                                              
                                               
                                                                             
                                                   
                                                                      

                                                                                         
                                                  
                                                                    
                                              
                                                                                            

                                                                      
                                                                         
                                                                         
                                                                          
                                                             
            
                                                              
                                                                    
                                                                     
                                                                                    

                                                                       
                                                               
                                                                                    
                                                          
                                                    
                                                  
                                                                                 
                                                            
                                                                        
                                                                              
                                                                   
                                                                           
                                                    
                                                                                       
                                                                
                                                                           
                                                                     
                                                                     
                                                           

end FinitePolygon

end AmbidextrousSofa
