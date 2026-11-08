module

public import AmbidextrousSofa.Analysis.FiniteVariation

@[expose] public section

/-!
# Actual finite polygon support variations

`upperPolygon` is a bounded intersection of the unit strip, two actual
horizontal endpoint walls, and finitely many upper supporting halfplanes.
The outward variation changes one halfplane parameter. Every unchanged
support remains exact, while a strict point in the moved face gives an
attaining point for the increased support. Such a strict point is derived
from any two distinct points of the face when the other normals are
nonparallel; it is not a separate variational assumption.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

/-- The actual set cut out by a finite upper support system and the fixed box. -/
def upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ) : Set Plane :=
  (Icc l r ×ˢ Icc (0 : ℝ) 1) ∩ ⋂ i, {p | coordDot p (normal i) ≤ height i}

theorem mem_upperPolygon_iff (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ) (p : Plane) :
    p ∈ upperPolygon l r normal height ↔
      p.1 ∈ Icc l r ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ ∀ i, coordDot p (normal i) ≤ height i := by
  simp only [upperPolygon, mem_inter_iff, mem_prod, mem_iInter, mem_ofPred_eq, and_assoc]

theorem isCompact_upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ) :
    IsCompact (upperPolygon l r normal height) :=
  (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_iInter (fun i => isClosed_le (continuous_coordDot_right (normal i)) continuous_const))

                                                                                  
                                                   
                                                                             
                                                        
                                                     
                                                                         
                                                                                  
                                                                               
                                                                                      
                                                                    
                                                                                 
                                                                                       

theorem horizontalProjection_upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i) :
    horizontalProjection (upperPolygon l r normal height) = Icc l r := by
  refine Subset.antisymm ?_ fun x hx => ⟨(x, 0), (mem_upperPolygon_iff _ _ _ _ _).2
    ⟨hx, ⟨le_rfl, zero_le_one⟩, hbaseline x hx⟩, rfl⟩
  rintro x ⟨p, hp, rfl⟩
  exact ((mem_upperPolygon_iff _ _ _ _ _).1 hp).1

                                                                          
                                                                            
                                                                  
                                                                       
                                                     
                                              
                                                             
                                                  
                                 
                                                                                            
                                                                   
                                                                        
                                                              
                                            
                                                                       
                                                                                
                                                                                   
                                                                           
                                                                               
                                                               
                                                                                      
                                
                                        
                                                                           
                                                                     
                                            
                                                                            
                                    
                                     
                                  
                            

                                                                        
                                   
                                                                           
                                         
                                                                          
              
                                 
                                                                                                  
                                                                                          

                                                                            
                                                                        
                                                                            
                         
                                                                                       
                                                             
                                               
                                                     
                        
                                                                      
                                                     
                                                             
                                                                          
                  
                                                                                
                                                                               
                                                                               
                                                                           
                                                                            
                                                                        
                                                                                              
                                        
                                                                
                                                                                       
                              
                                                                                       
                              
                                                                    

                                                                       
                                                                    
                                                                            
                                                                    
                                                           
                                                   
                                                                           
                                                                                  
                                                           
                                                           
                                                                                           
                                                     
                        
                                                                    
                                                  
                                 
                                                                                         
                                                                                                
                 
                                                                                                   
                                                       
                                                                                                    
                                                                                           
                                
                                     
                                                                
                                                      
                                                                   
                                                                                        
                                                                                               
                                               
                                                                    
                                                                      
                                    
                                                                                                  
                                
                                                                      
                                 
                 
                                                   
                                                                 
                                                                                     

end FinitePolygon

end AmbidextrousSofa
