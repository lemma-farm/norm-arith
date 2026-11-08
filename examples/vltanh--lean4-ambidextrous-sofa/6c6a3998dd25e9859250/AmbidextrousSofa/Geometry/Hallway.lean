module

public import AmbidextrousSofa.Geometry.Support
public import AmbidextrousSofa.Geometry.HullCompact
public import AmbidextrousSofa.Geometry.Motions

@[expose] public section

/-!
# Actual hallway constraints and support tightening

The inner corner is excluded by a disjunction, while both outer walls must
hold. Tightening the two support offsets preserves every original retained
point; it does not assert that the entire convex hull fits the hallway.
The actual outgoing strip is tightened separately and remains a whole-body
condition. These are the pointwise geometric steps GA.1--GA.2 and GA.5.
-/

noncomputable section

namespace AmbidextrousSofa

def companionNormal (θ : ℝ) : Plane := (-Real.sin θ, Real.cos θ)

                                                                     
                                  

                                               
                                                          
                                                                                   

                                                                         
                                                       
                                                         
                                                            
                                                                              
                                                                                 
                                                                     
                                         
                                              
                                                                   
                                 
                                                                             
                
                                                       

/-- A two-wall L-hallway in a prescribed frame. -/
def frameHall (u v : Plane) (a b : ℝ) : Set Plane :=
  {p | coordDot p u ≤ a + 1 ∧ coordDot p v ≤ b + 1 ∧
    (a ≤ coordDot p u ∨ b ≤ coordDot p v)}

/-- The frame hallway with both outer walls at the actual support values. -/
def canonicalHall (K : Set Plane) (u v : Plane) : Set Plane :=
  frameHall u v (support K u - 1) (support K v - 1)

                                                           
                             
                                                               
                                                                               
                                                                         

                                                                                           
                                                   
                                                                    
                                                                 
                                                                            
                                                                                  
                                                                                    
            
                                                                              
                                                                  
                                                                 

                                                                 
                                                                     
                                                            
                                                                       

                                                                            
                              
                                                  
                                                  
                    
                                                                          
                                                                                       

                                                                            
                                                          
                                   
                                                                          
                                                                                
                                                                                             
                                             
       

                                                                                  
                                          
                                                                  
                                                                                                  

                                                                                       
           
                                                                            
                                                                       
                               
                                                                                
                                                            
                                                          
                                                         
                                                                

                                                                                            
                                                                                
                                                               
                                                                             
                                                                 
                                          
                                                                                

                                                                     
                                                                            
                                                                 
                                                                          
                                                                                       
                                                            
                                                                                             
                                          
                          

                                                                     
                                                                               
                                                               
                                                 
                                                
                                                   
                                   
                                                                              

end AmbidextrousSofa
