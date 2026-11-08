module

public import SquaresInCircles.Common.Separation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Arcs and the angular budget

Directions are `Real.Angle = AddCircle (2π)`, whose Haar measure has total mass
`2π`; a closed metric ball of radius `w ≤ π` has mass `2w`. An `OpenArc` is an
arc of a circle about the disk centre that lies in a planar region. Arcs in
pairwise disjoint regions have half-widths of total at most `π`: shrink every
arc by the same factor below 1 and measure the closed arcs
(`open_arc_budget`). The centres of two such arcs are at least the sum of their
half-widths apart (`OpenArc.centers_separated`), and three directions have
perimeter at most `2π`, which bounds the third distance of three arcs.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set
open Set
namespace SquaresInCircles

local instance : Fact (0 < (2*Real.pi : ℝ)) := ⟨by positivity⟩

def circlePoint (o : Point) (r : ℝ) (θ : Direction) : Point :=
  (o.1+r*θ.cos, o.2+r*θ.sin)

                                                             
                                            
                                                                     
                                                                                   
                                                          

                                                                        
                                  

                                                                                 
                            
      

/-- A certified open angular interval contained in an actual planar region. -/
structure OpenArc (o : Point) (r : ℝ) (U : Set Point) where
  center : Direction
  halfWidth : ℝ
  positive : 0 < halfWidth
  atMostPi : halfWidth ≤ Real.pi
  inside : ∀ θ, dist θ center < halfWidth → circlePoint o r θ ∈ U

                                                                              
                                                                               
                                                          
                                                                                     
                                       
                                       
                                                                         
                            
                                                                                           
                                                                              
                                            
                                                                                             
                                                                          
                                                
                                                                         
                                                                         
          

                                                                                 
                                                            
                                                                           
                                                                                    
                                        
                                               
                                                              
                                            
                     
                                                   
                                                                                
                                                                                     
                                                                                             

                                                                             
                               
                                                      
                                                        
                                                     
                                            
                                                          
                      
                                                                                               
                                                    
                                                                      
                                 
                                          

                                                                       
                                                                             
                                                                         
                                                    
                                                                       
                       
                                             
                      
                         
                         
              
              
                                                               
                                                                      
                                       
                                        
                                     
                                                         
                             
                                                                       
                                     
           
                   

                                                                   
                                            
                                                        
                            
         

                                                                     
                     
                              

                                                                           
                                                                            
                                     
                                                                     
                                                                  
                                                          
              
                
                                     
                                                                                    
                                          
                                                
                                          
                                                                                
                                                                               
                                                                                       
                         
        
                                                                                              
                                         
                                                
                              
             
                        
                                                
                                                       
                          

                                                             
                                         
                                  
                                                                  
                                                  
                                                                          
                         
            
                                                                  
                                                  
                                                                          
                         
            

                                                                                          
                                                        
                                                    
                       
                       
                                                   
                                                   
                                                     
                                                     
                                         
                                       
                                  
                                                       
                                             
                        
                                
                                           
                                                             
                                                   
              
                                        
                                          
                                              
                                                            

                                                                                
                                                                           
                                                               
                                                                    
                                                      
                              
                                                             
                                       
                                       
                                       
                                                                    
                                        
          

                                                               
                                                               
                                                                    
                                                       
                                                   
                    

                                                                              
                                                                 
                              
                                            
              

                                                                
                                                                                    
          

end SquaresInCircles
