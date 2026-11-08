/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.MaxPrinciple
public import RegularityStructures.PDE.Nonlin
public import RegularityStructures.PDE.Jet
public import RegularityStructures.PDE.DuhamelTime
public import RegularityStructures.PDE.SmoothDense
public import RegularityStructures.PDE.HeatOpBridge
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# The semigroup property of the heat operator

`heatOp b (heatOp a g) = heatOp (a + b) g` for `a, b ≥ 0` and every `g ∈ C(T³, E)`
(`heatOp_heatOp`).

For smooth scalar `g` both sides solve the heat equation in `b` with the same initial value, so
their difference vanishes by the maximum principle (`eq_zero_of_heat_equation`). The general case
follows by density of smooth functions (Stone–Weierstrass) and the contraction property, and for
vector-valued `g` by testing against continuous linear functionals.
-/

open scoped ContDiff

public section

open Set Filter Topology

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasTorusDeriv.sub {g h : C(Torus3, E)} {Dg Dh : C(Torus3, Fin 3 → E)}
    (hg : HasTorusDeriv g Dg) (hh : HasTorusDeriv h Dh) : HasTorusDeriv (g - h) (Dg - Dh) := by
  simpa [sub_eq_add_neg] using hg.add hh.neg

                                     
                                                                                 
         
                                   

                                                                                          
               
                                                                                       
                                                                                       
                                                     
                                                                         
                                                                                    
                                       
                                                                   
              
                                                                                   
                                                  
                                                                    
                                                                                               
                                                                           
                                                 
                                 
                                                          
                                                                            
                       
                                                                                      
                       
                                    
                
                    
                                                                          
            
              
                                            
                                               
                                                   
                                        
          

                                                    
                                                                                       
                                                                                       
                                                     
                                                                         
                                                                                    
                                
            
       
                                                               
                                                                                 
                                                                               
                                 
                     
                                  
                                                                 
                                                     
                                     
                                           
                                      
          

                                                                      
                                                           
                                                                            

                                                               
                                                            
                                                                                

                                                          
                                                                                               
                                                                                              
                                                                                         
                                          
                                                                   
                                                                                     
                                                                                             
                                                               
                                                      
                                                       
                                                                                          
                           
                                                                      
                                             
                                                        
                                                          
                                                               
                                                                        
                                                
                                                            
                                                 
                                                             
                     
                                                
                                                                 
                                        
                                                                     
                                            
                              
                                
                                                                          
                                                               
                             
                 

end RegularityStructures.PDE

end

public section

open Set Filter Topology

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

                                                              
                                                                                   
                                                  
                                        
                                               
                                                           
                                              
                                                 
                                                                    
                                                    
               
                                                                                   
                            
                                                                                         
                            

                                                                       
                                                                           
                                                                       
       
                                                                      
                                                  
                                                                
                                                                            
         

                                                                                         
                                                       
                                                                                   
                                                                                   
                                                                            
                              

end RegularityStructures.PDE

end
