module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Ray.Analytic.Analytic
import Ray.Hartogs.Osgood
import Ray.Misc.Bounds
import Ray.Misc.Multilinear
import Ray.Misc.Topology

/-!
## Basics about complex analytic functions
-/

open Complex (exp I log)
open Filter (atTop)
open Metric (ball closedBall sphere isOpen_ball)
open Set (univ)
open scoped Real NNReal ENNReal Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

                                                           
                                                                                        
                                                                               
                                                      
             
                                          
                    
                                                                
                                                                          
                                     
                                                                                    
                                                         
                                                                                                        
                    
                                                                
                                                                          
                                     
                                                                                    
                                                         
                                                                                                        
                                    

                                                         
                                                                                                        
                                                                       
                                               
             
           
                                                                     
                                                  
                                                       
                                                  
                                            

                                                                               
                                                                                        
                  
                                          
                                                                              
             
           
                                                                            
                                                                              
                   
                                                          
                                          
                 
                                                                        
                                                      
             
                                           
                                                                                     
                          
                                                                                
                
                                                          
                                                                 
                           
                                                             
                          
                                     
                                                                    
                                                                                 
               
                         
