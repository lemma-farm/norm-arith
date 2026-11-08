/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FalconerThetaGauge.RegularMeasureEntryBudget
public import Mathlib
/-!
# Actual marked blocks of depths

The interval `{0,…,N}` is partitioned into consecutive blocks of `q` depths.
One fixed minimizing depth is marked in every actual block.
-/

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace FalconerThetaGauge

/-- A fixed minimizing element of an actual nonempty finite set of depths. -/
def finiteProfileMinimizer (A : ℕ → ℝ) (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then (Finset.exists_mem_eq_inf' h A).choose else 0

                                                                                 
                                        
                                              
                                                      

                                                                              
                                                                     
                                              
                                                     
                           

/-- The first depth in block `b`. -/
def profileBlockStart (q b : ℕ) : ℕ := b * q

/-- The last depth in block `b`, truncating the last block at `N`. -/
def profileBlockEnd (q N b : ℕ) : ℕ := min ((b + 1) * q - 1) N

/-- An actual finite block of consecutive depths. -/
def profileDepthBlock (q N b : ℕ) : Finset ℕ :=
  Finset.Icc (profileBlockStart q b) (profileBlockEnd q N b)

/-- The minimizing depth marked in the actual block. -/
def profileMarkedDepth (A : ℕ → ℝ) (q N b : ℕ) : ℕ :=
  finiteProfileMinimizer A (profileDepthBlock q N b)

                                                                  
                                                           
                                                             

                                                                             
               
                                  

                                                                             
               
                                                
                                                          

                                                                              
                                            
                             
                                                               
                               
                                          
                               
       

                                                               
                                                                              
                                           
                                     
                                      
                            
                          
                                          
       

                                                                     
                                                                  
                                                        
                                           
                                     
                                  
                                            
                                                
         
                                                                                  
                                                 

                                                       
                                   
                                                          
                                                                            
                                                                 
                                                                               

                                                      
                                                                         
                                                                      

                                                                   
                                                                                
                                                             

                                                           
                                                   
                                                       

                                                                                   
                                                                             
                                                                          
                                      
                                                     
                                                             
                                                
                                                              
                           
                                                                              
                               
                       
                                                                         
                         
              
                                                                      
                                              
                                                                   
                        
          

end FalconerThetaGauge
