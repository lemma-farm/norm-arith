/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic

/-!
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/

namespace MarkovProcess

/-- A strictly increasing family of `n` nonnegative times. -/
abbrev FiniteOrderedTimes (n : ℕ) := Fin n ↪o NNReal

namespace FiniteOrderedTimes

/-- The times after the first one, shifted so that the first time becomes zero. -/
def relativeTail {n : ℕ} (times : FiniteOrderedTimes (n + 1)) : FiniteOrderedTimes n :=
  OrderEmbedding.ofStrictMono (fun i ↦ times i.succ - times 0) fun _ _ hij ↦
    tsub_lt_tsub_right_of_le (times.monotone (Fin.zero_le _))
      (times.strictMono (Fin.strictMono_succ hij))

       
                                                                                     
                                                    
     

                                                                                      
                                                                                           
                                                                 
                                                                           

       
                                                                                         
                                        
     

                                                                                       
                                                                                   
                                                    
                                                        

                                                                                     
       
                                                   
                                          
                                                               
                        
         
                                                            

                                                                        
       
                                                                                               
                        
         
                          

                                                   
       
                                                                                   
                                                                   
                        
         
                                      

                                                                                     
                                                                            
                           
               

       
                                                                                    
                                                     
     

                                                                                      
       
                                                            
                                                                      
     

                                                                                    
       
                                                                 
                                               
                                                                 
     

                                                                          
                                                                                
                
                    

       
                                                                     
                                                                          
     

                                                                     
       
                                                                
                                                                        
     

                                                                                         
       
                                                                                
                                    
                                                                           
     

                                                                                          
                                                              
                                     
                                                            
                                                         

                                                        
def emptyPath (α : Type*) : Fin 0 → α :=
  Fin.elim0

                                        
                                                                             
       
                                                                           
                       

                                                                                    
       
                                                                   
                                                             
                       

end FiniteOrderedTimes

end MarkovProcess
