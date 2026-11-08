module
public import Mathlib.Algebra.Order.Chebyshev
public import GuthMaynard.NativeSource.GuthMaynard.LargeValuesMatrix

@[expose] public section

open Finset
open scoped BigOperators

namespace GuthMaynard.NativeMoment

/-!
# Sixth-moment trace dispersion

The first lemma is the nonnegativity assertion needed for the sixth root in
Guth--Maynard Lemma 4.2.  It is a direct finite Jensen inequality, proved here
over the reals before the spectral specialization.
-/

                                                                 
                                                  
                            
                                                     
                                             
                                                                    
                                         
              
                                                             
                              
              
        
                 
                        
                      
                                     

                                                                         
                                  
theorem sixthMoment_tail_lower {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (j : ι) :
    (∑ i ∈ s.erase j, x i ^ 2) ^ 3 ≤
      (s.card : ℝ) ^ 2 * ∑ i ∈ s.erase j, x i ^ 6 := by
  have hJensen := pow_sum_le_card_mul_sum_pow
    (s := s.erase j) (f := fun i => x i ^ 2)
      (fun i hi => sq_nonneg (x i)) 2
  have hcard : ((s.erase j).card : ℝ) ^ 2 ≤ (s.card : ℝ) ^ 2 := by
    have hbase : ((s.erase j).card : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast (Finset.card_erase_le (s := s) (a := j))
    exact pow_le_pow_left₀ (by positivity) hbase 2
  have hsum : 0 ≤ ∑ i ∈ s.erase j, x i ^ 6 := by positivity
  calc
    (∑ i ∈ s.erase j, x i ^ 2) ^ 3
        ≤ ((s.erase j).card : ℝ) ^ 2 *
          ∑ i ∈ s.erase j, (x i ^ 2) ^ 3 := hJensen
    _ = ((s.erase j).card : ℝ) ^ 2 * ∑ i ∈ s.erase j, x i ^ 6 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (s.card : ℝ) ^ 2 * ∑ i ∈ s.erase j, x i ^ 6 :=
      mul_le_mul_of_nonneg_right hcard hsum

                                                                           
                                                                          
       
                                                                            
                                                     
                 
                                
                                                   
                                                           
                     
                               
                               
                      
                                       
                                       
                                
                                 
                       
             
                                         
                                        
                                             
                                             
                                             
                                             
                       
                      
                                              
                                
                   
                                                      
                                      
                
                                                      
                                                     
                                      
                                                           
                                   
                                                
                                                    
                   
          
                                        
                                        
                                          
                                                      
                                                         
                            
                     
                                                                
                         
               
                                               
                                                        
                                                      
                                                         
               
                                         
                                             
                                                  
                                                    
                                                                            
                      
            
              
               
                                                                
               
                                                   
               
                
                                       
                                               
          
                                                          
                                                   
                                                                           
                                         

                                                                     
                                                     
                                                                      
                         
                                 
                                           
                                            
                                                                    
                                  
        
                                                                
                       
      
                                    
                                                
                                         
                                          

                                                             
                                                                 
                             
                                 
                                         
                                               
                                                
                                                                     
                                  
        
                                                                
                           
      
                                        
                                                      
                                          
                                 
                                                   
              

                                                                   
                                                                  
                                                      
                          
         
                               
                                                                  
                                                                 
                                   
                                             
                                                
                                 
                                                                           
                       
                                              
                       
                                             
                                                              
                              
                                                   
                                        
          
                             
                                                                 
                                                            
                                
                                                                 
                                                        
                                                              
                                
            
                                    
          
                             
                                                                 
                                                         
                                                             
                                                              
                                
            

                                                             
                                                                           
                                                    
                                                      
                                                                    
                                            
         
                             
                                                                       
                         
                                                                       
                              
                            
                                                                       
                                   
                                         
                                                         
                                      
                                                                  
                                         
                                                                
           
                                               
                                        
                                                                    
           
                                                  
                                                                     
                                                          
                                 

                                                                  
                           
                                                  
                                                                    
                                        
                          
                                                                     
                       
                                                                     
                                           
                          
                                                                 
                                           
                                         
                                                         
                                  
              
                                                   
                                                                            
                                         
                                                                
           
                                               
                                        
                                                                    
           
                                                  
                                                       
                                 

                                                                     
                   
                                                 
                                                                        
                                     
                          
                                                                     
                       
                                                                     
                                           
                          
                                                                 
                                           
                                                                              
                                                                          

end GuthMaynard.NativeMoment
