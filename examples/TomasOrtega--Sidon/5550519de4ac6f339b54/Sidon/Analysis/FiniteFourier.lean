module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Indicator

@[expose] public section

/-!
# Finite Fourier sums on the integers

The positive-exponent convention agrees with `fourier` at period one.
-/

noncomputable section

namespace Sidon

/-- The complex indicator of a finite set of integers. -/
def indicatorFinsupp (s : Finset ℤ) : ℤ →₀ ℂ :=
  Finsupp.indicator s fun _ _ => 1

@[simp]
theorem indicatorFinsupp_apply (s : Finset ℤ) (n : ℤ) :
    indicatorFinsupp s n = if n ∈ s then 1 else 0 := by
  simp [indicatorFinsupp, Finsupp.indicator_apply]

@[simp]
theorem support_indicatorFinsupp (s : Finset ℤ) :
    (indicatorFinsupp s).support = s := by
  ext n
  simp only [Finsupp.mem_support_iff, indicatorFinsupp_apply]
  split_ifs <;> simp_all

                                                                                   
                                                        
                                

                                                               
                                                           
                                                                      

       
                                                
                   

       
                                       
                                                          
                                                                          
                                                  

       
                                       
                                                          
                                                                            

       
                                              
                                               
                                        
                                                                                
                                                                

       
                                                   
                                               
                                                                      
                           
     

                                                                                  
                                                                  
                                                              
                                                     

                                                    
                                                              
       
                                                                        

                                         
                                               
      
                                                                   
                     
                                  
                                
               
                                                                                        

                                                                       
                                              
                                                                  

                                            
                                             
                                                          

       
                                                         
                                                          
                                                                                    
                          

       
                                                              
                                                            
      

       
                                                         
                                                          
                   
        
                                                                                    
                            
                            
                                                  
            
                                                               
                                                                                                
                                     
                                                                    

end Sidon
