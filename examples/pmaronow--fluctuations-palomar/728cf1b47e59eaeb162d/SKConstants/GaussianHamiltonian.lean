module

public import SKConstants.SKModel
public import SKConstants.GibbsComparison
public import SKConstants.ConcentrationMGF
public import Mathlib

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical

namespace SKConstants

                                                                        
                                                        
                                                       
                                                                     
                                                                  
                                                          
                                
                                                              
                                                                         
               
               
                                          
                                                                
               
                                                               
                                                   
                    
             
          
                                                            
                                      
                                                            
                           
                                                                
                                                          
                         
               
                              

@[expose] def goeSpinHamiltonian {n : ℕ} (sigma : ℝ) (x : Spin n)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  quadraticHamiltonian (GaussianProposal.goeMatrix sigma z) x

                                                                              
                                                      
                                                                              
          
                                             
     

                                                                      
                                               
                                                                
                                          
                                                                                            
           

                                                                  
                                     
                                                                   
                                                              
                                                

                                                  
                                                                
                             
                                      
      

                                                                      
                                   
                                                                                         
                                                              
                                                                    
                                                
                                                                 
      

                                                                        
                                                           
                                                                             
                                                                                  
                                                     
            

                                                                  
                          
                                                             
                                                                        
                                           
                                            
                                                        
                                                        
                                                                   
                                                                          
                                        

                                                             
                          
                                                             
                                                                                      
                                                           
                                  
                                                                   
                                                                                          
         
        
             
      
                                                                               
                                                                           
                                     
                                                            
                                                                            
                                             

end SKConstants
