module

public import SKConstants.GaussianProposal
public import Mathlib
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.GaussianProposal

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

                                                                   
                                                       
                                                                                 
                                                                                   
                                                   
                                                                          
               
                                   
         
          
                                                                                   

variable [LinearOrder ι]

abbrev UpperPair (ι : Type*) [LinearOrder ι] := {p : ι × ι // p.1 ≤ p.2}

                                                                          
                                         
                                                 

                                                             
                                                                     
                         
                                                           
                                  
                                                                            
                  
                   
                             
                 
                      
           
                                                            
                                                         
                    
               
                                        
                                                          
                    
                                                          
                                                
               
                       
                    
                            
                                 
                                                                     
                                                                       
              

                                                                
                                                                       
                                                                        
                                                  
                                                               
                                              
               
                                                                
                                  
                                                              

                                                      
                                                                     
                       
                                                                
                                                                    
                                            
                                                                       
                                                                                        
                                 
                                                                                  
                              
                                                                        
                                                                  
                                              
                                                  
        
                                                                                  
                                                                         
                 
                   

                                  
                                                              
                                                                       
                                                                             
                                                       
                                                       
                                               
                                                                        
                                       
                                                                               
                                          
                                                                  
                                                        
      
                                                            
                                             
               
         
          
                                          

end SKConstants.GaussianProposal
