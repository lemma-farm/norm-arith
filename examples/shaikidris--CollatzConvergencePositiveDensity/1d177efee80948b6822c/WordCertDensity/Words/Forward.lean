/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Words.Physical
import Mathlib.Tactic.Ring

/-!
# Chronological words and their integer affine numerator

`ForwardRealizes` is exactly a positive odd source with its finite list of
actual valuations. The natural numerator is the chronological (W.data)
numerator, distinct from the rational inverse-prefix offset.
-/

@[expose] public section

namespace WordCertDensity

namespace ValuationWord

                                                                                 
                                        
           
                                                             

                                                                 
                                                                                                 
              
                              
               
                                                     
                                    

                                                     
                                                                
                                                
              
                              
               
                           
                                                                                    

                                                                         
                                                       
                               
                                                                                
                  
                                         
                  
                                                                            
                                                              
          

                                                                             
                                                                        
                                 
                                                                            
                                                  

end ValuationWord

/-- A positive odd source realizing exactly the given chronological valuations. -/
def ForwardRealizes (w : ValuationWord) (source : ℕ) : Prop :=
  0 < source ∧ Odd source ∧
    acceleratedValuations source w.length = w.map (fun k : ℕ+ => (k : ℕ))

/-- The finite chronological valuation checks are decidable. -/
instance (w : ValuationWord) (x : ℕ) : Decidable (ForwardRealizes w x) :=
  inferInstanceAs (Decidable (0 < x ∧ Odd x ∧
    acceleratedValuations x w.length = w.map (fun k : ℕ+ => (k : ℕ))))

namespace ForwardRealizes

                                                  
                                                                                       

                                              
                                                                                         

                                                              
                                                                            
                                               

                                                                                  
                                                       
                                                                                  
                                                 
             
                              
                                                                           
                               
                                                                                      
                                          
                           
                                                                           
                    

                                                                 
                                                                            
                                      
                                   
                        
                  
                  
                                                                
                 
                                                                  
                                                                          

                                                                                           
                                                                        
                                                                      
                                 
                                                 
                  
                                                              
                                                                   
                                                                                          
                   
                                                  
                                                                        

                                                                          
                                                                         
                                                                     
                                  

                                                           
                                                                            
                                                             

                                                      
                                                                            
                                                               

                                                                              
                                                                         
                                                                
                                                               
                                 
                                                                     
                  
                                                        
                                                                     
                   
                                           
                                                      
                                            
                                                                                                    
                                                                    
          
                                                                                               
                                                              
                                                                         
                                               

                                                                 
                                                                            
                                                                                          
              
          
                                                                                  
                                                                                 
                             
               
                                                                          
                                                                                            
                                                                
                                       
                                                                        
                                                          
                                                                 
                                                 
                           
           

                                                                                        
                                                                        
                                                                              
                             
                                                
                                                         
                                      
                                             
                  
                                                                      
                                                                                           
                                                             
                                  
                                                                                        
                                           
            
                                                                         
                                            
                                                                       
                                                                    
                                                
                     
                                   
                                                             
                                                             
                                                       
                                        
                                                                           
                                                     
                                                                   
                                                                         
            
                         
                                                
                                                                              
                          
                                                
                                                             
                                              
                                                                     
                                                               
                                      

end ForwardRealizes

                                                                                
                                                                        
                                                                      
                                                                            

end WordCertDensity
