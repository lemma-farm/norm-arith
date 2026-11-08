import V7.TrialInterfaces

open scoped BigOperators

namespace V7

                                                     
                                              

                                                         
                                                            

                                                                   
                                                 

                                                                              
                          
                                      

                                                                         
                                                     

                                                    
                                                  
                                       
                     
                               
                                                             
                                                 
                   
                                                                     
                                                              
                                                                    
                                                                     
                           
                                         
                                               
                     
                                                             
                                  
                                                      
                                                     
                                                             
                                                                                 

structure BelowPrimalData (p : ℝ) (d n : ℕ) where
  oracle : PairOracle d
  z : Point d
  fstar : ℝ
  u : ℕ → ℝ
  dw : ℕ → ℝ
  s : ℕ → Point d
  v : ℕ → Point d
  x : ℕ → Point d
  trace : List (Observation d)

                                                                
                                                        
                 
                                                      
                                                                  
                                       
                                                                
                                              
          
                                                                             
                                                        
                    
                                              
                                                           
                                                                

                                                                   
                            
                                          
                                                                  
                                         
                                                         
                                                                
                                                      
                                                                  
                                       
                                                                
                                              
           
                                                                             
                                                        
                    
                                              
                                                           
                                                                  
                                                                                        
               
                                     
                                                                                                 
                                     
                             
                                            

                                                        
                                                
                                                                        
                                 
                                                                          

abbrev VectorSeq (d : ℕ) := ℕ → Point d
abbrev ScalarSeq := ℕ → ℝ
abbrev ScalarMatrix := ℕ → ℕ → ℝ

                                                                                    
                                            

                                                     
                                                                    
                                
                        
                                                                               
                                                   
                        
                                                                    
                              
                                            

                                                   
                                                                
                                
                                             
                        
                       
                                                                     
                                                   
                              
                                                                           
                        
             
                                
                                                           
                                                                     

                                                                           

                                                                              
                   
                                                                  
                          

                                               
                                 
                      
                                                       

                                                          
                                        
                                                                     
                                                 
                                                   
                                                       
                
                 
                                 
                                                                        
                                                     
                                        
                                                      
                                     
                                                        

                                                       
                    

                                                          
                                                                   
                                                 
                                                   
                                                                         
                         
                                                                
                                                                
                                     
                                                                       
                                                      
                                     
                                                                       
                                                      
                              
                                                                               
                                                      
                                                 

structure BelowDualData (p : ℝ) (d n : ℕ) where
  oracle : PairOracle d
  u : ScalarSeq
  dw : ScalarSeq
  alpha : ScalarMatrix
  c : ScalarMatrix
  b : ScalarMatrix
  G : VectorSeq d
  q : VectorSeq d
  r : VectorSeq d
  trace : List (Observation d)

                                                            
         
                                                                         
                                       
          
                               
                                                                   
                                                
                               
                                                                      

                                                               
                                                                   
                                                                  
                                          
                                                                         
                                     
                             
                                                
                                                         
                                       
           
                               
                                                                   
                                                
                               
                                                                         
          
                                                                                        
               
                                     
                                                                                              

                                                      
                                                          
                                                                      
                               
                         
                                                      
                                       
                                                        

                                                                           
                                                                           
                                                      
                                                  
                                              
                      
                      
                                   
                                                                     
                                             
                                                 
                                                                  
                                 
                                                       
                                  
                                                                                
                                       

                                                              
                                             
                     
                                                                     
                                                                      

                                                                           
                                                                              
structure BelowTrialWitness (p : ℝ) (d : ℕ) where
  n : ℕ
  completedOne : ℕ
  completedTwo : ℕ
  phaseOne : BelowPrimalData p d n
  phaseTwo : BelowDualData p d n
  phaseTwoCenter : Point d

                                                                
                                                   
                                                                  
                                                            
                                                          
                                  
                                                
                                                                        
                                                     
                                               
                                               
                        
                                                                   
                
                                              
                                                         
                                              
                                                                      
                                                   
                                                   
                                                             
                                                                        
                                                
                                                  
                                                 
                             
                                                  
                                                 
                                        
                                     
                        

                                                                            
               
                                               
                                                     
                                              
                            
                                                             
                                                 
                                                                  
                                                                    
                                                           
                                                    
                                                                          
                                                                              
                          
                                                     
                          
                                                             

end V7
