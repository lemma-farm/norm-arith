import V7.BelowTwoStatements

namespace V7

                                                     
                            

                                                         
                                                                                      

                                                                   
                                            

                                                  
                               
                                                                     
                           
                                         
                                               
                     
                                
                                               
                                                       
                    
                                                             
                                                                    
                                                   

                                                                     
                                                            
                                                   
                                                                   
                                                    
                                                
                                                                
                                                    
                                                        
                                        
                                                                   
                                        
                                                           
                         
                                                       
                                                                   

                                               
                             
                        
                                                                        

                                                            
                                                              
                                   
                                 
                                                   
                                    
                                                                         
                                      
                                                                 
                             

                                                     
                                                                
                                
                                                          

                                                   
                                                                
                                
                                           

                                                          
                                        
                                                                 
                                       
                                                   
                                                       
                
                 
                                 
                                                                        
                                                     
                                        
                                                      
                                     
                                                        

                                                      
                                                                   
                                                              
                                                     
                                                                        
                                                                
                                                                
                                     
                                                                       
                                                      
                                     
                                                                       
                                                      
                              
                                                                               
                                                   
                                                 

structure AbovePrimalPhaseData (p : ℝ) (d n : ℕ) where
  oracle : PairOracle d
  fstar : ℝ
  u : ScalarSeq
  dw : ScalarSeq
  alpha : ScalarMatrix
  c : ScalarMatrix
  b : ScalarMatrix
  s : VectorSeq d
  v : VectorSeq d
  x : VectorSeq d
  trace : List (Observation d)

                                                                          
                                                                                 
                                              
          
                                                                             
                                                        
                    
                                              
                                                           
                                                                

                                                                             
                                                                          
                                                                  
                                                   
                                          
                                                     
                                                                         
                                              
           
                                                                             
                                                        
                    
                                              
                                                           
                                                                  
                                                          
                                   
                                             
                                          
                                                              
                                     
                             
                                            

structure AboveDualPhaseData (p : ℝ) (d n : ℕ) where
  oracle : PairOracle d
  u : ScalarSeq
  dw : ScalarSeq
  alpha : ScalarMatrix
  c : ScalarMatrix
  b : ScalarMatrix
  G : VectorSeq d
  r : VectorSeq d
  q : VectorSeq d
  trace : List (Observation d)

                                                                      
                                                                                 
                                       
          
                               
                                                                   
                                                
                               
                                                                      

                                                                         
                                                                        
                                                                  
                                          
                                     
                             
                                               
                                                 
                                       
          
                               
                                                                   
                                                
                               
                                                                        
                                                          
                                   
                                             
                                              

structure AboveTrialWitness (p : ℝ) (d : ℕ) where
  nF : ℕ
  nD : ℕ
  completedF : ℕ
  completedD : ℕ
  etaF : ℝ
  etaD : ℝ
  gammaF : ℝ
  gammaD : ℝ
  phaseOne : AbovePrimalPhaseData p d nF
  phaseTwo : AboveDualPhaseData p d nD
  phaseTwoCenter : Point d

                                                                
                                                   
                                                                  
                            
                                                         
                                                         
                  
                                                                
                                       
                                       
              
                                                          
                                                       
              
                                                          
                                                       
                                                          
                                       
                                                 
                                                                        
                                                          
                                             
                                            
                      
                                                                   
                
                                            
                                                         
                                            
                                                                      
                                                   
                                                 
                                                           
                                                                    
                                              
                                                  
                                               
                             
                                                   
                                                 
                                        
                                     
                            

                                                                     
                                         
                                               
                              
                      
                                                             
                                                    
                                     
                                                 
                                                                  
                                                                    
                                                           
                                                    
                                                                          
                                                                              
                          
                                          

end V7
