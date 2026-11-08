import V7.PositiveModel

namespace V7

                                                          
                          
                                                                       

                                                                   
                             
                                                                         
                                          

                                                                 
                             
                                                                        
                        

                                                                      
                                                                     
                             
                               
                                                                            
                       

                                                                             
                               
                                                                              
                                                                                

                                                                      
                             
                                   
                                                      

inductive ObservableGuardKind where
  | upperModel | gradient | cocoercivity | interpolation | terminalDescent
  deriving DecidableEq

structure ObservableGuardFailure (d : ℕ) where
  kind : ObservableGuardKind
  x : Point d
  y : Point d

                                                              
                                            
                   
                                                       
                                                   
                                                           
                                                                    
                                                               

end V7
