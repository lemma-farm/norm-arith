/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The binary-unit projection argument is adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The source LICENSE and
NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
The recursive offsets use the local word algebra and reversed numerator.
-/
module

public import WordCertDensity.Words.Forward
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Dyadic offsets in ternary residue groups

Binary denominators are units modulo every power of three, including the
one-point group at level zero. A recursive residue offset is connected to the
rational inverse offset by their common integral numerator and binary denominator.
No generic rational cast into a ternary residue ring is used.
-/

@[expose] public section

namespace WordCertDensity

namespace Reference

                                                       
                                                      
                                                                     

                                                       
                                                                  
                

                                                            
                                                           
                      

                                               
                                                                        
                      

                                                         
                                       
                                                                         
                               

                                                                     
                                        
                                                        
                                                                     
                               

                                                                 
                                             
                                                        
                      
                                 

                                                              
noncomputable def project {m n : ℕ} (h : m ≤ n) :
    ZMod (3 ^ n) →+* ZMod (3 ^ m) :=
  ZMod.castHom (Nat.pow_dvd_pow 3 h) (ZMod (3 ^ m))

                                                           
                                                       
                                                           
                                  
                                                 

                                                                          
                                                             
                                                           
                                                               
                   
                                                                            
                                 
                                 
                                                                         
                                        
                           

end Reference

namespace ValuationWord

                                                                      
                                                                      
           
                                                                       

                                                     
                                                                         

                                                 
                                                                                  
                                                                            
                             

                                                                                       
                                                            
                                                  
                                                                         
                               
                  
                                      
                  
                                                                       
                                                                                            
          

                                                                             
                                                                         
                                                                     
                  
                               
                  
                                                          
                                            
                                                              
                                      

                                                                                             
                                                                 
                                                    
                                                                                       
                  
                               
                  
                                                                  
                                               
                                        
                                                                            
                                                                   
                               
                                  
                 
                                                                            
                                                
            
               
                                                                                         
                                                                 
          

                                                                 
                                                                      
                                                                           
                           
                                               
                                            
                                             
                         
      

                                                                            
                                                        
                                                        
                           
        
                                                                      
                                  
                                       
                                                                                 
                                                    

                                                                           
                                                                              
                                                                              
                                                

                                                                                  
                                                        
                                                                   
                  
                                                 
                  
                                                                                          
                                                     
               
                  
                
          

                                                                                      
                                                                       
                                                           
                                                       
                  
                                                 
                  
                                                                                                 
                                                                                  
               
                                                                  
                               
                                                            

end ValuationWord

end WordCertDensity
