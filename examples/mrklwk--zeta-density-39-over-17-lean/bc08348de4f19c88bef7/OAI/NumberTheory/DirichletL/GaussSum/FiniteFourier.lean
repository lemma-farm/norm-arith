module
public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinIdeals
public import OAI.NumberTheory.DirichletL.Mellin.LogProfiles
public import Mathlib
@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

namespace ShortDraftFiniteGaussFourier
open scoped Classical
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]

                                                           
                          
                                
                                                       
           
                     
           
                                                            
                                          
                                                   
                                                   
                                                          
                                                                                            

                               
                           
                                                           
                                                         
                                        
                                                        
                                                                            
           
      
                                                        
                                                   
                                   
                                                        
                                                                              
                                 
               
                                                    

end ShortDraftFiniteGaussFourier

namespace PoissonChildCRT
open scoped Classical

variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)

                                                           
                                                                    
                                   
                                            
                                                         
                                  
                                    
        
                                                            
                                           
                 
                                                            
             

                                                 
                       
                                                          
                                                             
                                      
                                                    
                                        
                                   
      

                                                      

                              
                                              
           
                  
                                  
                                                                 
                                                                 
                                                        
            
                                                         
                 
                                                                           
                                    
                                    
                                             
          
                                             
          

                                  
                                                    
                           
                   
                                          
              
                                                         
                                                             
                       

                                      
                                                            
                           
                   
                                          
              
                                                         
                                                             
                       

                                                  
                                                 
                                
                                                             
                                                              
                             
                                       
                                                       
                         
                                                        
                                          
                              
        
            
                          
                                                             
                                                                
                                                             
                                                                    
        
                                                                        
                                                                
                                             
                                                
                                                                                 
                                                       
                                                                     

                                     
                                                     
                                       
                                                 
                   
                                   
                                                                     
                                            
                                     
                   
                            
                                         
                                                           
                            
            
                                                                       

end PoissonChildCRT

namespace PoissonFirstLocal
open scoped Classical

                                            
                                               
                                                                      
                                         
                                                                                       
                                         
                                                                                       
                                        
                                          
                                                                       
                                             
                                                           
                                             
                                                           

                                                 
                                                                                 
                                                                                     
                                                      

                                                      

                                      
                                              
           
                  
                                  
                                                                 
                                                                 
                                                        
            
                                                         
                 
                                                                           
                                    
                                    
                                             
          
                                             
          

                                                    
                                             
                         
                                                      
                                                                         
                            

                                      
                                             
                                                                     

                                                          
                                                         
                                                                                
                         
                             
                                       
                                                 
                             
               
                                                         
                                     
                                                     
                                                               
                                                                           
                                
                                                            
                                             
              
                                              
                                                         
                                                                  
                        
                                              
                                                         
                                                                  
                        
                                          
              
                                                           
                                                   
                                                     

                                                               
                    
                                     
                                               
           
                                            
                 
                        
                                                   

                                                  
                                                   
           
                                            
                        
                        
                   
                                            

                                    
                                
                                
                                                       
                                                                 
                                                                                     
                                                                          
           
      
                                                                 
                                                                  
                                     
                    
                                                                              
                                                           
                                   
                                                                              
                               
                                   
               
                                        

                              
                                              
                                             
                                      
                                            
                           
                                                 
                 
                 
                                                           
                                                             
                 
                                             
                    
                                     
                                          
              
                                                         
                                                             
             

                                   
                                
                                
                                                          
                                                                       
              
                                                                
                                                                     
                                                                 
                                                                                     
                     
                                                                 
                                                 

                                        
                                  
                                
                                      
                                         
                   
                                                                        
                   
                                                                                        
                                                                             
                            
            
                                                                         

                                       
                                  
                                
                                      
                                       
              
                                                                       
              
                                                                
                                                                     
                   
                                                                        
                   
                                                                                        
                        
                            
            
                                                                                   

end PoissonFirstLocal

open Finset Complex

namespace ActualCubicChar

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]

omit [IsDomain R] in
theorem cubic_roots_surjective (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    Function.Surjective (restrictRootsOfUnity ρ 3) := by
  intro η
  have hη : ((η : Fˣ) : F) ^ 3 = 1 := by
    exact (mem_rootsOfUnity' 3 (η : Fˣ)).mp η.property
  obtain ⟨j, _, hj⟩ := hζF.eq_pow_of_pow_eq_one hη
  let z : rootsOfUnity 3 R := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
  refine ⟨z ^ j, ?_⟩
  apply rootsOfUnity.coe_injective
  change ρ (ζ ^ j) = ((η : Fˣ) : F)
  rw [map_pow]
  exact hj

noncomputable def cubic_roots_equiv (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    rootsOfUnity 3 R ≃* rootsOfUnity 3 F := by
  classical
  letI : Fintype (rootsOfUnity 3 R) := Fintype.ofFinite _
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  apply MulEquiv.ofBijective (restrictRootsOfUnity ρ 3)
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · exact cubic_roots_surjective ρ ζ hζ hζF
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hζ.card_rootsOfUnity, hζF.card_rootsOfUnity]

variable [Fintype F]

                                             
                                       
                                            
           
                                   
                                       
                      
                          
            
                                                  
                                          
         
      
                                                         
                                              
                                          
                         
                                
               
                           
          
                                                                     

def euler_to_roots (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    Fˣ →* rootsOfUnity 3 F where
  toFun u := rootsOfUnity.mkOfPowEq ((u : F) ^ m) (by
    rw [← pow_mul, ← hq]
    exact FiniteField.pow_card_sub_one_eq_one (u : F) u.ne_zero)
  map_one' := by
    apply rootsOfUnity.coe_injective
    simp
  map_mul' u v := by
    apply rootsOfUnity.coe_injective
    simp [mul_pow]

noncomputable def cubicResidueChar (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) : MulChar F R :=
  MulChar.ofUnitHom <|
    (Subgroup.subtype _).comp <|
      (cubic_roots_equiv ρ ζ hζ hζF).symm.toMonoidHom.comp
        (euler_to_roots m hq)

                                                          
                                                              
                                                        
                                                                    
                                       
                                                                           
                                                                             
               
                                                       
                                                                      
                                                                             
                                                                  
                                                                             
                      
           

                                                        
                                                              
                                               
                                                  
                   
         
                                                       
                          
                                                                           
                             
                                                               
                                 
                                                    

end ActualCubicChar

namespace ActualEisensteinCubic

section

open NumberField

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

def omega : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

def lambda : O := omega - 1

noncomputable instance quotientFintype (P : Ideal O) [P.IsMaximal] :
    Fintype (O ⧸ P) := Fintype.ofFinite _

noncomputable instance quotientField (P : Ideal O) [P.IsMaximal] :
    Field (O ⧸ P) := Ideal.Quotient.field P

theorem omega_primitive : IsPrimitiveRoot omega 3 := by
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot

                                    

                                                                            
                                             
                                                                     
                                                             
                                                
                             
                         

                                             
                                          

                                                                              
                                               
                                               

                                        
                                              
                                              
                                             

theorem omega_reduced_primitive (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hpow : (ρ omega) ^ 3 = 1 := by
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hne : ρ omega ≠ 1 := by
    intro he
    apply hgood
    have hz : ρ (omega - 1) = 0 := by rw [map_sub, he, map_one, sub_self]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hz
  apply IsPrimitiveRoot.mk_of_lt _ (by decide) hpow
  intro l hl0 hl3
  have hl : l = 1 ∨ l = 2 := by omega
  rcases hl with rfl | rfl
  · simpa using hne
  · intro h2
    apply hne
    calc
      ρ omega = (ρ omega) ^ 2 * ρ omega := by rw [h2, one_mul]
      _ = (ρ omega) ^ 3 := by ring
      _ = 1 := hpow

theorem card_sub_one_div_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    3 ∣ Nat.card (O ⧸ P) - 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let hζ := omega_reduced_primitive P hgood
  let u : (O ⧸ P)ˣ := (hζ.isUnit (by decide)).unit
  have hu : IsPrimitiveRoot u 3 := hζ.isUnit_unit (by decide)
  have h := orderOf_dvd_natCard u
  rw [← hu.eq_orderOf] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using h

noncomputable def cubicChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  exact ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq

                                                    
                                      
                                                 
                                            
           
                                               
                                             
                                         
                                               
                                                                       
                                           
                       
                                                                
         
                               
                              
                                                                   
                                                                         
                     
           
                                                                     
                                                                       
                                
                                                        
                                                                      
             
                                                      
                                                 
                                              

                                                       
                                                          
           
                                               
                                             
                                         
                                               
                                                                       
                                           
                                                                     
                                                                  
                                                  
                                               
                                          

                                                    
                                                      
           
                                               
                                             
                                         
                                               
                                                                       
                                           
                       
                                                                
         
          
                                             
           
                   
                                                   
                                                 
                                                        
                                             
                                                                    
                 
                                   
       

                                                   
                                                                
                                                
                                                           
                                                             
                                                                            
            

                                                       
                          
                                   
                                                         
                                 
           
                                               
                                             
                           
                                                         
                                                                 
                                                                                     
                      

                                                         
                          
                                                               
           
                                               
                                             
                                         
                                               
                                                                       
                                           
                                                  
                                                                
         
                                           
                         
                                             
                                      
                                                  

                                                       
                          
                                                       
                                                             
                                    
           
                                               
                                             
                                   
                                            
                                                  
                         
                                                                       
                    
                                                                     
                                
                                                            
           
                                                   
                         
                                       
                                      
                  
                            
                    
                                                              
                                                   
                                                                               
                                                           
                                    
                                                               
                                                              
                            
                                                                
                              
                                                                   

noncomputable def conjK : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

noncomputable def conjO : O ≃+* O :=
  RingOfIntegers.mapRingEquiv conjK.toRingEquiv

theorem conjO_omega : conjO omega = omega ^ 2 := by
  apply RingOfIntegers.coe_injective
  change conjK (IsCyclotomicExtension.zeta 3 ℚ K) =
    (IsCyclotomicExtension.zeta 3 ℚ K) ^ 2
  exact IsCyclotomicExtension.fromZetaAut_spec
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

                                                           
                         
                                                              
                                 
                       
                   

                                                         
                                      
                                                               
           
                                               
                            
                               
                                   
                                                                     
                                     
                     
           
                                                   
                                
                                                                  
                                                         
                                    

                                                    
                          
                                                               
                                                                 
           
                         
                                                  
     

                                                        
                          
                                                       
                                                                 
                                    
                               
                                   

end

noncomputable def quadraticCharO (P : Ideal O) [P.IsMaximal] :
    MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  exact (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O)

                                                       
                                  
           
                                               
                                             
                                                                          
                                                                                

noncomputable def sexticChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O :=
  cubicChar P hgood ^ 2 * quadraticCharO P

                                                     
                          
                                                
                                               
                                    
                                        
                                
                            
                           
                                       
        
                                                                   
                               
                                         
                                    
                                         
        
                                                                             
                                    
                           
      
                                                       
                               

                                                             
                                                          
                                                    
                                                                             
           
                                                            
                                                                                         
                        
                                              
                                   
                                                          
                                     
                               
        
                                                                   
                          
                                   
                                                                
                                                       
                                                                 
                          
                                        

                                                     
                                               
                               
                                                               
                                        
                             
                                                                       
                                                                          
                          
                         
                                               
                                             
                                         
                                                    
              
                                                                              
                                                                                     
                    
            
            
                                                                
                                                                           
                                         
                                                                          
                                     
                                                                             
                                                       
                                                 
                   

                                                                        
                                                          
                                                  
                                     
                                                                
                                                            
                                                                 
                               
                                                  
                                       
                  
             
           
        
                                              
                                                              
              
          
            
                                                        
                                   
                                                                                
                                               
                         
                                                                                       
                             
                                          
                                                 
                                                                                        
                    
                                                                         

private theorem conjK_ne_refl : conjK ≠ AlgEquiv.refl := by
  intro he
  have hw : omega ^ 2 = omega := by
    have hc : conjO omega = omega := by
      apply NumberField.RingOfIntegers.coe_injective
      change conjK (omega : K) = (omega : K)
      rw [he]
      rfl
    exact conjO_omega.symm.trans hc
  have hw1 : omega = 1 := by
    have hunit : IsUnit omega := omega_primitive.isUnit (by decide)
    apply (mul_left_cancel₀ hunit.ne_zero)
    calc
      omega * omega = omega ^ 2 := by ring
      _ = omega := hw
      _ = omega * 1 := by ring
  exact (omega_primitive.ne_one (by decide)) hw1

private theorem galois_card_two : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ K,
    IsCyclotomicExtension.finrank (n := 3) K
      (Polynomial.cyclotomic.irreducible_rat (by decide))]
  decide

private theorem galois_univ_pair [DecidableEq (K ≃ₐ[ℚ] K)] :
    (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {(AlgEquiv.refl : K ≃ₐ[ℚ] K), conjK} := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, galois_card_two, Finset.card_pair]
  exact conjK_ne_refl.symm

private theorem norm_eq_mul_conjK (p : O) :
    ((Algebra.norm ℚ (p : K) : ℚ) : K) = (p : K) * conjK (p : K) := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  have h := Algebra.norm_eq_prod_automorphisms ℚ (p : K)
  rw [galois_univ_pair, Finset.prod_pair conjK_ne_refl.symm] at h
  simpa using h

theorem norm_int_eq_mul_conjO (p : O) :
    ((Algebra.norm ℤ p : ℤ) : O) = p * conjO p := by
  apply NumberField.RingOfIntegers.coe_injective
  change ((Algebra.norm ℤ p : ℤ) : K) = (p : K) * conjK (p : K)
  have h := norm_eq_mul_conjK p
  rw [← Algebra.coe_norm_int p] at h
  exact h

                                                                           
                                       
                                          
                                                 
                                                                
        
                                                                   
                                             
                                         
                                
                                                          
                                                      
                                                           
                                            
                    
                                                            
                                                           
                   
                                              
        
                                                                               
                                         
         
                                                                                           
                                         

                                                                          
                                                            
                                                                             
           
                                                            
                                                                                         
                        
                                              
                                   
                                                      
                                   
                           
                        
                                        
                                                                           
        
                                                                   
                          
                                   
                                                                
                                                        
                                 
          
                                 
          
                                                                       
                                                   
           
                                 
          
                                                                       
                                                    
                              
                            
                                            
                                           
                     
          
                          
                                        

                                                                                     
                                                          
                                     
                                                                
                                                            
                                                                        
                               
                                                  
                                       
                  
             
           
        
                                              
                                                              
              
          
            
                                                        
                                   
                                                                                
                                               
                         
                                                                                       
                             
                                          
                                                 
                                                                                        
                    
                                                                         

                                                               
                          
                                                                            
           
                                                            
                                                               
                                                                      
                                                                
                              
                                      
                                                                      
                                             
        
                                                       
                                                      
                                  
                                                                           
                                              
                                                    
                                         
                                                                          
          
                                                                       
                                               
                                                                          
                                                               
                                                          
                                                          
                           
                                             

                                                                        
                          
                                                      
                                                                  
                                                            
                                  
                                                 
                                                    
                                                    
                   
             
           
        

                                                                  
                    
         
                                             

                                                                              
                                                               
                                          
                                                      
                                                         
                                                     
                                                                    
                                                                

                                                           
                                                           
                                                          
                                   
                                                  
                                                        
                                           
           
                                               
                                             
                            
                          
                                                     
                                               
                            
           
                                 
                         
                                       
                                      
                  
                                                                   
                            
                                             
                                                 
                                                     
                                
                                   
                                             
                                
                                                      
                                                                
                                                    
                            
                                                                   
                               
                         
                       
                                    
                                                  
                                                                         
                                                   
                                                     
                                    
                    
                                                 
                                        
                                                                 
                              
                                                                                
              
                                                                               
                                                           
      
                                                                              
                                                                      
                                                                  
                                                                

                                                 
                  

                                          
                                                  

                                                                 
                                                                          

                                           
                                                      
                            
                            
                                    
                                                       
                        
           
                                       
                         
                                                                            
                                    
                              
        
                                                                                        
                                               
                                                                                       
                                       
                                                                               
                                                                       
                                                               
                             
                     
                                                   
          

                                                           
                                                          
                                     
                                                          
                                                                  
                                                     
                                               
                                                                               
                                                          
                                                                      

                                                                      
                                                          
                                     
                                              
                                        
                                                                              
                 
                                  

                                                                      
                                                          
                                     
                                                           
                                                              
                                  
                                                    
                        
                                                                 
                                                          
                                                                         
                                            
                                                        
                                                        
                                                                            
                                              
                                   
                                
           
                                      
                 
                                                  
                                                 
                                             
                      
            

                                                                    
                                                    
                                            
                                                                     
                                                              
                                               
                                            
                            
                                                      
                                                             
                              
                                     
                                                           
                                                        
                                                         
                                                     

                                                         
                                                               
           
                                               
                                             
                                                                    
                                       
                                                                 

                                                    
                                                         
                                          
                                          
                                            
                                            
                                                 
                                
                                                    
            
                                                       
                      
                                      
                                                    
            
                                                       
                      
                                           
                                                    
            
                                        
                  
                                                           
                                                    
            
                         
                                                                         
                                                                                 
                                                    
            
                         
                                                    
            
                         
       

                                                                 
                                                         
                                                       
         
                                                
        
                                
                                                                       
                                 
                                                 
                                  
                                             
                  

                                                          
                                                       
                    
                                                            
                                                      
           
                                               
                                             
                               
                      
                               
                                                                                 
                                                                    
                                        
                                   
                                  
             
                                              
                                               
                                        
                                            
                                                 
                                 
                                                          
                                                                
                                                 
                                       
                                                                                       
                                             
                                                           
                                                                       
                                                                           
                    
                                                   
                                                               
                        
          
                                                             
                                       
                                       
                     
                   
                                                         
                                               
                                                        
                    

                                                                       
                                                   
                                               
           
                                                                              
                
          
                                                                                                

                                                           
                                  
                                                                
                                               
                                
                                                
                                                      

                                                               
                                          
                                                                      
                                               
                                
                                                
                                                      

end ActualEisensteinCubic

end

end OAI
