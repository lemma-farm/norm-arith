/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.UniversalF3

/-! # Explicit uniform scales for universal F3 absorption

The host parameter may vary with its order.  The absorber density `δ` is also
free, subject to one linear upper bound.  All order requirements reduce to
`1 ≤ refinerRho C γ δ * n`; the density is an explicit polynomial expression.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General

open Finset AntiEdgeSelection TypedApplicationLinks

noncomputable def refinerLambda (C γ δ : ℝ) : ℝ :=
  γ * δ / (2 ^ 24 * (C + 1))

noncomputable def refinerRho (C γ δ : ℝ) : ℝ :=
  (refinerLambda C γ δ) ^ 2 / 2 ^ 43

theorem refinerLambda_pos {C γ δ : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ) (hδ : 0 < δ) :
    0 < refinerLambda C γ δ := by
  unfold refinerLambda
  positivity

theorem refinerRho_pos {C γ δ : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ) (hδ : 0 < δ) :
    0 < refinerRho C γ δ := by
  unfold refinerRho
  have h := refinerLambda_pos hC hγ hδ
  positivity

theorem compatible_scales (C γ δ lam rho : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hγ1 : γ ≤ 1)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hs : (2 ^ 24 : ℝ) * (C + 1) * lam ≤ γ * δ)
    (hr : (2 ^ 43 : ℝ) * rho ≤ lam ^ 2) :
    8 * lam + 2 * rho ≤ δ ∧
      4200 * C * lam ≤ δ / 4 ∧
      8 * lam + 2 * rho + (2 ^ 35 : ℝ) * C * rho ≤ γ * δ / 4 := by
  have hClam : 0 ≤ C * lam := mul_nonneg hC hlam
  have hγδ : γ * δ ≤ δ := mul_le_of_le_one_left hδ hγ1
  have hlam2 : lam ^ 2 ≤ lam := by nlinarith
  have hCr := mul_le_mul_of_nonneg_left hr hC
  have hClam2 : C * lam ^ 2 ≤ C * lam := mul_le_mul_of_nonneg_left hlam2 hC
  norm_num at hs hr hCr
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem uniform_scalar_budget (S C γ δ n : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hδ : 0 < δ)
    (hsmall : 64 * (S + 1) * δ ≤ γ) (hn0 : 0 ≤ n)
    (hn1 : 1 ≤ refinerRho C γ δ * n) :
    let lam := refinerLambda C γ δ
    let rho := refinerRho C γ δ
    0 < lam ∧ lam ≤ 1 / 64 ∧ 32 * lam ≤ γ ∧ 0 < rho ∧
      2 ^ 42 * rho ≤ lam ^ 2 ∧ 256 ≤ lam * n ∧
      S + S * (2 * δ * n) < γ * n / 2 ∧ C ≤ δ * n / 4 ∧
      8 * lam + 2 * rho ≤ δ ∧ 4200 * C * lam ≤ δ / 4 ∧
      8 * lam + 2 * rho + (2 ^ 35 : ℝ) * C * rho ≤ γ * δ / 4 := by
  dsimp only
  let lam := refinerLambda C γ δ
  let rho := refinerRho C γ δ
  change 1 ≤ rho * n at hn1
  have hlam : 0 < lam := refinerLambda_pos hC hγ hδ
  have hrho : 0 < rho := refinerRho_pos hC hγ hδ
  have hn : 0 < n := by nlinarith only [hn1, hrho.le, hn0]
  have hlamEq : (2 ^ 24 : ℝ) * (C + 1) * lam = γ * δ := by
    dsimp [lam, refinerLambda]
    field_simp
  have hrhoEq : (2 ^ 43 : ℝ) * rho = lam ^ 2 := by
    dsimp [rho, refinerRho, lam]
    ring
  have hSδ : 0 ≤ S * δ := mul_nonneg hS hδ.le
  have hδ64 : δ ≤ 1 / 64 := by nlinarith only [hsmall, hSδ, hγ1]
  have hγδ : γ * δ ≤ δ := mul_le_of_le_one_left hδ.le hγ1
  have hClam : 0 ≤ C * lam := mul_nonneg hC hlam.le
  have hlamδ : lam ≤ δ := by
    norm_num at hlamEq
    nlinarith only [hlamEq, hClam, hlam.le, hγδ]
  have hlam64 : lam ≤ 1 / 64 := hlamδ.trans hδ64
  have hγδ' : γ * δ ≤ γ := mul_le_of_le_one_right hγ.le (by linarith only [hδ64])
  have hlamγ : 32 * lam ≤ γ := by
    norm_num at hlamEq
    nlinarith only [hlamEq, hClam, hlam.le, hγδ']
  have hscale : (2 ^ 42 : ℝ) * rho ≤ lam ^ 2 := by
    nlinarith only [hrhoEq, hrho.le]
  have hlam2 : lam ^ 2 ≤ lam := by nlinarith only [hlam.le, hlam64]
  have hrholam : 256 * rho ≤ lam := by
    norm_num at hrhoEq
    nlinarith only [hrhoEq, hlam2, hrho.le]
  have hn2 : 256 ≤ lam * n := by
    have h1 := mul_le_mul_of_nonneg_left hn1 (show (0 : ℝ) ≤ 256 by norm_num)
    have h2 := mul_le_mul_of_nonneg_right hrholam hn0
    nlinarith only [h1, h2]
  have hrhoδ : rho ≤ δ := by linarith only [hrholam, hlamδ, hrho.le]
  have hSr : 8 * S * rho ≤ γ := by
    have h1 := mul_le_mul_of_nonneg_left hrhoδ hS
    nlinarith only [h1, hsmall, hSδ, hδ.le]
  have hSN : 8 * S ≤ γ * n := by
    have h1 := mul_le_mul_of_nonneg_left hn1 (show 0 ≤ 8 * S by positivity)
    have h2 := mul_le_mul_of_nonneg_right hSr hn0
    nlinarith only [h1, h2]
  have hSδN : 64 * S * δ * n ≤ γ * n := by
    have h1 : 64 * S * δ ≤ γ := by nlinarith only [hsmall, hδ.le]
    exact mul_le_mul_of_nonneg_right h1 hn0
  have hembed : S + S * (2 * δ * n) < γ * n / 2 := by
    have hγn : 0 < γ * n := mul_pos hγ hn
    nlinarith only [hSN, hSδN, hγn]
  have hCr : 4 * C * rho ≤ δ := by
    have h1 : rho ≤ lam := by linarith only [hrholam, hrho.le]
    have h2 := mul_le_mul_of_nonneg_left h1 hC
    norm_num at hlamEq
    nlinarith only [h2, hlamEq, hClam, hlam.le, hγδ]
  have hfixed : C ≤ δ * n / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hn1 (show 0 ≤ 4 * C by positivity)
    have h2 := mul_le_mul_of_nonneg_right hCr hn0
    nlinarith only [h1, h2]
  obtain ⟨hledger, hroot, hcount⟩ := compatible_scales C γ δ lam rho hC hδ.le hγ1
    hlam.le (by linarith only [hlam64]) hlamEq.le hrhoEq.le
  exact ⟨hlam, hlam64, hlamγ, hrho, hscale, hn2, hembed, hfixed, hledger, hroot, hcount⟩

                                                                              
                                                                              
                              
                              
                                               
                                                                             
                                            
                                                                       
                                                            
                                               
                                                              
                                                     
                                                                                 
                                                                                            
                                                                                          
                                              
                                                                      
                                                                               

                                   
                                  

end PartitionedTriangleAbsorption.StructuralF3General
