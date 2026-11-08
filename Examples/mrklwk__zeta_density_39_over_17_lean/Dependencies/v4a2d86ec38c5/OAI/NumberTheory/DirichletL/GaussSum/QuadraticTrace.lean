module
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.Arithmetic.LatticeCount
public import Mathlib
set_option autoImplicit false
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
open Finset Complex
open scoped Classical
open scoped Classical
namespace ActualEisensteinCubic
section
open ActualEisensteinCoordinates ShortDraftLatticeCount
theorem omega_sq_for_norm : omega ^ 2 = -omega - 1 := by
  simpa [omega] using
    IsCyclotomicExtension.Rat.Three.eta_sq
      (IsCyclotomicExtension.zeta_spec 3 ℚ K)
theorem conjO_eval_coordinates (a b : ℤ) :
    conjO (eval a b) = eval (a - b) (-b) := by
  have hω : ActualEisensteinCoordinates.omega = omega := rfl
  simp only [eval, map_add, map_mul, map_intCast, hω, conjO_omega]
  rw [omega_sq_for_norm]
  push_cast
  ring
theorem coordinate_norm_eq_mul_conjO (p : O) :
    ((q (coords p) : ℤ) : O) = p * conjO p := by
  let a := (coords p).1
  let b := (coords p).2
  have hp : p = eval a b := (eval_coords p).symm
  symm
  calc
    p * conjO p = eval a b * eval (a - b) (-b) := by
      rw [hp, conjO_eval_coordinates]
    _ = ((q (coords p) : ℤ) : O) := by
      rw [eval_mul]
      simp only [eval, q]
      dsimp [a, b]
      push_cast
      ring
theorem algebraNorm_eq_coordinate_norm (p : O) :
    Algebra.norm ℤ p = q (coords p) := by
  have h := (norm_int_eq_mul_conjO p).trans
    (coordinate_norm_eq_mul_conjO p).symm
  exact_mod_cast h
theorem qNat_eq_absNorm_span (p : O) :
    qNat p = Ideal.absNorm (Ideal.span {p}) := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_eq_coordinate_norm]
  unfold qNat
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg (qO_nonneg p),
    Int.natAbs_of_nonneg (qO_nonneg p)]
end
section
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
theorem rational_modulus_card (m : ℕ) (_hm : m ≠ 0) :
    Nat.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
  have hnorm : Algebra.norm ℤ (m : O) = (m : ℤ) ^ 2 := by
    have h := Algebra.norm_algebraMap_of_basis
      EisensteinEmbedding.pb.basis (m : ℤ)
    simpa [EisensteinEmbedding.pb_dim] using h
  calc
    Nat.card (O ⧸ Ideal.span {(m : O)}) =
        Ideal.absNorm (Ideal.span {(m : O)}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = (Algebra.norm ℤ (m : O)).natAbs :=
      Ideal.absNorm_span_singleton (m : O)
    _ = m ^ 2 := by rw [hnorm]; simp
theorem eisEmbedding_eval (a b : ℤ) :
    eisEmbedding (ActualEisensteinCoordinates.eval a b) =
      (a : ℂ) + (b : ℂ) * omega3 := by
  have hgen : ActualEisensteinCoordinates.omega =
      EisensteinEmbedding.pb.gen := by
    rw [← ActualEisensteinCoordinates.pb_gen]
    rfl
  rw [ActualEisensteinCoordinates.eval, hgen]
  change EisensteinEmbedding.embedding omega3 omega3_sq
    (a + b * EisensteinEmbedding.pb.gen : O) = _
  exact EisensteinEmbedding.embedding_apply_ab omega3 omega3_sq a b
end
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
end ActualEisensteinCubic
end
end OAI
