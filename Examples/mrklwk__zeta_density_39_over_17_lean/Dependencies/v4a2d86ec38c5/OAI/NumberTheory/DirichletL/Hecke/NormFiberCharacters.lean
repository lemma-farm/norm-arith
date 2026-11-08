module
public import Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v4a2d86ec38c5.OAI.NumberTheory.DirichletL.Arithmetic.NormFiberMellin
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
namespace ActualEisensteinCubic
open MulChar AddChar
end ActualEisensteinCubic
namespace ShortDraftHeckeBridge
private abbrev K := CyclotomicField 3 ℚ
private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
private theorem orderOf_mod3_eq_two {p : ℕ} (h : p % 3 = 2) :
    orderOf (p : ZMod 3) = 2 := by
  have hc : (p : ZMod 3) = 2 :=
    (ZMod.natCast_eq_natCast_iff' p 2 3).2 (by simpa using h)
  rw [hc]
  have hdvd : orderOf (2 : ZMod 3) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by decide : (2 : ZMod 3) ^ 2 = 1)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).1 hdvd with h1 | h2
  · have h21 : (2 : ZMod 3) = 1 := orderOf_eq_one_iff.mp h1
    exact False.elim ((by decide : (2 : ZMod 3) ≠ 1) h21)
  · exact h2
private theorem not_dvd_three {p : ℕ} (hp : p.Prime) (hneq : p ≠ 3) : ¬ p ∣ 3 := by
  intro hd
  have h := (Nat.dvd_prime (by decide : Nat.Prime 3)).1 hd
  rcases h with h1 | h3
  · exact hp.ne_one h1
  · exact hneq h3
theorem absNorm_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 2 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_two hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf]
theorem norm_prime_implies_over {p : ℕ} (hp : p.Prime) (I : Ideal O)
    (hI : Ideal.absNorm I = p) :
    I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  have hprime : I.IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by
      rw [hI]
      exact (Nat.irreducible_iff_nat_prime p).2 hp)
  have hover : I.LiesOver (Ideal.span {(p : ℤ)}) := by
    rw [Ideal.liesOver_iff]
    rw [Ideal.under_def, algebraMap_int_eq]
    simpa [hI] using Ideal.span_singleton_absNorm (I := I) (hI ▸ hp)
  exact ⟨hprime, hover⟩
theorem norm_p_fiber_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    {I : Ideal O | Ideal.absNorm I = p} = ∅ := by
  ext I
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hI
  have hOver := norm_prime_implies_over hp I hI
  let : I.IsPrime := hOver.1
  let : I.LiesOver (Ideal.span {(p : ℤ)}) := hOver.2
  have hNorm := absNorm_inert hp hmod I
  have hpge := hp.two_le
  nlinarith
end ShortDraftHeckeBridge
end
end OAI
