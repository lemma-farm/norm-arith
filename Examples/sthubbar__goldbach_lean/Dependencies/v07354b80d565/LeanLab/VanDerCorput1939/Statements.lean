module
public import Mathlib
/-!
P0067 J. G. van der Corput, Sur la démonstration de l'hypothèse de Goldbach pour les nombres
impairs, donnée par M. Vinogradow, Bull. Soc. Math. France 67 1939, supplément, 87-99,
a lecture of 8 July 1937. Read from the numdam scan, pages 87 to 94, run 20261016T2204Z-20593.
STATED: Vinogradov's asymptotic (1) to (3) for I(N), the number of ways to write odd N as a sum
of three primes, as van der Corput reports it.
PROVED, no gaps: the Euler factor identity (1 + 1/(p-1)³)(1 - 1/(p² - 3p + 3)) = 1 - 1/(p-1)²,
prime by prime; the global identity of K P(N) with the singular series is NOT formalized;
K ≥ 1; that (1) gives every large odd N as a sum of three primes; and, in Totient.lean, the
lecture's φ(q) ≥ (1/2) q^{3/4}.
Not stated: the major and minor arc estimates of pages 91 to 99, whose constants c_m, γ_i
are not explicit.
AI-written Lean code, Claude. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013.
-/
@[expose] public section
noncomputable section
namespace LeanLab.VanDerCorput1939
open Real Finset
attribute [local instance] Classical.propDecidable
/-- `I(N)`, ordered triples of primes `p₁ + p₂ + p₃ = N`, the count `∫₀¹ S³(α) e(-αN) dα` of (4). -/
def I (N : ℕ) : ℕ :=
  #{t ∈ (range (N + 1)) ×ˢ (range (N + 1)) | t.1.Prime ∧ t.2.Prime ∧ N - t.1 - t.2 ≠ 0 ∧
    (N - t.1 - t.2).Prime ∧ t.1 + t.2 ≤ N}
/-- (2) `K = ∏_p (1 + 1/(p-1)³)` over all primes. -/
def K : ℝ := ∏' p : {p : ℕ // p.Prime}, (1 + 1 / ((p : ℝ) - 1) ^ 3)
/-- (3) `P(N) = ∏_{p ∣ N} (1 - 1/(p² - 3p + 3))`. -/
def P (N : ℕ) : ℝ := ∏ p ∈ N.primeFactors, (1 - 1 / ((p : ℝ) ^ 2 - 3 * p + 3))
end LeanLab.VanDerCorput1939
