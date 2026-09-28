import Mathlib.Data.Nat.MaxPrimeFac
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace JSP000307

theorem jsp_000307 :
    ∃ n p₁ p₂ p₃ : ℕ,
      n = 13 ∧
      Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧
      p₁ > p₂ ∧ p₂ > p₃ ∧
      p₁ ∣ n ∧ p₂ ∣ n + 1 ∧ p₃ ∣ n + 2 ∧
      (∀ d, Nat.Prime d → d ∣ n → d ≤ p₁) ∧
      (∀ d, Nat.Prime d → d ∣ n + 1 → d ≤ p₂) ∧
      (∀ d, Nat.Prime d → d ∣ n + 2 → d ≤ p₃) := by
  refine ⟨13, 13, 7, 5, rfl, by decide, by decide, by decide, by decide, by decide,
    by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · -- every prime divisor of 13 equals 13
    intro d hd hdvd
    have hd13 : d ≤ 13 := Nat.le_of_dvd (by norm_num) hdvd
    have h13p : Nat.Prime 13 := by decide
    have hd13 : d = 13 := (Nat.prime_dvd_prime_iff_eq hd h13p).mp hdvd
    omega
  · -- every prime divisor of 14 = 2·7 is 2 or 7, hence ≤ 7
    intro d hd hdvd
    have hd14 : d ≤ 14 := Nat.le_of_dvd (by norm_num) hdvd
    have hrew : (13:ℕ) + 1 = 2 * 7 := by norm_num
    have hdvd' : d ∣ 2 * 7 := by
      have h2 : d ∣ 13 + 1 := hdvd
      rw [hrew] at h2
      exact h2
    have hsplit := (Nat.Prime.dvd_mul hd).mp hdvd'
    rcases hsplit with h | h
    · have hd2 : d = 2 := (Nat.prime_dvd_prime_iff_eq hd (by decide)).mp h
      omega
    · -- d ∣ 7, d prime → d = 7
      have hd7 : d = 7 := (Nat.prime_dvd_prime_iff_eq hd (by decide)).mp h
      omega
  · -- every prime divisor of 15 = 3·5 is 3 or 5, hence ≤ 5 < 7
    intro d hd hdvd
    have hrew : (13:ℕ) + 2 = 3 * 5 := by norm_num
    have hdvd' : d ∣ 3 * 5 := by
      have h2 : d ∣ 13 + 2 := hdvd
      rw [hrew] at h2
      exact h2
    have hsplit := (Nat.Prime.dvd_mul hd).mp hdvd'
    rcases hsplit with h | h
    · have hd3 : d = 3 := (Nat.prime_dvd_prime_iff_eq hd (by decide)).mp h
      omega
    · have hd5 : d = 5 := (Nat.prime_dvd_prime_iff_eq hd (by decide)).mp h
      omega

end JSP000307
