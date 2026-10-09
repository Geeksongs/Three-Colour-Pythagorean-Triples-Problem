import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Pyth

/-- Natural-number Euclid parametrisation of every positive Pythagorean triple. -/
theorem euclid_nat (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + b * b = c * c) :
    ∃ K M n : ℕ, 0 < K ∧ 0 < n ∧ n < M ∧ Nat.gcd M n = 1 ∧ c = K * (M * M + n * n) ∧
      ((a = K * (M * M - n * n) ∧ b = K * (2 * M * n)) ∨
       (a = K * (2 * M * n) ∧ b = K * (M * M - n * n))) := by
  have hT : PythagoreanTriple (a : ℤ) b c := by
    unfold PythagoreanTriple; exact_mod_cast h
  obtain ⟨k, m, n, hxy, hg⟩ := hT.classified
  -- absolute values
  have hm2 : (m.natAbs : ℤ) ^ 2 = m ^ 2 := Int.natAbs_sq m
  have hn2 : (n.natAbs : ℤ) ^ 2 = n ^ 2 := Int.natAbs_sq n
  have hk2 : (k.natAbs : ℤ) ^ 2 = k ^ 2 := Int.natAbs_sq k
  set K := k.natAbs with hK
  set p := m.natAbs with hp
  set q := n.natAbs with hq
  have hgcd : Nat.gcd p q = 1 := hg
  -- the hypotenuse
  have hc : c = K * (p * p + q * q) := by
    have h1 : (c : ℤ) ^ 2 = ((K * (p * p + q * q) : ℕ) : ℤ) ^ 2 := by
      have hz : (c : ℤ) * c = (a : ℤ) * a + b * b := by exact_mod_cast h.symm
      push_cast
      have e0 : (p : ℤ) * p + (q : ℤ) * q = m ^ 2 + n ^ 2 := by
        rw [← sq, ← sq, hm2, hn2]
      have e : ((K : ℤ) * ((p : ℤ) * p + (q : ℤ) * q)) ^ 2 = k ^ 2 * (m ^ 2 + n ^ 2) ^ 2 := by
        rw [mul_pow, hk2, e0]
      rw [e]
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hz
        linear_combination hz
      · rw [h1, h2] at hz
        linear_combination hz
    have h2 : c * c = (K * (p * p + q * q)) * (K * (p * p + q * q)) := by
      have : ((c * c : ℕ) : ℤ) = (((K * (p * p + q * q)) * (K * (p * p + q * q)) : ℕ) : ℤ) := by
        push_cast at h1 ⊢; nlinarith [h1]
      exact_mod_cast this
    exact Nat.mul_self_inj.mp h2
  -- sign-free forms of the legs
  have hdiff : m ^ 2 - n ^ 2 = (p : ℤ) ^ 2 - (q : ℤ) ^ 2 := by rw [hm2, hn2]
  have hprod : (2 * m * n : ℤ).natAbs = 2 * p * q := by
    simp [Int.natAbs_mul, hp, hq]
  rcases Nat.lt_trichotomy q p with hqp | hqp | hqp
  · -- q < p
    have hq0 : 0 < q := by
      by_contra hq0
      have hq0' : q = 0 := by omega
      have : n = 0 := by simpa [hq] using hq0'
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [this] at h1 h2 <;> omega
    refine ⟨K, p, q, ?_, hq0, hqp, hgcd, hc, ?_⟩
    · have : k ≠ 0 := by
        rintro rfl
        rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp at h1 h2 <;> omega
      exact Int.natAbs_pos.mpr this
    · have hle : q * q ≤ p * p := Nat.mul_le_mul hqp.le hqp.le
      have hsub : (m ^ 2 - n ^ 2 : ℤ) = ((p * p - q * q : ℕ) : ℤ) := by
        rw [hdiff]; push_cast [Nat.cast_sub hle]; ring
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        constructor
        · have := congrArg Int.natAbs h1
          simpa [Int.natAbs_mul, hsub, hK] using this
        · have := congrArg Int.natAbs h2
          simp only [Int.natAbs_natCast, Int.natAbs_mul] at this
          rw [← mul_assoc] at this
          simpa [Int.natAbs_mul, hK, hp, hq, mul_assoc] using this
      · right
        constructor
        · have := congrArg Int.natAbs h1
          simpa [Int.natAbs_mul, hK, hp, hq, mul_assoc] using this
        · have := congrArg Int.natAbs h2
          simpa [Int.natAbs_mul, hsub, hK] using this
  · -- p = q : one leg vanishes
    exfalso
    have : m ^ 2 - n ^ 2 = 0 := by rw [hdiff, hqp]; ring
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [this] at h1; simp at h1; omega
    · rw [this] at h2; simp at h2; omega
  · -- p < q : swap roles
    have hp0 : 0 < p := by
      by_contra hp0
      have hp0' : p = 0 := by omega
      have : m = 0 := by simpa [hp] using hp0'
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [this] at h1 h2 <;> omega
    refine ⟨K, q, p, ?_, hp0, hqp, ?_, ?_, ?_⟩
    · have : k ≠ 0 := by
        rintro rfl
        rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp at h1 h2 <;> omega
      exact Int.natAbs_pos.mpr this
    · rw [Nat.gcd_comm]; exact hgcd
    · rw [hc]; ring
    · have hle : p * p ≤ q * q := Nat.mul_le_mul hqp.le hqp.le
      have hsub : (m ^ 2 - n ^ 2 : ℤ) = -((q * q - p * p : ℕ) : ℤ) := by
        rw [hdiff]; push_cast [Nat.cast_sub hle]; ring
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        constructor
        · have := congrArg Int.natAbs h1
          simpa [Int.natAbs_mul, hsub, hK] using this
        · have := congrArg Int.natAbs h2
          simpa [Int.natAbs_mul, hK, hp, hq, mul_assoc, mul_comm, mul_left_comm] using this
      · right
        constructor
        · have := congrArg Int.natAbs h1
          simpa [Int.natAbs_mul, hK, hp, hq, mul_assoc, mul_comm, mul_left_comm] using this
        · have := congrArg Int.natAbs h2
          simpa [Int.natAbs_mul, hsub, hK] using this

end Pyth
