import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace Pyth

/-- Coincidence lemma.  If a Pythagorean triple has a ≡ b ≡ c (mod M), then M divides a, b and c. -/
theorem coincidence (a b c M : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + b * b = c * c)
    (h1 : (a : ℤ) ≡ b [ZMOD M]) (h2 : (b : ℤ) ≡ c [ZMOD M]) :
    M ∣ a ∧ M ∣ b ∧ M ∣ c := by
  -- reduce to a primitive triple
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
  obtain ⟨a0, b0, hcop, ha0, hb0⟩ := Nat.exists_coprime a b
  set g := Nat.gcd a b with hgdef
  have hgc : g ∣ c := by
    have hsq : g ^ 2 ∣ c ^ 2 := by
      refine ⟨a0 ^ 2 + b0 ^ 2, ?_⟩
      have : c ^ 2 = a ^ 2 + b ^ 2 := by nlinarith [h]
      rw [this, ha0, hb0]; ring
    exact (Nat.pow_dvd_pow_iff (by norm_num)).mp hsq
  obtain ⟨c0, hc0⟩ := hgc
  have hprim : a0 * a0 + b0 * b0 = c0 * c0 := by
    have hgg : 0 < g * g := Nat.mul_pos hg hg
    have : (g * g) * (a0 * a0 + b0 * b0) = (g * g) * (c0 * c0) := by
      have e1 : a * a + b * b = (g * g) * (a0 * a0 + b0 * b0) := by rw [ha0, hb0]; ring
      have e2 : c * c = (g * g) * (c0 * c0) := by rw [hc0]; ring
      rw [← e1, ← e2]; exact h
    exact Nat.eq_of_mul_eq_mul_left hgg this
  -- differences
  have hd1 : (M : ℤ) ∣ (b : ℤ) - a := (Int.ModEq.dvd h1)
  have hd2 : (M : ℤ) ∣ (c : ℤ) - b := (Int.ModEq.dvd h2)
  have hb1 : (b : ℤ) - a = g * ((b0 : ℤ) - a0) := by rw [ha0, hb0]; push_cast; ring
  have hb2 : (c : ℤ) - b = g * ((c0 : ℤ) - b0) := by rw [hc0, hb0]; push_cast; ring
  rw [hb1] at hd1; rw [hb2] at hd2
  -- the two primitive differences are coprime
  have hcopd : Int.gcd ((b0 : ℤ) - a0) ((c0 : ℤ) - b0) = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpa : (p : ℤ) ∣ (b0 : ℤ) - a0 := (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_left _ _)
    have hpb : (p : ℤ) ∣ (c0 : ℤ) - b0 := (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_right _ _)
    obtain ⟨u, hu⟩ := hpa
    obtain ⟨v, hv⟩ := hpb
    have hb0' : (b0 : ℤ) = a0 + p * u := by linarith
    have hc0' : (c0 : ℤ) = a0 + p * u + p * v := by linarith
    have hz : ((a0 * a0 + b0 * b0 : ℕ) : ℤ) = ((c0 * c0 : ℕ) : ℤ) := by rw [hprim]
    push_cast at hz
    rw [hb0', hc0'] at hz
    have hpa0 : (p : ℤ) ∣ (a0 : ℤ) ^ 2 := by
      refine ⟨2 * a0 * v + p * ((u + v) ^ 2 - u ^ 2), ?_⟩
      linear_combination hz
    have hpa1 : (p : ℤ) ∣ (a0 : ℤ) := (Int.Prime.dvd_pow' hp hpa0)
    have hpa2 : p ∣ a0 := Int.natCast_dvd_natCast.mp hpa1
    have hpb1 : (p : ℤ) ∣ (b0 : ℤ) := by rw [hb0']; exact dvd_add hpa1 (dvd_mul_right _ _)
    have hpb2 : p ∣ b0 := Int.natCast_dvd_natCast.mp hpb1
    have : p ∣ Nat.gcd a0 b0 := Nat.dvd_gcd hpa2 hpb2
    rw [hcop] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  -- M divides g
  have hMg' : M ∣ g := by
    have := Int.dvd_gcd hd1 hd2
    rw [Int.gcd_mul_left, hcopd] at this
    simpa using this
  refine ⟨hMg'.trans (Nat.gcd_dvd_left a b), hMg'.trans (Nat.gcd_dvd_right a b), ?_⟩
  exact hMg'.trans ⟨c0, hc0⟩

end Pyth
