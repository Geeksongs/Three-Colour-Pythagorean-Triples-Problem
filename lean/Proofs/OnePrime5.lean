import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
Exact unavoidability threshold for colourings by the 5-adic valuation:
every K-colouring F(v_5(n)) has a monochromatic Pythagorean triple with hypotenuse ≤ 5^K,
and F(s) = s mod K has none with hypotenuse < 5^K.
-/

namespace Pyth5

/-! ## Upper bound -/

/-- (2+i)^n as a pair of integers. -/
def gp : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | (n + 1) => (2 * (gp n).1 - (gp n).2, (gp n).1 + 2 * (gp n).2)

lemma gp_norm (n : ℕ) : (gp n).1 ^ 2 + (gp n).2 ^ 2 = 5 ^ n := by
  induction n with
  | zero => simp [gp]
  | succ n ih =>
    have h : (gp (n + 1)).1 ^ 2 + (gp (n + 1)).2 ^ 2 = 5 * ((gp n).1 ^ 2 + (gp n).2 ^ 2) := by
      simp only [gp]; ring
    rw [h, ih]; ring

lemma gp_inv (n : ℕ) :
    ((gp (n + 1)).1 : ZMod 5) = 2 * (gp (n + 1)).2 ∧ ((gp (n + 1)).2 : ZMod 5) ≠ 0 := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> simp [gp] <;> decide
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have key : ∀ y : ZMod 5, y ≠ 0 →
        (2 * (2 * y) - y = 2 * (2 * y + 2 * y)) ∧ (2 * y + 2 * y ≠ 0) := by decide
    obtain ⟨k1, k2⟩ := key _ h2
    have e1 : ((gp (n + 2)).1 : ZMod 5) = 2 * (gp (n + 1)).1 - (gp (n + 1)).2 := by
      simp only [gp]; push_cast; ring
    have e2 : ((gp (n + 2)).2 : ZMod 5) = (gp (n + 1)).1 + 2 * (gp (n + 1)).2 := by
      simp only [gp]; push_cast; ring
    refine ⟨?_, ?_⟩
    · rw [e1, e2, h1]; exact k1
    · rw [e2, h1]; exact k2

def leg1 (β : ℕ) : ℕ := ((gp β).1 ^ 2 - (gp β).2 ^ 2).natAbs
def leg2 (β : ℕ) : ℕ := (2 * (gp β).1 * (gp β).2).natAbs

lemma leg_sq (β : ℕ) : leg1 β ^ 2 + leg2 β ^ 2 = (5 ^ β) ^ 2 := by
  have h : ((leg1 β : ℕ) : ℤ) ^ 2 + ((leg2 β : ℕ) : ℤ) ^ 2 = ((5 : ℤ) ^ β) ^ 2 := by
    simp only [leg1, leg2, Int.natCast_natAbs, sq_abs]
    have := gp_norm β
    nlinarith [this]
  exact_mod_cast h

lemma leg_not_dvd (β : ℕ) (hβ : 1 ≤ β) : ¬ 5 ∣ leg1 β ∧ ¬ 5 ∣ leg2 β := by
  obtain ⟨n, rfl⟩ : ∃ n, β = n + 1 := ⟨β - 1, by omega⟩
  obtain ⟨h1, h2⟩ := gp_inv n
  have fin : ∀ x y : ZMod 5, x = 2 * y → y ≠ 0 → (x ^ 2 - y ^ 2 ≠ 0) ∧ (2 * x * y ≠ 0) := by decide
  obtain ⟨f1, f2⟩ := fin _ _ h1 h2
  constructor
  · intro hd
    apply f1
    have hz : ((5 : ℕ) : ℤ) ∣ ((gp (n + 1)).1 ^ 2 - (gp (n + 1)).2 ^ 2) := Int.natCast_dvd.mpr hd
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((gp (n + 1)).1 ^ 2 - (gp (n + 1)).2 ^ 2) 5).mpr
      (by exact_mod_cast hz)
    push_cast at this
    exact this
  · intro hd
    apply f2
    have hz : ((5 : ℕ) : ℤ) ∣ (2 * (gp (n + 1)).1 * (gp (n + 1)).2) := Int.natCast_dvd.mpr hd
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (gp (n + 1)).1 * (gp (n + 1)).2) 5).mpr
      (by exact_mod_cast hz)
    push_cast at this
    exact this

theorem upper (K : ℕ) (hK : 0 < K) (F : ℕ → Fin K) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ c ≤ 5 ^ K ∧
      F (padicValNat 5 a) = F (padicValNat 5 b) ∧ F (padicValNat 5 b) = F (padicValNat 5 c) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  -- pigeonhole on the exponents 0..K
  obtain ⟨s, v, hsv, hvK, hF⟩ : ∃ s v : ℕ, s < v ∧ v ≤ K ∧ F s = F v := by
    have hcard : Fintype.card (Fin K) < Fintype.card (Fin (K + 1)) := by simp
    obtain ⟨x, y, hxy, hf⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (K + 1) => F (i : ℕ)) hcard
    have hne : (x : ℕ) ≠ (y : ℕ) := fun h => hxy (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ⟨x, y, h, by omega, hf⟩
    · exact ⟨y, x, h, by omega, hf.symm⟩
  obtain ⟨β, rfl⟩ : ∃ β, v = s + β := ⟨v - s, by omega⟩
  have hβ : 1 ≤ β := by omega
  obtain ⟨hn1, hn2⟩ := leg_not_dvd β hβ
  have ha0 : 0 < leg1 β := Nat.pos_of_ne_zero (fun h0 => hn1 (h0 ▸ dvd_zero 5))
  have hb0 : 0 < leg2 β := Nat.pos_of_ne_zero (fun h0 => hn2 (h0 ▸ dvd_zero 5))
  refine ⟨5 ^ s * leg1 β, 5 ^ s * leg2 β, 5 ^ (s + β), by positivity, by positivity, ?_, ?_, ?_, ?_⟩
  · have := leg_sq β
    calc (5 ^ s * leg1 β) ^ 2 + (5 ^ s * leg2 β) ^ 2
        = (5 ^ s) ^ 2 * (leg1 β ^ 2 + leg2 β ^ 2) := by ring
      _ = (5 ^ s) ^ 2 * (5 ^ β) ^ 2 := by rw [this]
      _ = (5 ^ (s + β)) ^ 2 := by rw [pow_add]; ring
  · exact Nat.pow_le_pow_right (by norm_num) hvK
  · have va : padicValNat 5 (5 ^ s * leg1 β) = s := by
      rw [padicValNat.mul (by positivity) ha0.ne', padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd hn1]; simp
    have vb : padicValNat 5 (5 ^ s * leg2 β) = s := by
      rw [padicValNat.mul (by positivity) hb0.ne', padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd hn2]; simp
    rw [va, vb]
  · have vb : padicValNat 5 (5 ^ s * leg2 β) = s := by
      rw [padicValNat.mul (by positivity) hb0.ne', padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd hn2]; simp
    have vc : padicValNat 5 (5 ^ (s + β)) = s + β := padicValNat.prime_pow _
    rw [vb, vc]; exact hF

/-! ## Lower bound -/

lemma five_dvd_one (x y z : ℕ) (h : x ^ 2 + y ^ 2 = z ^ 2) : 5 ∣ x ∨ 5 ∣ y ∨ 5 ∣ z := by
  have fin : ∀ a b c : ZMod 5, a ^ 2 + b ^ 2 = c ^ 2 → a = 0 ∨ b = 0 ∨ c = 0 := by decide
  have h' : ((x : ZMod 5)) ^ 2 + (y : ZMod 5) ^ 2 = (z : ZMod 5) ^ 2 := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 5) h
  rcases fin _ _ _ h' with h1 | h1 | h1
  · exact Or.inl ((ZMod.natCast_eq_zero_iff x 5).mp h1)
  · exact Or.inr (Or.inl ((ZMod.natCast_eq_zero_iff y 5).mp h1))
  · exact Or.inr (Or.inr ((ZMod.natCast_eq_zero_iff z 5).mp h1))

lemma bound_aux (K β g e0 c0 c : ℕ) (hKβ : K ∣ β) (hβ : 1 ≤ β)
    (hdvd : 5 ^ β ∣ e0) (he0 : 0 < e0) (hec : e0 ≤ c0) (hc : c = g * c0) (hg : 0 < g) :
    5 ^ K ≤ c := by
  have hKpos : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp at hKβ; omega
    · exact h
  have hβK : K ≤ β := Nat.le_of_dvd (by omega) hKβ
  have h1 : 5 ^ β ≤ e0 := Nat.le_of_dvd he0 hdvd
  have h2 : 5 ^ K ≤ 5 ^ β := Nat.pow_le_pow_right (by norm_num) hβK
  have h3 : c0 ≤ c := by rw [hc]; exact Nat.le_mul_of_pos_left c0 hg
  exact le_trans h2 (le_trans h1 (le_trans hec h3))

theorem lower (K : ℕ) (hK : 0 < K) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 2 + b ^ 2 = c ^ 2) (hc : c < 5 ^ K) :
    ¬ (padicValNat 5 a % K = padicValNat 5 b % K ∧ padicValNat 5 b % K = padicValNat 5 c % K) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rintro ⟨hab, hbc⟩
  -- reduce to a primitive triple
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
  obtain ⟨a0, b0, hcop, ha0, hb0⟩ := Nat.exists_coprime a b
  set g := Nat.gcd a b with hgdef
  have hgc : g ∣ c := by
    have hsq : g ^ 2 ∣ c ^ 2 := by
      refine ⟨a0 ^ 2 + b0 ^ 2, ?_⟩
      rw [← h, ha0, hb0]; ring
    exact (Nat.pow_dvd_pow_iff (by norm_num)).mp hsq
  obtain ⟨c0, hc0⟩ := hgc
  have hprim : a0 ^ 2 + b0 ^ 2 = c0 ^ 2 := by
    have hgg : 0 < g ^ 2 := by positivity
    have e : g ^ 2 * (a0 ^ 2 + b0 ^ 2) = g ^ 2 * c0 ^ 2 := by
      calc g ^ 2 * (a0 ^ 2 + b0 ^ 2) = a ^ 2 + b ^ 2 := by rw [ha0, hb0]; ring
        _ = c ^ 2 := h
        _ = g ^ 2 * c0 ^ 2 := by rw [hc0]; ring
    exact Nat.eq_of_mul_eq_mul_left hgg e
  have ha0pos : 0 < a0 := Nat.pos_of_ne_zero (by rintro rfl; simp at ha0; omega)
  have hb0pos : 0 < b0 := Nat.pos_of_ne_zero (by rintro rfl; simp at hb0; omega)
  have hc0pos : 0 < c0 := by
    have : 0 < c0 ^ 2 := by rw [← hprim]; positivity
    exact Nat.pos_of_ne_zero (by rintro rfl; simp at this)
  have hale : a0 ≤ c0 := (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp (by nlinarith [hprim])
  have hble : b0 ≤ c0 := (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp (by nlinarith [hprim])
  -- valuations of a, b, c
  have va : padicValNat 5 a = padicValNat 5 a0 + padicValNat 5 g := by
    rw [ha0, padicValNat.mul ha0pos.ne' hg.ne']
  have vb : padicValNat 5 b = padicValNat 5 b0 + padicValNat 5 g := by
    rw [hb0, padicValNat.mul hb0pos.ne' hg.ne']
  have vc : padicValNat 5 c = padicValNat 5 c0 + padicValNat 5 g := by
    rw [hc0, padicValNat.mul hg.ne' hc0pos.ne']; ring
  -- exactly one of a0, b0, c0 is divisible by 5
  have hab' : ¬ (5 ∣ a0 ∧ 5 ∣ b0) := fun ⟨h1, h2⟩ => by
    have := Nat.dvd_gcd h1 h2; rw [hcop] at this; omega
  have hac' : ¬ (5 ∣ a0 ∧ 5 ∣ c0) := fun ⟨h1, h2⟩ => by
    have h5b : 5 ∣ b0 ^ 2 := by
      have h5a2 : 5 ∣ a0 ^ 2 := dvd_pow h1 (by norm_num)
      have h5c2 : 5 ∣ a0 ^ 2 + b0 ^ 2 := by rw [hprim]; exact dvd_pow h2 (by norm_num)
      exact (Nat.dvd_add_right h5a2).mp h5c2
    exact hab' ⟨h1, (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5b)⟩
  have hbc' : ¬ (5 ∣ b0 ∧ 5 ∣ c0) := fun ⟨h1, h2⟩ => by
    have h5a : 5 ∣ a0 ^ 2 := by
      have h5b2 : 5 ∣ b0 ^ 2 := dvd_pow h1 (by norm_num)
      have h5c2 : 5 ∣ a0 ^ 2 + b0 ^ 2 := by rw [hprim]; exact dvd_pow h2 (by norm_num)
      exact (Nat.dvd_add_left h5b2).mp h5c2
    exact hab' ⟨(Nat.Prime.dvd_of_dvd_pow (by norm_num) h5a), h1⟩
  set s := padicValNat 5 g with hs
  rcases five_dvd_one a0 b0 c0 hprim with h5 | h5 | h5
  · -- 5 ∣ a0
    have hb5 : ¬ 5 ∣ b0 := fun h6 => hab' ⟨h5, h6⟩
    have hc5 : ¬ 5 ∣ c0 := fun h6 => hac' ⟨h5, h6⟩
    rw [va, vb, padicValNat.eq_zero_of_not_dvd hb5] at hab
    have hmod : padicValNat 5 a0 ≡ 0 [MOD K] :=
      Nat.ModEq.add_right_cancel' s (by simpa [Nat.ModEq] using hab)
    have hKd : K ∣ padicValNat 5 a0 := (Nat.modEq_zero_iff_dvd).mp hmod
    have hge : 1 ≤ padicValNat 5 a0 := one_le_padicValNat_of_dvd ha0pos.ne' h5
    have := bound_aux K _ g a0 c0 c hKd hge (pow_padicValNat_dvd) ha0pos hale hc0 hg
    omega
  · -- 5 ∣ b0
    have ha5 : ¬ 5 ∣ a0 := fun h6 => hab' ⟨h6, h5⟩
    have hc5 : ¬ 5 ∣ c0 := fun h6 => hbc' ⟨h5, h6⟩
    rw [va, vb, padicValNat.eq_zero_of_not_dvd ha5] at hab
    have hmod : padicValNat 5 b0 ≡ 0 [MOD K] :=
      Nat.ModEq.add_right_cancel' s (by simpa [Nat.ModEq] using hab.symm)
    have hKd : K ∣ padicValNat 5 b0 := (Nat.modEq_zero_iff_dvd).mp hmod
    have hge : 1 ≤ padicValNat 5 b0 := one_le_padicValNat_of_dvd hb0pos.ne' h5
    have := bound_aux K _ g b0 c0 c hKd hge (pow_padicValNat_dvd) hb0pos hble hc0 hg
    omega
  · -- 5 ∣ c0
    have ha5 : ¬ 5 ∣ a0 := fun h6 => hac' ⟨h6, h5⟩
    have hb5 : ¬ 5 ∣ b0 := fun h6 => hbc' ⟨h6, h5⟩
    rw [vb, vc, padicValNat.eq_zero_of_not_dvd hb5] at hbc
    have hmod : padicValNat 5 c0 ≡ 0 [MOD K] :=
      Nat.ModEq.add_right_cancel' s (by simpa [Nat.ModEq] using hbc.symm)
    have hKd : K ∣ padicValNat 5 c0 := (Nat.modEq_zero_iff_dvd).mp hmod
    have hge : 1 ≤ padicValNat 5 c0 := one_le_padicValNat_of_dvd hc0pos.ne' h5
    have := bound_aux K _ g c0 c0 c hKd hge (pow_padicValNat_dvd) hc0pos le_rfl hc0 hg
    omega

/-- Exact threshold for the colouring `n ↦ v_5(n) mod K`. -/
theorem threshold (K : ℕ) (hK : 0 < K) :
    (∀ F : ℕ → Fin K, ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ c ≤ 5 ^ K ∧
      F (padicValNat 5 a) = F (padicValNat 5 b) ∧ F (padicValNat 5 b) = F (padicValNat 5 c)) ∧
    (∀ a b c : ℕ, 0 < a → 0 < b → a ^ 2 + b ^ 2 = c ^ 2 → c < 5 ^ K →
      ¬ (padicValNat 5 a % K = padicValNat 5 b % K ∧ padicValNat 5 b % K = padicValNat 5 c % K)) :=
  ⟨upper K hK, fun a b c ha hb h hc => lower K hK a b c ha hb h hc⟩

end Pyth5

#print axioms Pyth5.threshold
