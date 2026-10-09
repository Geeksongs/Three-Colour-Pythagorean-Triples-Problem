import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Proofs.Data
import Proofs.Euclid

/-!
Strict statement: the explicit 3-colouring `col` of {1..N}, N = 25,000,000 (bytes in `Pyth.dataStr`)
has no monochromatic Pythagorean triple a^2 + b^2 = c^2 with c ≤ N.

Proof structure
* `okAll` is a computable Boolean check over Euclid parameters (m, n, t) with gcd m n = 1.
* `okAll_sound`: okAll = true → no monochromatic triple (uses Mathlib's `PythagoreanTriple.classification`).
* `okAll_true`: okAll = true by `native_decide` (adds the axiom `Lean.ofReduceBool`).
-/

namespace Pyth

def bytes : ByteArray := dataStr.toUTF8

/-- colour of vertex `v` (1-indexed). -/
def col (v : ℕ) : UInt8 := bytes.get! (v - 1)

def N : ℕ := 25000000

def okTriple (m n t : ℕ) : Bool :=
  !(col (t * (m * m - n * n)) == col (t * (2 * m * n)) &&
    col (t * (2 * m * n)) == col (t * (m * m + n * n)))

def okMN (m n : ℕ) : Bool :=
  if 0 < n ∧ n < m ∧ Nat.gcd m n = 1 then
    (List.range (N / (m * m + n * n) + 1)).all fun t => decide (t = 0) || okTriple m n t
  else true

def okAll : Bool :=
  (List.range 5001).all fun m => (List.range m).all fun n => okMN m n

/-- all bytes are the characters '0', '1', '2' and there are exactly N of them. -/
def validData : Bool :=
  decide (bytes.size = N) &&
    (List.range N).all fun i => decide (bytes.get! i = 48 ∨ bytes.get! i = 49 ∨ bytes.get! i = 50)

theorem okAll_true : okAll = true := by native_decide

theorem validData_true : validData = true := by native_decide

/-- Natural-number core: Euclid parameters give no monochromatic triple. -/
theorem key (h : okAll = true) (K M n : ℕ) (hK : 0 < K) (hn : 0 < n) (hnM : n < M)
    (hg : Nat.gcd M n = 1) (hc : K * (M * M + n * n) ≤ N) :
    ¬ (col (K * (M * M - n * n)) = col (K * (2 * M * n)) ∧
       col (K * (2 * M * n)) = col (K * (M * M + n * n))) := by
  have hM : M < 5001 := by
    by_contra hM
    have h1 : 5001 * 5001 ≤ M * M := Nat.mul_le_mul (by omega) (by omega)
    have h2 : M * M ≤ K * (M * M + n * n) := by nlinarith
    have : N = 25000000 := rfl
    omega
  have h1 : okMN M n = true := by
    unfold okAll at h
    simp only [List.all_eq_true, List.mem_range] at h
    exact h M hM n hnM
  have hKle : K < N / (M * M + n * n) + 1 := by
    have hpos : 0 < M * M + n * n := by nlinarith
    have : K ≤ N / (M * M + n * n) := (Nat.le_div_iff_mul_le hpos).2 (by linarith)
    omega
  unfold okMN at h1
  rw [if_pos ⟨hn, hnM, hg⟩] at h1
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h1
  rcases h1 K hKle with h0 | h2
  · omega
  · unfold okTriple at h2
    intro ⟨e1, e2⟩
    simp [e1, e2] at h2

/-- Soundness: if the Boolean check passes, there is no monochromatic Pythagorean triple. -/
theorem sound (h : okAll = true) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (habc : a * a + b * b = c * c) (hc : c ≤ N) :
    ¬ (col a = col b ∧ col b = col c) := by
  obtain ⟨K, M, n, hK, hn, hnM, hg, hcK, hab⟩ := euclid_nat a b c ha hb habc
  have hle : K * (M * M + n * n) ≤ N := hcK ▸ hc
  have hk := key h K M n hK hn hnM hg hle
  rintro ⟨e1, e2⟩
  rw [hcK] at e2
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hk ⟨e1, e2⟩
  · exact hk ⟨e1.symm, e1.trans e2⟩

/-- Main theorem: the colouring given by `dataStr` has no monochromatic Pythagorean triple
    with hypotenuse ≤ 25,000,000, and uses only the three colours '0','1','2'. -/
theorem main :
    validData = true ∧
    ∀ a b c : ℕ, 0 < a → 0 < b → a * a + b * b = c * c → c ≤ N →
      ¬ (col a = col b ∧ col b = col c) :=
  ⟨validData_true, fun a b c ha hb h hc => sound okAll_true a b c ha hb h hc⟩

end Pyth
