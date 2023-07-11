import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

/- From Lupo:
  A function f : ℤ≥1 → ℝ is called negligible if 
  for all c ∈ ℝ>0 there exists n₀ ∈ ℤ≥1 such that 
  n₀ ≤ n →  |f(n)| < 1/n^c
-/

def negligible (f : ℕ → ℝ) := 
  ∀ c > 0, ∃ n₀, ∀ n, n₀ ≤ n → abs (f n) < 1 / (n : ℝ)^c

def negligible' (f : ℕ → ℝ) := 
  ∀ (c : ℝ), ∃ (n₀ : ℕ), ∀ (n : ℕ),
  0 < c → n₀ ≤ n → abs (f n) < 1 / n^c 

example  (n k₀ : ℕ):(n : ℝ)^(k₀ : ℝ) = (n : ℝ)^k₀ := by exact?
example (c : ℕ) (hc : c > 0): 0 < c := by exact?

lemma negl_equiv (f : ℕ → ℝ) : negligible f ↔ negligible' f := by 
  apply Iff.intro 
  -- → case
  · intro h c
    have arch := exists_nat_gt c
    cases arch with 
    | intro k hk => 
    let k₀ := max k 1
    have k_leq_k₀ : k ≤ k₀ := le_max_left k 1
    have kr_leq_k₀r : (k : ℝ) ≤ k₀ := Nat.cast_le.mpr k_leq_k₀
    have k₀_pos : 0 < k₀ := le_max_right k 1
    have a := h k₀ (Iff.mpr Nat.cast_pos k₀_pos) 
    cases a with
    | intro n' hn₀ => 
    let n₀ := max n' 1 
    have n₀_pos : 0 < n₀ := le_max_right n' 1
    have n'_leq_n₀ : n' ≤ n₀ := le_max_left n' 1 
    use n₀ 
    intro n c_pos hn 
    have hnnn : n' ≤ n := by linarith
    have b : (n : ℝ)^c ≤ (n:ℝ)^(k₀ : ℝ) := 
      by apply Real.rpow_le_rpow_of_exponent_le <;> norm_cast <;> repeat linarith
    have daf : (n : ℝ)^(k₀ : ℝ) = (n : ℝ)^k₀ := rfl
    rw [daf] at b
    have d : 1/ (n : ℝ)^k₀ ≤1 / n^c := by 
      apply one_div_le_one_div_of_le
      · apply Real.rpow_pos_of_pos 
        norm_cast
        linarith 
      · assumption
    have goal : abs (f n) < 1 / n^c := calc 
      abs (f n) < 1 / (n : ℝ)^k₀ := by exact hn₀ n hnnn
              _ ≤ 1 / n^c := d 
    exact goal
  -- ← case
  · intro h c hc 
    cases h c with
    | intro n₀ hn₀ => 
    use n₀ 
    intro n hn
    exact hn₀ n hc hn