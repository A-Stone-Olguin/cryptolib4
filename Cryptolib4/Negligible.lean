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
    intro n _ hn 
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

lemma zero_negl : negligible (λ _ => 0) := by 
  intro c _ 
  use 1 
  intro n hn 
  norm_num
  have npos : n > 0 := by linarith
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr npos) c

#check Nat.cast_le.mpr

lemma negl_add_negl_negl {f g : ℕ → ℝ} : negligible f → negligible g → negligible (f + g) := by 
  intro hf hg c hc
  have hc1 : 0 < (c + 1)  := add_pos hc one_pos
  have hf2 := hf (c+1) hc1
  have hg2 := hf (c+1) hc1
  cases hf2 with
  | intro nf hnf => 
  cases hg2 with
  | intro ng hng => 
  let n₀ := max (max nf ng) 2
  use n₀ 
  intros n hn 
  let nr := (n : ℝ)
  have n_eq_nr : (n : ℝ) = nr := rfl 

  have tn : max nf ng ≤ n₀ := le_max_left (max nf ng) 2 
  have t2n₀ : 2 ≤ n₀ := le_max_right (max nf ng) 2 
  have t2n : 2 ≤ n := by linarith 
  have t2nr : 2 ≤ nr := by 
    rw [← n_eq_nr]
    exact Nat.cast_le.mpr t2n
  have tnr_pos : 0 < nr := by linarith 

  have t2na : (1 / nr) * (1/ nr^c) ≤ (1 / (2 : ℝ)) * (1 / nr^c) := by
    have ht2 : 0 < (1 / nr^c) := by apply one_div_pos.mpr; exact Real.rpow_pos_of_pos tnr_pos c
    apply (mul_le_mul_right ht2).mpr 
    exact Iff.mpr (one_div_le_one_div tnr_pos two_pos) t2nr
  have tnr2 : 1 / nr^(c+1) ≤(1 / (2: ℝ)) * (1 / nr^c) := by 
    sorry 
  have tnf : nf ≤ n := by 
    sorry
  have tfn := hnf n tnf
  have tf : abs (f n) < (1 / (2 : ℝ)) * (1 / nr^c) := by linarith 

  have tng : ng ≤ n := by 
    sorry 
  have tgn := hng n tng 
  have tg : abs (g n) < (1 / (2 : ℝ)) * (1 /nr^c) := by sorry 

  sorry



lemma bounded_negl_negl {f g : ℕ → ℝ} (hg : negligible g): (∀ n, abs (f n) ≤ abs (g n)) → negligible f := by 
  intro h c hc
  cases (hg c hc) with
  | intro n₀ hn₀ => 
  use n₀ 
  intro n hn 
  exact gt_of_gt_of_ge (hn₀ n hn) (h n)

lemma nat_mul_negl_negl {f : ℕ → ℝ} (m : ℕ) : negligible f → negligible (λ n => m * (f n)) := by 
  intro hf 
  induction m with
  | zero => norm_num; exact zero_negl
  | succ k ih => 
    norm_num 
    have d : (λn => ((k : ℝ) + 1) * (f n)) = (λn => (k : ℝ) * (f n)) + (λn => f n) := by 
      ring_nf
      rfl
    rw [d]
    exact negl_add_negl_negl ih hf

example (n k c: ℝ) (h : abs n ≤ abs k  ) : abs (n *c) ≤ abs (k * c) := by 
  apply abs_le_abs

lemma const_mul_negl_negl  {f : ℕ → ℝ} (m : ℝ) : negligible f → negligible (λ n => m * (f n)) := by 
  intro hf 
  have arch := exists_nat_gt (abs m)
  cases arch with
  | intro k hk => 
  apply bounded_negl_negl
  · exact nat_mul_negl_negl k hf 
  · intro n
    have h : abs m ≤ abs (k : ℝ) := by refine Iff.mpr le_iff_lt_or_eq ?_; left; simp; exact hk 
    rw [abs_mul]
    rw [abs_mul]
    exact mul_le_mul h (Eq.le rfl) (abs_nonneg (f n)) (abs_nonneg ↑k)

theorem neg_exp_negl : negligible ((λ n => (1 : ℝ) / 2^n) : ℕ → ℝ) := by 
    sorry
  