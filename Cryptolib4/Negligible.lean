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

lemma zero_negl : negligible (λ _ => 0) := by 
  intro c _ 
  use 1 
  intro n hn 
  norm_num
  have npos : n > 0 := by linarith
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr npos) c

lemma negl_add_negl_negl {f g : ℕ → ℝ} : negligible f → negligible g → negligible (f + g) := by 
  intro hf hg c hc 
  have hc1 : 0 < (c + 1) := add_pos hc one_pos
  cases (hf (c + 1) hc1) with
  | intro nf hnf =>
  cases (hg (c + 1) hc1) with
  | intro ng hng =>
  let n₀ := max (max nf ng) 2 
  use n₀ 
  intro n hn
  have tn : max nf ng ≤ n₀ := le_max_left (max nf ng) 2 
  have h1 : nf ≤ n := le_trans (le_max_left nf ng) (le_trans tn hn) 
  have h2 : ng ≤ n := le_trans (le_max_right nf ng) (le_trans tn hn) 
  specialize hnf n h1 
  specialize hng n h2 
  have h_add : abs (f n) + abs (g n) < 2 / ↑n^(c + 1) := calc
    abs (f n) + abs (g n) < 1 / ↑n ^ (c + 1) + 1 / ↑n ^ (c + 1) := by exact add_lt_add hnf hng
                        _ = 2 / ↑n ^ (c + 1) := by ring_nf
  have h_fg_add :abs ((f + g) n) = abs (f n + g n) := by exact rfl
  rw [h_fg_add]
  apply gt_of_gt_of_ge (gt_of_ge_of_gt _ h_add) (abs_add (f n) (g n))
  
  have h : n ≥ 2 := by 
    apply le_trans _ hn 
    apply le_max_right 
  have hltr : 1 / (n: ℝ) ≤ 1 / 2  := by
    have hnrge2 : (n : ℝ) ≥ 2 := (Nat.cast_le).mpr h 
    exact (one_div_le_one_div (lt_of_lt_of_le two_pos hnrge2) two_pos).mpr hnrge2
  have hnc : n^(c+1) = n^c * n := by 
    apply Real.rpow_add_one
    apply ne_of_gt 
    norm_cast 
    exact lt_of_lt_of_le two_pos h
  have h2pos :  0 < 2 / ↑n ^ c := by 
    have hinv : 2/(n^c) = 2 * (n^c)⁻¹ := rfl 
    rw [hinv]
    apply Real.mul_pos two_pos 
    apply (inv_pos).mpr (Real.rpow_pos_of_pos (lt_of_lt_of_le two_pos _) _)
    norm_cast
  have hltc2 : 2/n^(c+1) ≤ 1/n^c := calc 
    2 / n^(c+1) = 2 / (n^c * n) := by rw [hnc]
              _ = 2 / n^c * 1 / n  := by ring_nf
              _ ≤ 2 / n^c * 1/2 := by apply (mul_le_mul_left _).mpr; simp at hltr; exact hltr; rw [mul_one]; exact h2pos
              _ = 1 / n^c := by ring_nf

  have goal : 1 / ↑n ^ c ≥ 2 / ↑n ^ (c + 1) := by 
    apply le_trans hltc2 
    rfl
  exact goal



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

lemma const_mul_negl_negl  {f : ℕ → ℝ} (m : ℝ) : negligible f → negligible (λ n => m * (f n)) := by 
  intro hf 
  have arch := exists_nat_gt (abs m)
  cases arch with
  | intro k hk => 
  apply bounded_negl_negl
  · exact nat_mul_negl_negl k hf 
  · intro n
    have h : abs m ≤ abs (k : ℝ) := by refine Iff.mpr le_iff_lt_or_eq ?_; left; simp; exact hk 
    repeat rw [abs_mul]
    exact mul_le_mul h (Eq.le rfl) (abs_nonneg (f n)) (abs_nonneg ↑k)

theorem neg_exp_negl : negligible ((λ n => (1 : ℝ) / 2^n) : ℕ → ℝ) := by 
  sorry
--   intro c hc
--   have h : (0 < c ∧ c < 1) ∨ 1 ≤ c := by 
--     apply Decidable.or_iff_not_imp_right.mpr
--     intro hnot 
--     exact And.intro hc (not_le.mp hnot)
--   cases h with
--   | inl h => 
--     cases h with
--     | intro left right => 
--     use 2 
--     intro n hn 
--     simp
--     have hinv : 0 < ((2^n: ℝ))⁻¹ := by 
--       apply inv_pos.mpr 
--       norm_num
--     have h_abs_pos : abs ((2 ^ n : ℝ) )⁻¹ = ((2 ^ n:ℝ))⁻¹ := abs_of_pos hinv 
--     rw [abs_of_pos]
--     apply (inv_lt_inv _ _ ).mpr
--     · induction n with
--     | zero => 
--       norm_cast
--     | succ n ih => 
--       sorry 
--     · norm_num
--     · apply Real.rpow_pos_of_pos
--       norm_cast
--       exact lt_of_lt_of_le two_pos hn
--     · norm_num

--   | inr h => 
--     use 1 
--     intro n hn
--     simp
--     have h_abs_pos : abs ((2 ^ n : ℝ) )⁻¹ = ((2 ^ n:ℝ))⁻¹ := abs_of_pos hinv 
--     rw [abs_of_pos]
--     apply (inv_lt_inv _ _ ).mpr
--     induction n with
--     | zero => contradiction
--     | succ n ih => 
--       sorry

--   -- have h_or : 0 < c < 1 ∨ 1 < c := by sorry



--   have arch := exists_nat_gt c 
--   cases arch with
--   | intro m hm => 


--   let n₀ := 2^(Nat.succ m)
--   use n₀ 
--   intro n hn 
--   -- simp
--   have hle : 2^(Nat.succ m) ≤ n := hn 
--   have n₀pos : 0 < 2^(Nat.succ m) := Fin.size_positive'
--   have h : 0 ≤ 2^(Nat.succ m) := by exact Nat.zero_le (2 ^ Nat.succ m)
--   have hexp : 2^(2^(Nat.succ m)) ≤ 2^n := (Nat.pow_le_iff_le_right Nat.AtLeastTwo.prop).mpr hn
--   have hlec : (2^(Nat.succ m))^c ≤ n^c := by 
--     apply Iff.mpr (Real.rpow_le_rpow_iff ?hx ?hy hc) ?_
--     norm_cast
--     norm_cast 
--     exact le_trans h hn
--     norm_cast
--   have hcomp : (2 ^ ↑(Nat.succ m)) ^ c < 2 ^ 2 ^ Nat.succ m := by 
--     have h : (2 ^ ↑(Nat.succ m)) ^ c = (2 ^ (c*↑(Nat.succ m))) := by 
--       rw [← Real.rpow_mul zero_le_two]
--       ring_nf
--     rw [h]
--     apply Real.rpow_lt_rpow_of_exponent_lt one_lt_two
--     sorry
--   -- have h : n^c  < 2^(2^(Nat.succ m)) := by 
--   --   norm_num 
--   --   sorry
  


--   sorry

-- #check Real.rpow_lt_rpow_iff
-- #check Real.rpow_le_rpow_of_exponent_le
-- #check Real.rpow_lt_rpow_of_exponent_lt
-- example (x y z: ℝ ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hl : y < z) : x^y < x^z := sorry
  