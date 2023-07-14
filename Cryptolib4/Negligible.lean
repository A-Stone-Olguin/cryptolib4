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

#check lt_of_lt_of_le

example (n m x: ℝ) (hnm : n < m) (hmx : m < x) : n < x := by exact gt_trans hmx hnm
-- example (n m x: ℝ) (hnm : n < m) (hmx : m < x) : c > 0 → m * c = n *c → m= n  := by apply?
example (n m x y: ℝ) (hnm : n ≤ m ) :n * x ≤ m * x := by refine Iff.mpr (mul_le_mul_right ?a0) hnm 
example (n : ℕ) (c : ℕ) (hc : c > 0) (hn : n > 0) (hcn0 : c ≠ 0): n^(c+1) = n * n^c := by exact Nat.pow_succ'
example (n : ℝ) (c : ℝ) (hn : n > 0) : n^(c+1) = n^c * n := by
  apply Real.rpow_add_one (ne_of_gt hn)

example (n : ℝ) (c : ℝ) (hn : n ≥ 2) : n^(c+1) = n^c * n := by
  apply Real.rpow_add_one (ne_of_gt (lt_of_lt_of_le  two_pos hn))

   


example (n c : ℝ) (hn : n > 0) (hc : c > 0): 1/n = 1/c → n = c :=by 
  intro h 
  simp at h
  exact h

example (n c : ℝ) (hn : n > 0) (hc : c > 0): n=c → 1/n = 1/c :=by 
  intro h
  simp 
  exact h

example (n : ℝ) (c : ℝ) (hn : n > 0) : 1/n^(c+1) = 1/n^c * 1/n^1 := by
  ring_nf
  apply Real.rpow_neg

example (n : ℝ) (hn :n > 0) (hpos :  0 < (n^c)): 0 < (n^c)⁻¹  := by exact Iff.mpr inv_pos hpos

#check Real.rpow_add
#check Real.rpow_neg
#check one_div_pow
#check Real.mul_pos
#check Real.rpow_inv_le_iff_of_neg
#check Real.rpow_pos_of_pos
#check Nat.cast_div

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
  have h1 : nf ≤ n := by 
    have h := le_max_left nf ng 
    trans 
    exact h
    trans
    exact tn 
    exact hn 
  have h2 : ng ≤ n := by
    have h := le_max_right nf ng 
    trans 
    exact h
    trans
    exact tn 
    exact hn 
  specialize hnf n h1 
  specialize hng n h2 
  have h_add : abs (f n) + abs (g n) < 2 / ↑n^(c + 1) := calc
    abs (f n) + abs (g n) < 1 / ↑n ^ (c + 1) + 1 / ↑n ^ (c + 1) := by exact add_lt_add hnf hng
                        _ = 2 / ↑n ^ (c + 1) := by ring_nf
  have h_fg_add :abs ((f + g) n) = abs (f n + g n) := by exact rfl
  rw [h_fg_add]
  apply gt_of_gt_of_ge _ (abs_add (f n) (g n))
  apply gt_of_ge_of_gt _ h_add
  have h : n ≥ 2 := by 
    apply le_trans _ hn 
    apply le_max_right 
  have hlt :  1/n ≤ 1/2 := by refine Nat.div_le_div_left h two_pos 
  have hltr : 1 / (n: ℝ) ≤ 1 / 2  := by
    
    sorry
  have hnc : n^(c+1) = n^c * n := by 
    apply Real.rpow_add_one
    apply ne_of_gt 
    norm_cast 
    exact lt_of_lt_of_le two_pos h
  have h2pos :  0 < 2 / ↑n ^ c := by 
    have hinv : 2/(n^c) = 2 * (n^c)⁻¹ := rfl 
    rw [hinv]
    apply Real.mul_pos two_pos 
    apply (inv_pos).mpr 
    apply Real.rpow_pos_of_pos
    apply lt_of_lt_of_le two_pos
    norm_cast
  have hltc2 : 2/n^(c+1) ≤ 1/n^c := calc 
    2 / n^(c+1) = 2 / (n^c * n) := by rw [hnc]
              _ = 2 / n^c * 1 / n  := by ring_nf
              _ ≤ 2 / n^c * 1/2 := by apply Iff.mpr (mul_le_mul_left _); simp at hltr; exact hltr; simp; exact h2pos
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
    rw [abs_mul]
    rw [abs_mul]
    exact mul_le_mul h (Eq.le rfl) (abs_nonneg (f n)) (abs_nonneg ↑k)

theorem neg_exp_negl : negligible ((λ n => (1 : ℝ) / 2^n) : ℕ → ℝ) := by 
    sorry
  