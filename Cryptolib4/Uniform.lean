import Cryptolib4.ToMathlib
import Mathlib.Probability.ProbabilityMassFunction.Uniform
import Mathlib.Data.ZMod.Defs

variable (G : Type) [Fintype G] [Group G] [DecidableEq G]

noncomputable section

-- Instance doesn't transfer across import?
instance : ∀ (n : ℕ), Fintype (Bitvec n) := by 
  intro n; exact Vector.fintype

def uniform_bitvec (n : ℕ) : Pmf (Bitvec n) := 
  Pmf.ofMultiset (instForAllNatFintypeBitvec n).elems.val (Bitvec.multiset_ne_zero n)

def uniform_group : Pmf G := 
  Pmf.ofMultiset (@Fintype.elems G).val (Group.multiset_ne_zero G)


-- Need a proof that 2 is positive
instance : Fact (0 < 2) where
  out := two_pos

-- We have that n is positive and not equal to zero...
def uniform_zmod (n : ℕ) [Fact (0 < n)] [NeZero n] : Pmf (ZMod n) := uniform_group (ZMod n)
def uniform_2 : Pmf (ZMod 2) := uniform_zmod 2 

-- Had to modify from NNReal to ENNReal
lemma uniform_group_prob : 
  ∀ (g : G), (uniform_group G) g = 1 / Multiset.card (@Fintype.elems G).val := by 
  intro g 
  
  have h1 : (uniform_group G)= (λ (a : G) => 
    (Multiset.count a (@Fintype.elems G).val : ENNReal) / Multiset.card (@Fintype.elems G).val) := by 
    ext
    simp [uniform_group, Pmf.ofMultiset]
    sorry
  have h2 : (uniform_group G) g = 
    Multiset.count g (@Fintype.elems G).val / Multiset.card (@Fintype.elems G).val := congr_fun h1 g
  rw [h2]
  have h3 : Multiset.count g (@Fintype.elems G).val = 1 := Multiset.count_univ g 
  rw [h3]
  simp

lemma uniform_zmod_prob {n : ℕ} [Fact (0 < n)] [NeZero n] : ∀ (a : ZMod n), (uniform_zmod n) a = 1/n := by
  intro a 
  simp [uniform_zmod]
  have h1 := uniform_group_prob (ZMod n) a
  have h2 : Multiset.card (@Fintype.elems (ZMod n)).val = n := ZMod.card n
  rw [h2] at h1
  rw [inv_eq_one_div]
  exact h1 
