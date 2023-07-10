import Cryptolib4.ToMathlib
import Mathlib.Probability.ProbabilityMassFunction.Uniform

variable (G : Type) [Fintype G] [Group G] [DecidableEq G]

noncomputable section

-- Instance doesn't transfer across import?
instance : ∀ (n : ℕ), Fintype (Bitvec n) := by 
  intro n; exact Vector.fintype

def uniform_bitvec (n : ℕ) : Pmf (Bitvec n) := 
  Pmf.ofMultiset (instForAllNatFintypeBitvec n).elems.val (Bitvec.multiset_ne_zero n)

def uniform_group : Pmf G := 
  Pmf.ofMultiset (@Fintype.elems G).val (Group.multiset_ne_zero G)

-- Need Group instance of ZMod for this definition
-- def uniform_zmod (n : ℕ) [Fact (0 < n)] : Pmf (ZMod n) := uniform_group (ZMod n)
-- def uniform_2 : Pmf (ZMod 2) := uniform_zmod 2

#check congr_fun

lemma uniform_group_prob : 
  ∀ (g : G), (uniform_group G) g = 1 / Multiset.card (@Fintype.elems G).val := by 
  intro g 
  have h1 : ↑(uniform_group G) = (λ (a : G) => 
    (Multiset.count a (@Fintype.elems G).val : NNReal) / Multiset.card (@Fintype.elems G).val) := by 
    
    sorry
  have h2 : (uniform_group G) g = 
    Multiset.count g (@Fintype.elems G).val / Multiset.card (@Fintype.elems G).val := by 
      -- exact congr_fun h1 g
      sorry
    
  rw [h2]
  have h3 : Multiset.count g (@Fintype.elems G).val = 1 := Multiset.count_univ g 
  rw [h3]
  simp

  -- TODO need to add instance of uniform group for ZMod