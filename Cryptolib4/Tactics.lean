import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

variable {α β : Type}

lemma bind_skip' (p : Pmf α) (f g : α → Pmf β) :
  (∀ (a : α), f a = g a) → p.bind f = p.bind g := by 
    intro ha 
    ext 
    simp 
    simp_rw [ha]

lemma bind_skip_const' (pa : Pmf α) (pb : Pmf β) (f : α → Pmf β) : 
  (∀ (a : α), f a = pb) → pa.bind f = pb := by 
    intro ha 
    ext 
    simp 
    simp_rw [ha]
    simp [ENNReal.tsum_mul_right]


syntax "bind_skip" : tactic 

macro_rules 
  | `(tactic| bind_skip) => `(tactic| apply bind_skip' <;> intro a)

syntax "bind_skip_const" : tactic 

macro_rules 
  | `(tactic| bind_skip_const) => `(tactic| apply bind_skip_const' <;> intro a)