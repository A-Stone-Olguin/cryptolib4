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

lemma bind_skip_cons' (pa : Pmf α) (pb : Pmf β) (f : α → Pmf β) : 
  (∀ (a : α), f a = pb) → pa.bind f = pb := by 
    intro ha 
    ext 
    simp 
    simp_rw [ha]
    simp [NNReal.tsum_mul_right]

    sorry

def Tactic.Interactive.bind_skip (x : parse (TK "with" *> Ident)?) : Tactic Unit := 
  do `[apply bind_skip'] 
    let a := x.get_or_else `_ 
    Tactic.Interactive.intro a