/-
 -----------------------------------------------------------
  The Decisional Diffie-Hellman assumption as a security game
 -----------------------------------------------------------
-/


import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Cryptolib4.ToMathlib
import Cryptolib4.Uniform

noncomputable section

section DDH

variable (G : Type) [Fintype G] [Group G]
          (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g) 
          (q : ℕ) [Fact (0 < q)] [NeZero q] (G_card_q : Fintype.card G = q) 
          (D : G → G → G → Pmf (ZMod 2))

def DDH0 : Pmf (ZMod 2) := 
  do
    let x ← uniform_zmod q
    let y ← uniform_zmod q 
    let b ← D (g^x.val) (g^y.val) (g^(x.val*y.val))
    pure b

def DDH1 : Pmf (ZMod 2) := 
  do
    let x ← uniform_zmod q
    let y ← uniform_zmod q 
    let z ← uniform_zmod q 
    let b ← D (g^x.val) (g^y.val) (g^z.val)
    pure b

-- -- From Lupo: DDH0(D) is the event that D outputs 1 upon receiving (g^x, g^y, g^(xy))
local notation "Pr[DDH0("D")]" => (DDH0 G g g_gen_G q G_card_q D 1 : ℝ)
-- -- From Lupo: DDH1(D) is the event that D outputs 1 upon receiving (g^x, g^y, g^z)
local notation "Pr[DDH1("D")]" => (DDH1 G g g_gen_G q G_card_q D 1 : ℝ)

-- def DDH (ε : nnreal) : Prop := abs (Pr[DDH0(D)] - Pr[DDH1(D)]) ≤ ε

end DDH