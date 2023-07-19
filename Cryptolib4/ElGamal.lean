/-
 -----------------------------------------------------------
  Correctness and semantic security of ElGamal public-key 
  encryption scheme
 -----------------------------------------------------------
-/

import Cryptolib4.DDH
import Cryptolib4.PKE
import Cryptolib4.Tactics
import Cryptolib4.ToMathlib
import Cryptolib4.Uniform

noncomputable section ElGamal 

variable (G : Type) [Fintype G] [CommGroup G] [DecidableEq G] 
           (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
           (q : ℕ) [Fact (0 < q)] [NeZero q](G_card_q : Fintype.card G = q) 
           (A_state : Type) (A1 : G → Pmf (G × G × A_state))
           (A2 : G → G → A_state → Pmf (ZMod 2))

def A2' : G × G → A_state → Pmf (ZMod 2) := λ (gg : G × G) => A2 gg.1 gg.2 

-- From Lupo: Generates a public key `g^x.val`, and private key `x`
def keygen : Pmf (G × (ZMod q)) := 
  do 
    let x ← uniform_zmod q
    pure (g^x.val, x)


-- From Lupo: encrypt takes a pair (public key, message)
def encrypt (pk m : G) : Pmf (G × G) := 
  do
    let y ← uniform_zmod q
    pure (g^y.val, pk^y.val * m)

-- From Lupo: `x` is the secret key, `c.1` is g^y, the first part of the 
-- cipher text returned from encrypt, and `c.2` is the 
-- second value returned from encrypt
def decrypt (x : ZMod q) (c : G × G) : G := (c.2 / (c.1^x.val)) 
#check decrypt

/- 
  -----------------------------------------------------------
  Proof of correctness of ElGamal
  -----------------------------------------------------------
-/

lemma decrypt_eq_m (m : G) (x y : ZMod q) : decrypt G q x ((g^y.val), ((g^x.val)^y.val * m)) = m := by 
  simp [decrypt]
  rw [(pow_mul g x.val y.val).symm]
  rw [(pow_mul g y.val x.val).symm]
  rw [mul_comm y.val x.val]
  simp

theorem elgamal_correctness : pke_correctness (keygen G g q) (encrypt G g q) (decrypt G q) := by 
  simp [pke_correctness]
  intro m 
  simp [enc_dec, keygen, encrypt, bind]
  bind_skip_const
  simp [pure]
  bind_skip_const 
  simp_rw [decrypt_eq_m]
  simp 
  
/- 
  -----------------------------------------------------------
  Proof of semantic security of ElGamal
  -----------------------------------------------------------
-/