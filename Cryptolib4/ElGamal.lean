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

variable (G : Type) [inst_1 : Fintype G] [inst_2 : CommGroup G] [inst_3 : DecidableEq G] 
           (g : G) (g_gen_G : ∀ (x : G), x ∈ Subgroup.zpowers g)
           (q : ℕ) [inst_4 : Fact (0 < q)] [inst_5 : NeZero q](G_card_q : Fintype.card G = q) 
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

def D (gx gy gz : G) : Pmf (ZMod 2) := 
  do 
    let m ← A1 gx 
    let b ← uniform_2
    let mb ← pure (if b = 0 then m.1 else m.2.1)
    let b' ← A2 gy (gz * mb) m.2.2
    pure (1 + b + b')  

/- From Lupo: 
  The probability of the attacker (i.e. the composition of A1 and A2) 
  winning the semantic security game (i.e. guessing the correct bit), 
  w.r.t. ElGamal is equal to the probability of D winning the game DDH0. 
-/
theorem SSG_DDH0 : SSG (keygen G g q) (encrypt G g q) A1 (A2' G A_state A2) = DDH0 G g q (D G A_state A1 A2) := by 
  simp only [SSG, DDH0, bind, keygen, encrypt, D]
  simp_rw [Pmf.bind_bind (uniform_zmod q)]
  bind_skip
  simp [pure]
  simp_rw [Pmf.bind_comm (uniform_zmod q)]
  simp only [A2']
  repeat bind_skip
  rw [pow_mul g _ _]

def Game1 : Pmf (ZMod 2) := 
  do 
    let x ← uniform_zmod q 
    let y ← uniform_zmod q
    let m ← A1 (g^x.val)
    let b ← uniform_2 
    let ζ ← (do let z ← uniform_zmod q; let mb ← pure (if b = 0 then m.1 else m.2.1); pure (g^z.val * mb))
    let b' ← A2 (g^y.val) ζ m.2.2 
    pure (1 + b + b')  

def Game2 : Pmf (ZMod 2) := 
  do 
    let x ← uniform_zmod q 
    let y ← uniform_zmod q
    let m ← A1 (g^x.val)
    let b ← uniform_2 
    let ζ ← (do let z ← uniform_zmod q; pure (g^z.val))
    let b' ← A2 (g^y.val) ζ m.2.2 
    pure (1 + b + b') 

/- From Lupo: 
  The probability of the attacker (i.e. the composition of A1 and A2) 
  winning Game1 (i.e. guessing the correct bit) is equal to the 
  probability of D winning the game DDH1. 
-/
theorem Game1_DDH1 : Game1 G g q A_state A1 A2 = DDH1 G g q (D G A_state A1 A2) := by 
  simp only [DDH1, Game1, bind, D]
  repeat bind_skip 
  simp_rw [Pmf.bind_bind (A1 _)]
  rw [Pmf.bind_comm (uniform_zmod q)]
  simp_rw [Pmf.bind_bind (uniform_zmod q)]
  repeat bind_skip 
  rw [Pmf.bind_comm (uniform_2)]
  bind_skip
  rw [Pmf.bind_bind (uniform_2)]
  simp_rw [Pmf.bind_bind]
  repeat bind_skip 
  simp [pure]

#check ZMod.val_cast_of_lt
lemma exp_bij : Function.Bijective (λ (z : ZMod q) => g^z.val) := by 
  apply (Fintype.bijective_iff_surjective_and_card _).mpr 
  apply And.intro
  · -- surjective 
    intro gz 
    have hz := Subgroup.mem_zpowers_iff.mp (g_gen_G gz)
    cases hz with
    | intro z hz => 
    cases z with
    | ofNat z => 
      let zq := z % q 
      use zq 
      have h1 : (λ (z : ZMod q) => g^z.val) zq = g^ (zq : ZMod q).val := rfl 
      rw [h1]
      rw [ZMod.val_cast_of_lt] 
      · 
        simp_rw [← hz]
        have hnat : g^ Int.ofNat z = g^z := by simp
        rw [hnat, ← Nat.mod_add_div z q, pow_add, pow_mul, ← G_card_q]
        simp [pow_card_eq_one]
      · exact Nat.mod_lt z inst_4.out
    | negSucc z => 
      sorry
  · -- injective 
    rw [G_card_q]
    exact ZMod.card q