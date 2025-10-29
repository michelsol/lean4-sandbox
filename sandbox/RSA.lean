import Sandbox.NthDigit

namespace RSA

structure KeyPair where
  p : ℕ
  hp : p.Prime
  q : ℕ
  hq : q.Prime
  hpq : p.Coprime q
  e : ℕ
  he1 : 1 < e
  he2 : e < (p - 1) * (q - 1)
  he3 : e.Coprime ((p - 1) * (q - 1))

structure PublicKey where
  e : ℕ
  n : ℕ

structure PrivateKey where
  d : ℕ
  n : ℕ

namespace KeyPair

def n (keys : KeyPair) := keys.p * keys.q

def φ (keys : KeyPair) := (keys.p - 1) * (keys.q - 1)

def d (keys : KeyPair) := (keys.e : ZMod keys.φ)⁻¹.val

def toPublicKey (keys : KeyPair) : PublicKey := ⟨keys.e, keys.n⟩

def toPrivateKey (keys : KeyPair) : PrivateKey := ⟨keys.d, keys.n⟩

def symm (keys : KeyPair) : KeyPair :=
  { p := keys.q
    hp := keys.hq
    q := keys.p
    hq := keys.hp
    hpq := Nat.Coprime.symm keys.hpq
    e := keys.e
    he1 := keys.he1
    he2 := by convert keys.he2 using 1; ring
    he3 := by convert keys.he3 using 1; ring
  }

end KeyPair

def encryptBlock (key : PublicKey) (m : ℕ) := m ^ key.e % key.n

def decryptBlock (key : PrivateKey) (c : ℕ) := c ^ key.d % key.n

theorem encryptBlock_eq_zero_iff (keys : KeyPair) (m : ℕ) (hm : m < keys.n) :
    encryptBlock keys.toPublicKey m = 0 ↔ m = 0 := by
  unfold encryptBlock
  dsimp [KeyPair.toPublicKey]
  constructor
  all_goals intro h1
  · replace h1 : keys.n ∣ m ^ keys.e := by omega
    have h2 := calc
        keys.p ∣ keys.n := by apply Nat.dvd_mul_right
        _ ∣ _ := h1
    replace h2 := keys.hp.dvd_of_dvd_pow h2
    have h3 := calc
        keys.q ∣ keys.n := by apply Nat.dvd_mul_left
        _ ∣ _ := h1
    replace h3 := keys.hq.dvd_of_dvd_pow h3
    replace h1 : keys.n ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd keys.hpq h2 h3
    exact Nat.eq_zero_of_dvd_of_lt h1 hm
  · calc
      _ = 0 ^ keys.e % keys.n := by rw [h1]
      _ = 0 % keys.n := by
        congr 1
        refine Nat.zero_pow ?_
        have := keys.he1
        omega
      _ = _ := by simp

@[simp] theorem encryptBlock_zero (keys : KeyPair) : encryptBlock keys.toPublicKey 0 = 0 := by
  have := keys.he1
  simp [encryptBlock, KeyPair.toPublicKey, keys.e.zero_pow (by omega)]

theorem decryptBlock_encryptBlock_lemma_p (keys : KeyPair) (m : ℕ) (hm : m < keys.n) :
    m ^ (keys.e * keys.d) ≡ m [MOD keys.p] := by
  obtain ⟨p, hp, q, hq, hpq, e, he1, he2, he3⟩ := keys
  dsimp [KeyPair.n, KeyPair.d, KeyPair.toPublicKey, KeyPair.toPrivateKey]
  set d := (e : ZMod ((p - 1) * (q - 1)))⁻¹.val
  have h1 : e * d ≡ 1 [MOD ((p - 1) * (q - 1))] := by
    simpa [←ZMod.natCast_eq_natCast_iff] using ZMod.mul_val_inv he3
  have h2 : e * d ≠ 0 := by
    intro h2
    simp [h2, Nat.ModEq] at h1
    grind
  obtain ⟨k, h1⟩ : ∃ k : ℕ, e * d - 1 = k * ((p - 1) * (q - 1)) := by
    apply exists_eq_mul_left_of_dvd
    apply (Nat.modEq_iff_dvd' (by omega)).mp
    exact h1.symm
  replace h1 : e * d = k * ((p - 1) * (q - 1)) + 1 := by omega
  by_cases h3 : m % p = 0
  · calc
      _ = (m % p) ^ (e * d) % p := by apply Nat.pow_mod
      _ = _ := by simp [h3, zero_pow_eq_zero.mpr h2]
  · calc
      _ = m ^ (k * ((p - 1) * (q - 1)) + 1) := by rw [h1]
      _ = (m ^ (p - 1)) ^ (k * (q - 1)) * m := by ring_nf
      _ ≡ m [MOD p] := calc
        (m ^ (p - 1)) ^ (k * (q - 1)) * m % p =
          (m ^ (p - 1)) ^ (k * (q - 1)) % p * (m % p) % p := by apply Nat.mul_mod
        _ = (m ^ (p - 1) % p) ^ (k * (q - 1)) % p * (m % p) % p := by congr 2; apply Nat.pow_mod
        _ = 1 ^ (k * (q - 1)) % p * (m % p) % p := by
          congr 4
          convert_to _ = 1 % p using 1
          · symm
            apply Nat.mod_eq_of_lt
            exact Nat.Prime.one_lt hp
          zify
          apply Int.ModEq.pow_card_sub_one_eq_one hp
          apply Nat.isCoprime_iff_coprime.mpr
          apply Nat.Coprime.symm
          rw [hp.coprime_iff_not_dvd]
          omega
        _ = _ := by simp

theorem decryptBlock_encryptBlock_lemma_q (keys : KeyPair) (m : ℕ) (hm : m < keys.n) :
    m ^ (keys.e * keys.d) ≡ m [MOD keys.q] := by
  convert decryptBlock_encryptBlock_lemma_p keys.symm m (by
    convert hm using 1
    dsimp [KeyPair.symm, KeyPair.n]
    ring) using 1
  dsimp [KeyPair.symm, KeyPair.d, KeyPair.φ]
  rw [show (keys.p - 1) * (keys.q - 1) = (keys.q - 1) * (keys.p - 1) by ring]

theorem decryptBlock_encryptBlock (keys : KeyPair) (m : ℕ) (hm : m < keys.n) :
    decryptBlock keys.toPrivateKey (encryptBlock keys.toPublicKey m) = m := by
  unfold decryptBlock encryptBlock
  obtain ⟨p, hp, q, hq, hpq, e, he1, he2, he3⟩ := keys
  dsimp [KeyPair.n] at hm
  dsimp [KeyPair.n, KeyPair.d, KeyPair.toPublicKey, KeyPair.toPrivateKey]
  let keys : KeyPair := ⟨p, hp, q, hq, hpq, e, he1, he2, he3⟩
  set n := p * q
  set d := (e : ZMod ((p - 1) * (q - 1)))⁻¹.val
  calc
    _ = (m ^ e) ^ d % n := by symm; apply Nat.pow_mod
    _ = m ^ (e * d) % n := by symm; congr 1; apply Nat.pow_mul
    _ = m % n := by
      change m ^ (e * d) ≡ m [MOD (p * q)]
      rw [←Nat.modEq_and_modEq_iff_modEq_mul hpq]
      split_ands
      · exact decryptBlock_encryptBlock_lemma_p keys m hm
      · exact decryptBlock_encryptBlock_lemma_q keys m hm
    _ = m := by exact Nat.mod_eq_of_lt hm

@[simp] theorem decryptBlock_zero (keys : KeyPair) : decryptBlock keys.toPrivateKey 0 = 0 := by
  convert_to decryptBlock keys.toPrivateKey (encryptBlock keys.toPublicKey 0) = 0 using 1
  · simp
  apply decryptBlock_encryptBlock
  dsimp [KeyPair.n]
  have := keys.hp.one_lt
  have := keys.hq.one_lt
  nlinarith

def encrypt (key : PublicKey) (m : ℕ) :=
  ∑ k ∈ Finset.Ico 0 (key.n.log m + 1), encryptBlock key (key.n.nthDigit m k) * key.n ^ k

def decrypt (key : PrivateKey) (c : ℕ) :=
  ∑ k ∈ Finset.Ico 0 (key.n.log c + 1), decryptBlock key (key.n.nthDigit c k) * key.n ^ k

theorem decrypt_encrypt (keys : KeyPair) (m : ℕ) :
    decrypt keys.toPrivateKey (encrypt keys.toPublicKey m) = m := by
  have hb1 : 2 ≤ keys.n := by
    dsimp [KeyPair.n]
    have := keys.hp.one_lt
    have := keys.hq.one_lt
    nlinarith
  by_cases hm : m = 0
  · simp [encrypt, decrypt, hm, Nat.nthDigit]
  unfold decrypt
  have th1 : Nat.log keys.n (encrypt keys.toPublicKey m) = Nat.log keys.n m := by
    refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
    · unfold encrypt
      calc
        ∑ k ∈ Finset.Ico 0 (Nat.log keys.n m + 1),
          encryptBlock keys.toPublicKey (keys.n.nthDigit m k) * keys.n ^ k =
        (∑ k ∈ Finset.Ico 0 (Nat.log keys.n m),
          encryptBlock keys.toPublicKey (keys.n.nthDigit m k) * keys.n ^ k +
            encryptBlock keys.toPublicKey (keys.n.nthDigit m (Nat.log keys.n m)) *
              keys.n ^ (Nat.log keys.n m)) := by
          have h1 :
              {Nat.log keys.n m} ⊆ Finset.Ico 0 (Nat.log keys.n m + 1) := by
            intro i hi
            simp at hi ⊢
            omega
          rw [←Finset.sum_sdiff h1]
          congr 2
          ext i
          simp
          omega
        _ ≥
          encryptBlock keys.toPublicKey (keys.n.nthDigit m (Nat.log keys.n m)) *
          keys.n ^ (Nat.log keys.n m) := by
          apply Nat.le_add_left
        _ ≥ 1 * keys.n ^ (Nat.log keys.n m) := by
          gcongr
          contrapose! hm
          replace h1 : encryptBlock keys.toPublicKey (keys.n.nthDigit m (Nat.log keys.n m)) = 0
            := by omega
          rw [encryptBlock_eq_zero_iff keys (keys.n.nthDigit m (Nat.log keys.n m))
                (by apply keys.n.nthDigit_lt; omega)] at h1
          simpa [Nat.nthDigit_log_eq_zero_iff _ _ hb1] using h1
        _ = _ := by ring
    · unfold encrypt
      apply Nat.sum_mul_base_pow_lt_base_pow hb1
      intro k
      unfold encryptBlock
      dsimp [KeyPair.toPublicKey]
      apply Nat.mod_lt
      omega
  have th2 k : keys.n.nthDigit (encrypt keys.toPublicKey m) k =
      encryptBlock keys.toPublicKey (keys.n.nthDigit m k) := by
    unfold encrypt
    dsimp [KeyPair.toPublicKey]
    rw [Nat.nthDigit_sum_mul_base_pow]
    · split_ifs with hk
      · rfl
      · symm
        calc
          _ = 0 ^ keys.e % keys.n := by
            unfold encryptBlock
            congr 2
            unfold Nat.nthDigit
            calc
              _ = 0 % keys.n := by
                congr 1
                refine Nat.div_eq_of_lt ?_
                replace hk : keys.n.log m < k := by omega
                convert_to keys.n.log m < keys.n.log (keys.n ^ k) using 1 at hk
                · symm; exact Nat.log_pow hb1 k
                contrapose! hk
                exact Nat.log_mono_right hk
              _ = _ := by simp
          _ = 0 % keys.n := by
            congr 1
            refine Nat.zero_pow ?_
            have := keys.he1
            omega
          _ = 0 := by simp
    · simpa using hb1
    · unfold encryptBlock
      intro i
      apply Nat.mod_lt
      simp
      omega
  calc
    ∑ k ∈ Finset.Ico 0 (Nat.log keys.n (encrypt keys.toPublicKey m) + 1),
      decryptBlock keys.toPrivateKey
        (keys.n.nthDigit (encrypt keys.toPublicKey m) k) * keys.n ^ k =
    ∑ k ∈ Finset.Ico 0 (Nat.log keys.n (encrypt keys.toPublicKey m) + 1),
      keys.n.nthDigit m k * keys.n ^ k := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      rw [th2]
      rw [decryptBlock_encryptBlock]
      apply keys.n.nthDigit_lt
      omega
    _ = m := by simpa [th1] using Nat.sum_nthDigit_mul_base_pow hb1 m

end RSA


def keys : RSA.KeyPair :=
  { p := 61
    hp := by decide
    q := 53
    hq := by decide
    hpq := by decide
    e := 17
    he1 := by decide
    he2 := by decide
    he3 := by decide }


-- #eval RSA.encrypt keys.toPublicKey 12345
-- #eval RSA.decrypt keys.toPrivateKey (RSA.encrypt keys.toPublicKey 12345)
