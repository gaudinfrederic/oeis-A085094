import Mathlib
import CornerTable

open scoped Pointwise

/- A077754 / Murthy — formalisation en cours.
   Théorème : tout n hors {1,2,5,11} ∪ 10ℕ admet un multiple
   N ≥ 10 à chiffres tous non nuls et σ₁₀(N) = n. -/

def sigma10 (N : ℕ) : ℕ := (Nat.digits 10 N).sum
def allNonzero (N : ℕ) : Bool := (Nat.digits 10 N).all (· ≠ 0)
def exceptions (n : ℕ) : Prop := n ∈ ({1,2,5,11} : Set ℕ) ∨ 10 ∣ n

/-- Étape 0 : tout multiple de 10 contient le chiffre 0. -/
theorem exc_10 (n : ℕ) (hn : 10 ∣ n) (N : ℕ) (hN : n ∣ N) (h10 : N ≥ 10) :
    allNonzero N = false := by
  have hmod : N % 10 = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp (dvd_trans hn hN)
  have hN0 : N ≠ 0 := by omega
  rw [allNonzero, List.all_eq_false]
  refine ⟨0, ?_, by simp⟩
  rw [Nat.digits_def' (by norm_num) (by omega : 0 < N), hmod]
  simp

/-- Auxiliaire : N ≥ 10 à chiffres non nuls ⇒ σ ≥ dernier
    chiffre + 1 (le préfixe est non vide et tout chiffre ≥ 1). -/
theorem sigma_ge_last_add_one (N : ℕ) (h10 : N ≥ 10) (h : allNonzero N) :
    sigma10 N ≥ N % 10 + 1 := by
  have hN0 : 0 < N := by omega
  rw [allNonzero, Nat.digits_def' (by norm_num) hN0,
      List.all_eq_true] at h
  have hq : Nat.digits 10 (N / 10) ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  rw [sigma10, Nat.digits_def' (by norm_num) hN0]
  cases hD : Nat.digits 10 (N / 10) with
  | nil => exact absurd hD hq
  | cons d ds =>
    have hdm : d ∈ N % 10 :: Nat.digits 10 (N / 10) := by
      rw [hD]; simp
    have hd : d ≥ 1 :=
      Nat.pos_iff_ne_zero.mpr (of_decide_eq_true (h d hdm))
    rw [List.sum_cons, List.sum_cons]
    omega

/-- n = 1 : impossible (σ ≥ 2). -/
theorem exc_1 (N : ℕ) (h10 : N ≥ 10) (h : allNonzero N) :
    sigma10 N ≠ 1 := by
  have hs := sigma_ge_last_add_one N h10 h
  have hdig : N % 10 ∈ Nat.digits 10 N := by
    rw [Nat.digits_def' (by norm_num) (by omega : 0 < N)]; simp
  rw [allNonzero, List.all_eq_true] at h
  have h0 : N % 10 ≥ 1 := Nat.pos_iff_ne_zero.mpr (of_decide_eq_true (h (N % 10) hdig))
  omega

/-- n = 2 : le dernier chiffre est pair et non nul ⇒ ≥ 2,
    donc σ ≥ 3. -/
theorem exc_2 (N : ℕ) (hN : 2 ∣ N) (h10 : N ≥ 10) (h : allNonzero N) :
    sigma10 N ≠ 2 := by
  have hs := sigma_ge_last_add_one N h10 h
  have hdig : N % 10 ∈ Nat.digits 10 N := by
    rw [Nat.digits_def' (by norm_num) (by omega : 0 < N)]; simp
  rw [allNonzero, List.all_eq_true] at h
  have h0 : N % 10 ≠ 0 := by
    have := h (N % 10) hdig; simpa using this
  have hpar : N % 10 % 2 = 0 := by omega
  omega

/-- n = 5 : multiple finit par 0 ou 5 ; non nul ⇒ finit par
    5, et ≥ 2 chiffres ⇒ σ ≥ 6. -/
theorem exc_5 (N : ℕ) (hN : 5 ∣ N) (h10 : N ≥ 10) (h : allNonzero N) :
    sigma10 N ≠ 5 := by
  have hs := sigma_ge_last_add_one N h10 h
  have hdig : N % 10 ∈ Nat.digits 10 N := by
    rw [Nat.digits_def' (by norm_num) (by omega : 0 < N)]; simp
  rw [allNonzero, List.all_eq_true] at h
  have h0 : N % 10 ≠ 0 := by
    have := h (N % 10) hdig; simpa using this
  have h5 : N % 10 % 5 = 0 := by omega
  have hge : N % 10 ≥ 5 := by omega
  omega

/-- Borne faible : |somme alternée| ≤ somme (éléments ≥ 0). -/
lemma abs_altSum_le_sum (l : List ℤ) (h : ∀ x ∈ l, 0 ≤ x) :
    |l.alternatingSum| ≤ l.sum := by
  induction l using List.alternatingSum.induct with
  | case1 => simp
  | case2 a =>
    have := h a (by simp); simp [abs_of_nonneg this]
  | case3 a b rest ih =>
    have ha := h a (by simp)
    have hb := h b (by simp)
    have hrest : ∀ x ∈ rest, 0 ≤ x := fun x hx => h x (by simp [hx])
    have habs := ih hrest
    simp only [List.alternatingSum, List.sum_cons]
    calc |a + -b + rest.alternatingSum|
        ≤ |a + -b| + |rest.alternatingSum| := abs_add_le _ _
      _ ≤ (a + b) + rest.sum :=
          add_le_add (by rw [abs_le]; omega) habs
      _ = a + (b + rest.sum) := by ring

/-- Borne forte : ≥ 2 éléments tous ≥ 1 ⇒ |alt| ≤ somme − 2. -/
lemma abs_altSum_le_sum_sub_two (l : List ℤ) (h : ∀ x ∈ l, 1 ≤ x)
    (hlen : l.length ≥ 2) :
    |l.alternatingSum| ≤ l.sum - 2 := by
  match l with
  | [] => simp at hlen
  | [_] => simp at hlen
  | a :: b :: rest =>
    have ha := h a (by simp)
    have hb := h b (by simp)
    have hrest : ∀ x ∈ rest, 0 ≤ x := fun x hx => by
      have := h x (by simp [hx]); omega
    have habs := abs_altSum_le_sum rest hrest
    simp only [List.alternatingSum, List.sum_cons]
    calc |a + -b + rest.alternatingSum|
        ≤ |a + -b| + |rest.alternatingSum| := abs_add_le _ _
      _ ≤ (a + b - 2) + rest.sum :=
          add_le_add (by rw [abs_le]; omega) habs
      _ = a + (b + rest.sum) - 2 := by ring

/-- n = 11 : obstruction de la somme alternee. -/
theorem exc_11 (N : ℕ) (hN : 11 ∣ N) (h10 : N ≥ 10) (h : allNonzero N) :
    sigma10 N ≠ 11 := by
  intro hσ
  rw [allNonzero, List.all_eq_true] at h
  have hA := Nat.eleven_dvd_iff.mp hN
  have hall : ∀ x ∈ (Nat.digits 10 N).map (fun n : ℕ => (n : ℤ)), 1 ≤ x := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨d, hd, hdx⟩ := hx
    rw [← hdx]
    have hd0 : d ≠ 0 := of_decide_eq_true (h d hd)
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hd0)
  have hlen : ((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).length ≥ 2 := by
    have e : ((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).length
        = (Nat.digits 10 N).length := List.length_map _
    have hlog : Nat.log 10 N ≥ 1 :=
      Nat.le_log_of_pow_le (by norm_num) (by simpa using h10)
    have hlen' := Nat.length_digits 10 N (by norm_num) (by omega : N ≠ 0)
    omega
  have habs := abs_altSum_le_sum_sub_two _ hall hlen
  have hsum : ((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).sum
      = (sigma10 N : ℤ) := by
    have hmap : ∀ l : List ℕ,
        ((l.map (fun n : ℕ => (n : ℤ))).sum : ℤ) = l.sum := by
      intro l; induction l with
      | nil => simp
      | cons a t ih =>
        rw [List.map_cons, List.sum_cons, List.sum_cons, Nat.cast_add, ih]
    rw [sigma10]; exact hmap _
  have hmod : 2 ∣ (((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).sum
      - ((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).alternatingSum) := by
    have hp : ∀ l : List ℤ, 2 ∣ (l.sum - l.alternatingSum) := by
      intro l
      induction l using List.alternatingSum.induct with
      | case1 => simp
      | case2 a => simp [List.alternatingSum]
      | case3 a b rest ih =>
        obtain ⟨k, hk⟩ := ih
        use k + b
        simp only [List.alternatingSum, List.sum_cons]
        omega
    exact hp _
  obtain ⟨k, hk⟩ := hA
  obtain ⟨k2, hk2⟩ := hmod
  rw [hσ] at hsum
  have hb : |((Nat.digits 10 N).map (fun n : ℕ => (n : ℤ))).alternatingSum|
      ≤ 9 := by omega
  rw [abs_le] at hb
  omega

/-- Lemme du bloc bas (partie 2^a) : pour tout a >= 1 il existe
    B a a chiffres, tous dans {1,2}, divisible par 2^a, et
    sigma(B) <= 2a. Construction B_{a+1} = B_a + c.10^a,
    c dans {1,2} choisi par la parite de B_a / 2^a. -/
theorem lowBlock2 (a : ℕ) (ha : 1 ≤ a) :
    ∃ B : ℕ, 2 ^ a ∣ B ∧ (Nat.digits 10 B).length = a ∧
      (∀ d ∈ Nat.digits 10 B, d = 1 ∨ d = 2) ∧ sigma10 B ≤ 2 * a := by
  induction a with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨2, ?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num [Nat.digits, Nat.digitsAux]
      · intro d hd
        have : Nat.digits 10 2 = [2] := by norm_num [Nat.digits, Nat.digitsAux]
        rw [this] at hd
        simp at hd
        exact Or.inr hd
      · norm_num [sigma10, Nat.digits, Nat.digitsAux]
    · obtain ⟨B, hdiv, hlen, hdig, hsum⟩ := ih hk
      set t := B / 2 ^ k with ht
      set c := if t % 2 = 0 then 2 else 1 with hc
      have hcpos : 0 < c := by unfold c; split <;> norm_num
      have hclt : c < 10 := by unfold c; split <;> norm_num
      have hcmem : c = 1 ∨ c = 2 := by
        unfold c; split <;> simp
      have hBt : B = t * 2 ^ k := (Nat.div_mul_cancel hdiv).symm
      have h10k : (10 : ℕ) ^ k = 2 ^ k * 5 ^ k := by
        rw [← Nat.mul_pow]
      have hpar : 2 ∣ t + c * 5 ^ k := by
        unfold c
        split_ifs with hev
        · exact ⟨t / 2 + 5 ^ k, by omega⟩
        · have h5 : (5 : ℕ) ^ k % 2 = 1 := by
            have ho : Odd ((5 : ℕ) ^ k) := Odd.pow (by decide)
            exact Nat.odd_iff.mp ho
          have ht2 : t % 2 = 1 := by omega
          refine ⟨(t + 5 ^ k) / 2, ?_⟩
          omega
      have hd : Nat.digits 10 (B + c * 10 ^ k)
          = Nat.digits 10 B ++ [c] := by
        have h := Nat.digits_append_digits (b := 10) (m := c) (n := B)
          (by norm_num)
        rw [hlen] at h
        have hdc : Nat.digits 10 c = [c] :=
          Nat.digits_of_lt 10 c (by omega) hclt
        rw [hdc, mul_comm (10 ^ k) c] at h
        exact h.symm
      refine ⟨B + c * 10 ^ k, ?_, ?_, ?_, ?_⟩
      · rw [hBt, h10k]
        have hE : t * 2 ^ k + c * (2 ^ k * 5 ^ k)
            = 2 ^ k * (t + c * 5 ^ k) := by ring
        rw [hE]
        obtain ⟨w, hw⟩ := hpar
        rw [hw]
        exact ⟨w, by ring⟩
      · rw [hd, List.length_append, List.length_singleton, hlen]
      · rw [hd]
        intro d hd'
        rw [List.mem_append] at hd'
        rcases hd' with h1 | h2
        · exact hdig d h1
        · rw [List.mem_singleton] at h2
          rw [h2]; exact hcmem
      · rw [sigma10, hd, List.sum_append, List.sum_singleton]
        rw [sigma10] at hsum
        have hc2 : c ≤ 2 := by unfold c; split <;> norm_num
        omega

/-- Lemme du bloc bas (partie 5^b) : pour tout b >= 1 il existe
    B a b chiffres, tous dans {1,..,5}, divisible par 5^b, et
    sigma(B) <= 5b. Construction B_{b+1} = B_b + c.10^b,
    c dans {1,..,5} choisi modulo 5. -/
theorem lowBlock5 (b : ℕ) (hb : 1 ≤ b) :
    ∃ B : ℕ, 5 ^ b ∣ B ∧ (Nat.digits 10 B).length = b ∧
      (∀ d ∈ Nat.digits 10 B, 1 ≤ d ∧ d ≤ 5) ∧ sigma10 B ≤ 5 * b := by
  induction b with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨5, ?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num [Nat.digits, Nat.digitsAux]
      · intro d hd
        have : Nat.digits 10 5 = [5] := by norm_num [Nat.digits, Nat.digitsAux]
        rw [this] at hd; simp at hd; omega
      · norm_num [sigma10, Nat.digits, Nat.digitsAux]
    · obtain ⟨B, hdiv, hlen, hdig, hsum⟩ := ih hk
      set t := B / 5 ^ k with ht
      set w := t * 2 ^ (3 * k) % 5 with hw
      have hwlt : w < 5 := Nat.mod_lt _ (by norm_num)
      set c := 5 - w with hcdef
      have hcpos : 0 < c := by omega
      have hcle : c ≤ 5 := by omega
      have hclt : c < 10 := by omega
      have hBt : B = t * 5 ^ k := (Nat.div_mul_cancel hdiv).symm
      have h10k : (10 : ℕ) ^ k = 5 ^ k * 2 ^ k := by
        rw [← Nat.mul_pow]
      have h2k : (2 : ZMod 5) ^ (3 * k) * (2 : ZMod 5) ^ k = 1 := by
        rw [← pow_add]
        have : 3 * k + k = 4 * k := by ring
        rw [this, pow_mul]
        have h16 : ((2 : ZMod 5) ^ 4) = 1 := by decide
        rw [h16, one_pow]
      have hwz : (w : ZMod 5) = (t : ZMod 5) * (2 : ZMod 5) ^ (3 * k) := by
        have e : (w : ZMod 5) = ((t * 2 ^ (3 * k) : ℕ) : ZMod 5) := by
          rw [ZMod.natCast_eq_natCast_iff, hw]
          exact Nat.mod_modEq _ _
        calc (w : ZMod 5) = ((t * 2 ^ (3 * k) : ℕ) : ZMod 5) := e
        _ = (t : ZMod 5) * (2 : ZMod 5) ^ (3 * k) := by push_cast; rfl
      have hcz : (c : ZMod 5) = -(w : ZMod 5) := by
        have hcw : c + w = 5 := by omega
        have h2 := congrArg (Nat.cast : ℕ → ZMod 5) hcw
        push_cast at h2
        have h5z : (5 : ZMod 5) = 0 := by decide
        rw [h5z] at h2
        exact eq_neg_of_add_eq_zero_left h2
      have key : ((t : ZMod 5) + (c : ZMod 5) * (2 : ZMod 5) ^ k) = 0 := by
        calc (t : ZMod 5) + (c : ZMod 5) * (2 : ZMod 5) ^ k
            = (t : ZMod 5) + (-(w : ZMod 5)) * (2 : ZMod 5) ^ k := by
              rw [hcz]
          _ = (t : ZMod 5) - (t * (2 : ZMod 5) ^ (3 * k))
                * (2 : ZMod 5) ^ k := by rw [hwz]; ring
          _ = (t : ZMod 5) - t * ((2 : ZMod 5) ^ (3 * k)
                * (2 : ZMod 5) ^ k) := by ring
          _ = (t : ZMod 5) - t * 1 := by rw [h2k]
          _ = 0 := by ring
      have hpar : 5 ∣ t + c * 2 ^ k := by
        have h2 : ((t + c * 2 ^ k : ℕ) : ZMod 5) = 0 := by
          push_cast; exact key
        exact (CharP.cast_eq_zero_iff (ZMod 5) 5 _).mp h2
      have hd : Nat.digits 10 (B + c * 10 ^ k)
          = Nat.digits 10 B ++ [c] := by
        have h := Nat.digits_append_digits (b := 10) (m := c) (n := B)
          (by norm_num)
        rw [hlen] at h
        have hdc : Nat.digits 10 c = [c] :=
          Nat.digits_of_lt 10 c (by omega) hclt
        rw [hdc, mul_comm (10 ^ k) c] at h
        exact h.symm
      refine ⟨B + c * 10 ^ k, ?_, ?_, ?_, ?_⟩
      · rw [hBt, h10k]
        have hE : t * 5 ^ k + c * (5 ^ k * 2 ^ k)
            = 5 ^ k * (t + c * 2 ^ k) := by ring
        rw [hE]
        obtain ⟨w2, hw2⟩ := hpar
        rw [hw2]
        exact ⟨w2, by ring⟩
      · rw [hd, List.length_append, List.length_singleton, hlen]
      · rw [hd]
        intro d hd'
        rw [List.mem_append] at hd'
        rcases hd' with h1 | h2
        · exact hdig d h1
        · rw [List.mem_singleton] at h2
          rw [h2]; omega
      · rw [sigma10, hd, List.sum_append, List.sum_singleton]
        rw [sigma10] at hsum
        omega

/-- La grille d echange : x = d1 + 11 d2, d_i in [-4,4],
    |d1+d2| <= 4, x =/= 0. |X| = 60 (decidable). -/
def Xgrid : List ℤ :=
  (((List.range 9).map fun (i : ℕ) => (i : ℤ) - 4).product
    ((List.range 9).map fun (i : ℕ) => (i : ℤ) - 4)).filterMap
    fun p =>
      if -4 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 4 ∧ p.1 + 11 * p.2 ≠ 0
      then some (p.1 + 11 * p.2) else none

/-- |X| = 60 et listes d unites {2,5}-smooth / {2,3,5}-smooth.
    [T-Lean] par calcul natif. -/
theorem Xgrid_card : Xgrid.length = 60 := by native_decide

/-- les elements {2,5}-smooth de X : 16 signes. -/
def Xsmooth25 : List ℤ :=
  [1, 2, 4, 8, 10, 20, 32, 40, -1, -2, -4, -8, -10, -20, -32, -40]

theorem Xsmooth25_sub : ∀ x ∈ Xsmooth25, x ∈ Xgrid := by native_decide

/-- les elements {2,3,5}-smooth de X : 28 signes. -/
def Xsmooth235 : List ℤ :=
  [1, 2, 3, 4, 8, 9, 10, 12, 18, 20, 24, 30, 32, 40,
   -1, -2, -3, -4, -8, -9, -10, -12, -18, -20, -24, -30, -32, -40]

theorem Xsmooth235_sub : ∀ x ∈ Xsmooth235, x ∈ Xgrid := by native_decide

/-- Concatenation sans retenue : N = B + 10^d.H avec
    d = nb de chiffres de B (B /= 0) se decompose en
    digits N = digits B ++ digits H. -/
theorem digits_concat (B H : ℕ) (hB : B ≠ 0) :
    Nat.digits 10 (B + 10 ^ (Nat.digits 10 B).length * H)
      = Nat.digits 10 B ++ Nat.digits 10 H := by
  have h := Nat.digits_append_digits (b := 10) (m := H) (n := B)
    (by norm_num)
  exact h.symm

/-- sigma se distribue sur la concatenation. -/
theorem sigma_concat (B H : ℕ) (hB : B ≠ 0) :
    sigma10 (B + 10 ^ (Nat.digits 10 B).length * H)
      = sigma10 B + sigma10 H := by
  rw [sigma10, digits_concat B H hB, List.sum_append]; rfl

/-- nonnul se distribue sur la concatenation. -/
theorem nonzero_concat (B H : ℕ) (hB : B ≠ 0) :
    allNonzero (B + 10 ^ (Nat.digits 10 B).length * H)
      = (allNonzero B && allNonzero H) := by
  simp only [allNonzero, digits_concat B H hB, List.all_append]

/-- Echange equilibre sur un triple {10^{3i},10^{3i+1},10^{3i+2}}
    avec d0 = -(d1+d2) : la valeur change de 9.10^{3i}.(d1+11d2). -/
theorem exchange_value (i : ℕ) (d1 d2 : ℤ) :
    (10 : ℤ) ^ (3 * i) * (-(d1 + d2))
      + (10 : ℤ) ^ (3 * i + 1) * d1
      + (10 : ℤ) ^ (3 * i + 2) * d2
      = 9 * (10 : ℤ) ^ (3 * i) * (d1 + 11 * d2) := by
  ring

/-- Theoreme de Chowla (1935) : dans Z/k, si 0 in B et tout
    autre element de B est une unite, alors
    |A+B| >= min(k, |A|+|B|-1). Preuve e-transform. -/
theorem chowla (k : ℕ) [NeZero k] (A B : Finset (ZMod k))
    (hA : A.Nonempty) (h0 : 0 ∈ B) (hu : ∀ b ∈ B, b = 0 ∨ IsUnit b) :
    min k (A.card + B.card - 1) ≤ (A + B).card := by
  suffices H : ∀ n : ℕ, ∀ (A B : Finset (ZMod k)), B.card ≤ n →
      A.Nonempty → 0 ∈ B → (∀ b ∈ B, b = 0 ∨ IsUnit b) →
      min k (A.card + B.card - 1) ≤ (A + B).card by
    exact H B.card A B le_rfl hA h0 hu
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro A B hBn hA h0 hu
  -- cas trivial : A + B atteint deja la taille du groupe
  rcases lt_or_ge (A + B).card k with hcase | hcase
  swap
  · exact le_trans (min_le_left _ _) hcase
  by_cases hfull : ∃ a0 ∈ A, ∃ b0 ∈ B, b0 ≠ 0 ∧ a0 + b0 ∉ A
  · -- etape e-transform : on fait decroitre |B|
    obtain ⟨a0, ha0, b0, hb0, hb0n, hnotin⟩ := hfull
    set T := Finset.addDysonETransform a0 (A, B) with hTdef
    have hTcard := Finset.addDysonETransform.card a0 (A, B)
    have hTsub := Finset.addDysonETransform.subset a0 (A, B)
    have hT1 : T.1 = A ∪ (a0 +ᵥ B) := rfl
    have hT2 : T.2 = B ∩ ((-a0) +ᵥ A) := rfl
    have h0' : (0 : ZMod k) ∈ T.2 := by
      rw [hT2, Finset.mem_inter]
      refine ⟨h0, ?_⟩
      change 0 ∈ A.image (fun x => -a0 +ᵥ x)
      rw [Finset.mem_image]
      exact ⟨a0, ha0, by simp⟩
    have hb0' : b0 ∉ T.2 := by
      rw [hT2, Finset.mem_inter]
      rintro ⟨-, h⟩
      change b0 ∈ A.image (fun x => -a0 +ᵥ x) at h
      rw [Finset.mem_image] at h
      obtain ⟨a, ha, hva⟩ := h
      apply hnotin
      have haeq : a = a0 + b0 := by
        rw [vadd_eq_add] at hva
        have hc : a0 + (-a0 + a) = a := by
          rw [← add_assoc, add_neg_cancel, zero_add]
        rw [hva] at hc; rw [← hc]
      rwa [← haeq]
    have hB'lt : T.2.card < B.card := by
      apply Finset.card_lt_card
      exact ⟨hT2.symm ▸ Finset.inter_subset_left, fun h => hb0' (h hb0)⟩
    have hu' : ∀ b ∈ T.2, b = 0 ∨ IsUnit b := fun b hb =>
      hu b ((Finset.mem_inter.mp (hT2 ▸ hb)).1)
    have hA' : T.1.Nonempty :=
      hA.mono (hT1.symm ▸ Finset.subset_union_left)
    have ih' := ih T.2.card (lt_of_lt_of_le hB'lt hBn) T.1 T.2 le_rfl hA' h0' hu'
    calc min k (A.card + B.card - 1)
        = min k (T.1.card + T.2.card - 1) := by rw [hTcard]
      _ ≤ (T.1 + T.2).card := ih'
      _ ≤ (A + B).card := Finset.card_mono hTsub
  · -- pas de (a0,b0) : A est periodique — contradiction avec cardinal
    push_neg at hfull
    by_cases hB1 : B.card ≤ 1
    · -- B = {0} : A + B = A
      have hBeq : B = {0} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨h0, fun x hx =>
          Finset.card_le_one.mp hB1 x hx 0 h0⟩
      rw [hBeq]
      simp
    · -- B >= 2 : prendre b0 ≠ 0 unite → A + b0 = A → k | |A| → A = univ
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp
        (by omega : 1 < B.card)
      obtain ⟨b0, hb0, hb0n⟩ : ∃ b0 ∈ B, b0 ≠ 0 := by
        rcases eq_or_ne x 0 with hx0 | hx0
        · exact ⟨y, hy, fun h => hxy (hx0.trans h.symm)⟩
        · exact ⟨x, hx, hx0⟩
      have hAbs : A.image (· + b0) ⊆ A := by
        intro x hx
        rw [Finset.mem_image] at hx; obtain ⟨a, ha, rfl⟩ := hx
        exact hfull a ha b0 hb0 hb0n
      have hinj : Set.InjOn (· + b0) A :=
        Set.injOn_of_injective (fun x y h => add_right_cancel h)
      have heq : A.image (· + b0) = A :=
        Finset.eq_of_subset_of_card_le hAbs
          (by rw [Finset.card_image_of_injOn hinj])
      have hsum : ∑ x ∈ A, x = ∑ a ∈ A, (a + b0) := by
        have h := Finset.sum_image (s := A) (g := (· + b0)) (f := id) hinj
        rw [heq] at h; simpa using h
      rw [Finset.sum_add_distrib, Finset.sum_const] at hsum
      have h0b : A.card • b0 = 0 :=
        add_left_cancel (show ∑ x ∈ A, x + A.card • b0 = ∑ x ∈ A, x + 0
          from by rw [add_zero]; exact hsum.symm)
      rw [nsmul_eq_mul] at h0b
      have hu' := hu b0 hb0
      rcases hu' with hb0z | hb0u
      · exact absurd hb0z hb0n
      have hA0 : (A.card : ZMod k) = 0 :=
        (IsUnit.mul_left_eq_zero hb0u).mp h0b
      have hkdvd : k ∣ A.card :=
        (CharP.cast_eq_zero_iff (ZMod k) k A.card).mp hA0
      have hAcard : A.card = k := by
        have hpos : 0 < A.card := Finset.card_pos.mpr hA
        have hle : A.card ≤ k := by
          have := Finset.card_le_univ A
          rwa [ZMod.card] at this
        have hkle : k ≤ A.card := Nat.le_of_dvd hpos hkdvd
        omega
      have hAuniv : A = Finset.univ := Finset.eq_univ_of_card A (by
        rw [hAcard, ZMod.card])
      have : (A + B).card = k := by
        have hu2 : (A + B) = Finset.univ := by
          apply Finset.eq_univ_of_forall
          intro x
          rw [hAuniv]
          exact Finset.mem_add.mpr ⟨x, Finset.mem_univ x, 0, h0, add_zero x⟩
        rw [hu2, Finset.card_univ, ZMod.card]
      omega

/-- La fibre : H = somme_e (1 + u_e) . 10^e pour e < L,
    representee comme ofDigits de la liste des chiffres. -/
def fibre (u : ℕ → ℕ) (L : ℕ) : ℕ :=
  Nat.ofDigits 10 ((List.range L).map fun e => 1 + u e)

/-- Recurrence de la fibre : fibre u (L+1) = fibre u L +
    10^L . (1 + u L). -/
theorem fibre_succ (u : ℕ → ℕ) (L : ℕ) :
    fibre u (L + 1) = fibre u L + 10 ^ L * (1 + u L) := by
  rw [fibre, List.range_succ, List.map_append, List.map_singleton,
      Nat.ofDigits_append]
  simp [fibre]

/-- Valeur de la fibre : somme_e (1 + u_e) . 10^e. -/
theorem fibre_val (u : ℕ → ℕ) (L : ℕ) :
    fibre u L = ∑ e ∈ Finset.range L, (1 + u e) * 10 ^ e := by
  induction' L with L ih
  · simp [fibre]
  · rw [fibre_succ, ih, Finset.sum_range_succ]
    ring

/-- Delta de la fibre : v = u + D (sur Z) change la valeur
    de somme_e D_e . 10^e. -/
theorem fibre_delta (u v : ℕ → ℕ) (D : ℕ → ℤ) (L : ℕ)
    (hd : ∀ e, (v e : ℤ) = u e + D e) :
    (fibre v L : ℤ) = (fibre u L : ℤ) +
      ∑ e ∈ Finset.range L, D e * (10 : ℤ) ^ e := by
  rw [fibre_val u, fibre_val v]; push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [hd e]; ring

/-- Echange applique a la fibre : modifier u aux positions
    3i, 3i+1, 3i+2 par des deltas entiers d de somme nulle
    change la valeur de 9.10^{3i}.(d1 + 11.d2) (sur Z). -/
theorem fibre_exchange_delta (u v : ℕ → ℕ) (d : ℕ → ℤ) (L i : ℕ)
    (h3i : 3 * i + 2 < L)
    (hd : ∀ e, (v e : ℤ) = u e + d e)
    (hd0 : ∀ e, e ∉ ({3 * i, 3 * i + 1, 3 * i + 2} : Finset ℕ) → d e = 0)
    (hbal : d (3 * i) + d (3 * i + 1) + d (3 * i + 2) = 0) :
    (fibre v L : ℤ) = fibre u L +
      9 * 10 ^ (3 * i) * (d (3 * i + 1) + 11 * d (3 * i + 2)) := by
  rw [fibre_delta u v d L hd]; congr 1
  have hset : ({3 * i, 3 * i + 1, 3 * i + 2} : Finset ℕ) ⊆
      Finset.range L := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;>
      rw [Finset.mem_range] <;> omega
  rw [← Finset.sum_subset hset (fun e _ he => by
    have hde : d e = 0 := hd0 e he
    rw [hde]; simp)]
  have hi1 : 3 * i ∉ ({3 * i + 1, 3 * i + 2} : Finset ℕ) := by
    simp
  have hi2 : 3 * i + 1 ∉ ({3 * i + 2} : Finset ℕ) := by
    simp
  rw [Finset.sum_insert hi1, Finset.sum_insert hi2,
      Finset.sum_singleton]
  have h0d : d (3 * i) = -(d (3 * i + 1) + d (3 * i + 2)) := by
    omega
  have e1 : (10 : ℤ) ^ (3 * i + 1) = 10 * 10 ^ (3 * i) :=
    pow_succ' 10 (3 * i)
  have e2 : (10 : ℤ) ^ (3 * i + 2) = 10 * 10 ^ (3 * i + 1) :=
    pow_succ' 10 (3 * i + 1)
  rw [h0d, e1, e2]; ring

/-- Deltas equilibres sur s triplets disjoints {3j+3,3j+4,
    3j+5} (j < s) : la fibre change de la somme des
    9.10^{3(j+1)}.(D(3j+4) + 11 D(3j+5)). -/
theorem fibre_stages_delta (u v : ℕ → ℕ) (D : ℕ → ℤ) (L s : ℕ)
    (hL : 3 * s + 3 ≤ L)
    (hd : ∀ e, (v e : ℤ) = u e + D e)
    (hT : ∀ e, e ∉ (Finset.range s).biUnion
        (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) → D e = 0)
    (hbal : ∀ j < s,
        D (3*j+3) + D (3*j+4) + D (3*j+5) = 0) :
    (fibre v L : ℤ) = (fibre u L : ℤ) + ∑ j ∈ Finset.range s,
      9 * 10 ^ (3*(j+1)) * (D (3*j+4) + 11 * D (3*j+5)) := by
  rw [fibre_delta u v D L hd]; congr 1
  have hsub : (Finset.range s).biUnion
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) ⊆
      Finset.range L := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨j, hj, hxt⟩ := hx
    rw [Finset.mem_range] at hj ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxt
    rcases hxt with rfl | rfl | rfl <;> omega
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ)
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) := by
    intro j _ j' _ hjj'
    rw [Function.onFun]
    refine Finset.disjoint_left.mpr fun a ha hb => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with h | h | h <;> omega
  rw [← Finset.sum_subset hsub (fun e _ he => by
    have hde : D e = 0 := hT e he
    rw [hde]; simp)]
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hi1 : 3*j+3 ∉ ({3*j+4, 3*j+5} : Finset ℕ) := by simp
  have hi2 : 3*j+4 ∉ ({3*j+5} : Finset ℕ) := by simp
  rw [Finset.sum_insert hi1, Finset.sum_insert hi2,
      Finset.sum_singleton]
  have h0 : D (3*j+3) = -(D (3*j+4) + D (3*j+5)) := by
    have := hbal j hj; omega
  have e1 : (10 : ℤ) ^ (3*j+4) = 10 * 10 ^ (3*j+3) :=
    pow_succ' 10 (3*j+3)
  have e2 : (10 : ℤ) ^ (3*j+5) = 10 * 10 ^ (3*j+4) :=
    pow_succ' 10 (3*j+4)
  have e3 : 3*(j+1) = 3*j+3 := by ring
  rw [h0, e2, e1, e3]; ring

/-- Les chiffres de la fibre sont exactement les 1 + u_e
    (des que u_e <= 8). -/
theorem fibre_digits (u : ℕ → ℕ) (L : ℕ) (hu : ∀ e < L, u e ≤ 8) :
    Nat.digits 10 (fibre u L) = (List.range L).map fun e => 1 + u e := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro d hd
    rw [List.mem_map] at hd
    obtain ⟨e, he, rfl⟩ := hd
    have := hu e (List.mem_range.mp he)
    omega
  · intro hne
    have hL : 0 < L := by
      rcases Nat.eq_zero_or_pos L with rfl | h
      · simp at hne
      · exact h
    have : ((List.range L).map fun e => 1 + u e).getLast hne
        = 1 + u (L - 1) := by
      simp [List.getLast_map, List.getLast_range (by simpa using hL.ne')]
    rw [this]; omega

/-- sigma(H) = L + somme u_e ; en particulier = L + K si
    somme u_e = K. -/
theorem fibre_sigma (u : ℕ → ℕ) (L : ℕ) (hu : ∀ e < L, u e ≤ 8) :
    sigma10 (fibre u L) = L + ((List.range L).map u).sum := by
  rw [sigma10, fibre_digits u L hu]
  have hgen : ∀ l : List ℕ,
      ((l.map fun e => 1 + u e).sum) = l.length + (l.map u).sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
          List.length_cons, ih]; omega
  rw [hgen, List.length_range]

/-- Alignement : g = gcd(9,m) divise toujours n des que m | n
    (la condition g | sigma_total est donc automatique
    puisque sigma_total = n). -/
theorem align_trivial (g m n : ℕ) (hgm : g = Nat.gcd 9 m) (hmn : m ∣ n) :
    g ∣ n :=
  Nat.dvd_trans (hgm ▸ Nat.gcd_dvd_right 9 m) hmn

/-- Assemblage final : si B et H sont a chiffres non nuls,
    B /= 0, et n divise B + 10^{len B}.H, alors N = B + 10^d.H
    est un temoin de l existence (somme sigma B + sigma H,
    au moins 2 chiffres des que len B + len H >= 2). -/
theorem assemble (n B H : ℕ) (hB : B ≠ 0)
    (hnonB : allNonzero B) (hnonH : allNonzero H)
    (hdiv : n ∣ B + 10 ^ (Nat.digits 10 B).length * H)
    (hsum : sigma10 B + sigma10 H = n)
    (hlen : 2 ≤ (Nat.digits 10 B).length + (Nat.digits 10 H).length) :
    ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        (Nat.digits 10 N).length ≥ 2 := by
  refine ⟨B + 10 ^ (Nat.digits 10 B).length * H, hdiv, ?_, ?_, ?_⟩
  · rw [nonzero_concat B H hB, hnonB, hnonH]; rfl
  · rw [sigma_concat B H hB]; exact hsum
  · rw [digits_concat B H hB, List.length_append]; exact hlen

/-- Division coprime : si R et m copremiers divisent N,
    alors R.m | N. -/
theorem coprime_mul_dvd {R m N : ℕ} (hcop : Nat.Coprime R m)
    (hR : R ∣ N) (hm : m ∣ N) : R * m ∣ N :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hR hm

/-- Reduction mod R : si R | 10^d et R | B, alors
    R | B + 10^d.H (le bloc bas absorbe la fibre). -/
theorem dvd_concat_base (R B H d : ℕ) (hR10 : R ∣ 10 ^ d)
    (hRB : R ∣ B) : R ∣ B + 10 ^ d * H :=
  dvd_add hRB (dvd_mul_of_dvd_left hR10 H)

/- DETTE CENTRALE (papier SS4-SS6) : pour m coprime a 10, tout
    residu t est atteint par une fibre a L positions et somme
    4L + r0 des que L >= 3s+4, s = ceil((M-1)/(U-1)) avec
    U in {16,28} (s <= m/27+1 dans le pire cas 3∤M).
    Contenu : grille d echange X (60 valeurs, echange
    9.10^{3i}(d1+11d2)), sous-ensembles d unites garanties. -/

/-- Le scalaire 9/g est premier avec M = m/g (g = gcd(9,m)) :
    c'est ce qui rend chaque facteur d'etage une unite mod M. -/
theorem scalar_unit (m : ℕ) :
    Nat.Coprime (9 / Nat.gcd 9 m) (m / Nat.gcd 9 m) :=
  Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left m (by norm_num))

/-- L'ensemble d'etage B* i dans ZMod M : {0} union
    {(9/g).10^{3i}.x mod M} pour x dans la liste d'unites. -/
def stageSet (M i g : ℕ) (xs : List ℤ) : Finset (ZMod M) :=
  {0} ∪ (xs.toFinset.image fun (x : ℤ) =>
    ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M) * (x : ZMod M))

theorem zero_mem_stageSet (M i g : ℕ) (xs : List ℤ) :
    (0 : ZMod M) ∈ stageSet M i g xs :=
  Finset.mem_union_left _ (Finset.mem_singleton_self 0)

/-- Les elements non nuls d'un etage sont des unites, des que
    9/g, 10 et chaque x de la liste sont des unites mod M. -/
theorem stageSet_units (M i g : ℕ) (xs : List ℤ)
    (hsc : IsUnit ((9 / g : ℕ) : ZMod M))
    (h10 : IsUnit ((10 : ℕ) : ZMod M))
    (hx : ∀ x ∈ xs, IsUnit (x : ZMod M)) :
    ∀ b ∈ stageSet M i g xs, b = 0 ∨ IsUnit b := by
  intro b hb
  rw [stageSet, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image] at hb
  rcases hb with rfl | ⟨x, hxs, rfl⟩
  · exact Or.inl rfl
  · right
    exact ((hsc.mul (h10.pow _)).mul (hx x (List.mem_toFinset.mp hxs)))

/-- Cardinal d'un etage : pour M > 184, les x distincts
    donnent des residus distincts (l'injectivite vient du cast
    et de la multiplication par l'unite), et 0 n'est pas
    atteint, donc |B*_i| = |xs| + 1. -/
theorem stageSet_card (M i g : ℕ) (xs : List ℤ)
    (hM : 184 < M) (hsc : IsUnit ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M))
    (hnd : xs.Nodup) (hxb : ∀ x ∈ xs, |x| ≤ 92)
    (hx0 : ∀ x ∈ xs, x ≠ 0) :
    (stageSet M i g xs).card = xs.length + 1 := by
  have hc0 : ∀ x ∈ xs, (x : ZMod M) ≠ 0 := by
    intro x hx hxe
    rw [CharP.intCast_eq_zero_iff (ZMod M) M] at hxe
    have h2 : M ∣ x.natAbs := Int.natCast_dvd.mp hxe
    have h3 : x.natAbs ≤ 92 := by
      have h := hxb x hx
      rw [← Int.natCast_natAbs x] at h
      exact_mod_cast h
    have h4 : x.natAbs = 0 :=
      Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    exact hx0 x hx (Int.natAbs_eq_zero.mp h4)
  have hinj : Set.InjOn (fun (x : ℤ) =>
      ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M) * (x : ZMod M))
      (↑xs.toFinset : Set ℤ) := by
    intro x hx y hy hxy
    have hxy' : (x : ZMod M) = (y : ZMod M) :=
      hsc.mul_right_inj.mp hxy
    rw [Finset.mem_coe, List.mem_toFinset] at hx hy
    rw [ZMod.intCast_eq_intCast_iff] at hxy'
    have hdvd : (M : ℤ) ∣ (y - x) := Int.modEq_iff_dvd.mp hxy'
    have h2 : M ∣ (y - x).natAbs := Int.natCast_dvd.mp hdvd
    have hlt : (y - x).natAbs < M := by
      have h1 := hxb x hx; have h2' := hxb y hy
      have hb : |y - x| ≤ (184 : ℤ) := by
        have hx' := abs_le.mp h1
        have hy' := abs_le.mp h2'
        exact abs_le.mpr ⟨by omega, by omega⟩
      have hlt' : (|y - x| : ℤ) < M :=
        lt_of_le_of_lt hb (by exact_mod_cast hM)
      rw [← Int.natCast_natAbs] at hlt'
      exact_mod_cast hlt'
    have h0 : (y - x).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt h2 hlt
    exact (sub_eq_zero.mp (Int.natAbs_eq_zero.mp h0)).symm
  have h0im : (0 : ZMod M) ∉ xs.toFinset.image fun (x : ℤ) =>
      ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M) * (x : ZMod M) := by
    intro h
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, hxe⟩ := h
    have hx' : x ∈ xs := List.mem_toFinset.mp hx
    have : (x : ZMod M) = 0 := hsc.mul_right_eq_zero.mp hxe
    exact hc0 x hx' this
  rw [stageSet, Finset.singleton_union,
      Finset.card_insert_of_notMem h0im,
      Finset.card_image_of_injOn hinj,
      List.toFinset_card_of_nodup hnd]

/-- Tout element de la liste 16 ({2,5}-smooth) a sa valeur
    absolue divisant 160 ; pour M coprime a 10 c'est donc une
    unite mod M. -/
theorem xunit25 (M : ℕ) (hM : Nat.Coprime M 10) :
    ∀ x ∈ Xsmooth25, IsUnit (x : ZMod M) := by
  have h160 : (160 : ℕ).Coprime M := by
    have h10 : (10 : ℕ).Coprime M := Nat.coprime_comm.mp hM
    have h2 : (2 : ℕ).Coprime M := h10.coprime_dvd_left (by norm_num)
    have h5 : (5 : ℕ).Coprime M := h10.coprime_dvd_left (by norm_num)
    have h25 : (2 ^ 5 : ℕ).Coprime M :=
      (Nat.coprime_pow_left_iff (show 0 < 5 by norm_num) 2 M).mpr h2
    rw [show (160 : ℕ) = 2 ^ 5 * 5 by norm_num]
    exact (Nat.coprime_mul_iff_left).mpr ⟨h25, h5⟩
  intro x hx
  have hxd : x.natAbs ∣ 160 := by fin_cases hx <;> decide
  have hxu : IsUnit ((x.natAbs : ℕ) : ZMod M) := by
    rw [ZMod.isUnit_iff_coprime]
    exact h160.coprime_dvd_left hxd
  rcases Int.natAbs_eq x with h | h
  · rw [h, Int.cast_natCast]; exact hxu
  · rw [h, Int.cast_neg, Int.cast_natCast]
    exact hxu.neg

/-- Tout element de la liste 28 ({2,3,5}-smooth) a sa valeur
    absolue divisant 2880 ; pour M coprime a 30 c'est une
    unite mod M. -/
theorem xunit235 (M : ℕ) (hM : Nat.Coprime M 30) :
    ∀ x ∈ Xsmooth235, IsUnit (x : ZMod M) := by
  have h2880 : (2880 : ℕ).Coprime M := by
    have h30 : (30 : ℕ).Coprime M := Nat.coprime_comm.mp hM
    have h2 : (2 : ℕ).Coprime M := h30.coprime_dvd_left (by norm_num)
    have h3 : (3 : ℕ).Coprime M := h30.coprime_dvd_left (by norm_num)
    have h5 : (5 : ℕ).Coprime M := h30.coprime_dvd_left (by norm_num)
    have h26 : (2 ^ 6 : ℕ).Coprime M :=
      (Nat.coprime_pow_left_iff (show 0 < 6 by norm_num) 2 M).mpr h2
    have h32 : (3 ^ 2 : ℕ).Coprime M :=
      (Nat.coprime_pow_left_iff (show 0 < 2 by norm_num) 3 M).mpr h3
    rw [show (2880 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 by norm_num]
    exact (Nat.coprime_mul_iff_left).mpr
      ⟨(Nat.coprime_mul_iff_left).mpr ⟨h26, h32⟩, h5⟩
  intro x hx
  have hxd : x.natAbs ∣ 2880 := by fin_cases hx <;> decide
  have hxu : IsUnit ((x.natAbs : ℕ) : ZMod M) := by
    rw [ZMod.isUnit_iff_coprime]
    exact h2880.coprime_dvd_left hxd
  rcases Int.natAbs_eq x with h | h
  · rw [h, Int.cast_natCast]; exact hxu
  · rw [h, Int.cast_neg, Int.cast_natCast]
    exact hxu.neg

/-- Appartenance a une somme d'etages : x in sum_j B j ssi il
    existe des choix f j in B j dont x est la somme. -/
theorem mem_sum_range {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (B : ℕ → Finset α) (x : α) :
    ∀ s : ℕ, x ∈ ∑ j ∈ Finset.range s, B j ↔
      ∃ f : ℕ → α, (∀ j < s, f j ∈ B j) ∧
        x = ∑ j ∈ Finset.range s, f j := by
  intro s
  induction s generalizing x with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, Finset.mem_add]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨f, hf, rfl⟩ := (ih a).mp ha
      refine ⟨Function.update f s b, fun j hj => ?_, ?_⟩
      · rcases Nat.lt_or_ge j s with h | h
        · rw [Function.update_of_ne (Nat.ne_of_lt h)]
          exact hf j h
        · have hjs : j = s := by omega
          subst hjs
          rw [Function.update_self]
          exact hb
      · rw [Finset.sum_range_succ, Function.update_self]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (by
          rw [Finset.mem_range] at hj; omega)]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨∑ j ∈ Finset.range s, f j, ?_, f s, hf s (by simp),
        by rw [Finset.sum_range_succ]⟩
      exact (ih _).mpr ⟨f, fun j hj => hf j (by omega), rfl⟩

/-- Inversion de la grille : x in Xgrid ssi x = d1 + 11.d2
    avec (d1,d2) in [-4,4]^2, |d1+d2| <= 4, x /= 0.
    Le d0 equilibrant est alors -(d1+d2) in [-4,4]. -/
theorem mem_XR_iff (d : ℤ) :
    d ∈ ((List.range 9).map fun (i : ℕ) => (i : ℤ) - 4) ↔
      -4 ≤ d ∧ d ≤ 4 := by
  constructor
  · intro h
    fin_cases h <;> decide
  · intro ⟨h1, h2⟩
    interval_cases d <;> decide

theorem Xgrid_mem_iff (x : ℤ) :
    x ∈ Xgrid ↔ ∃ d1 d2 : ℤ, -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧
      d2 ≤ 4 ∧ -4 ≤ d1 + d2 ∧ d1 + d2 ≤ 4 ∧
      x = d1 + 11 * d2 ∧ x ≠ 0 := by
  constructor
  · intro hx
    unfold Xgrid at hx
    rw [List.mem_filterMap] at hx
    obtain ⟨⟨d1, d2⟩, hp, hopt⟩ := hx
    dsimp only at hopt
    replace hp : (d1, d2) ∈
        ((List.range 9).map fun i => (i : ℤ) - 4) ×ˢ
        ((List.range 9).map fun i => (i : ℤ) - 4) := hp
    rw [List.mem_product] at hp
    replace hp : d1 ∈
        (List.range 9).map (fun i : ℕ => (i : ℤ) - 4) ∧
        d2 ∈ (List.range 9).map (fun i : ℕ => (i : ℤ) - 4) := hp
    rw [mem_XR_iff, mem_XR_iff] at hp
    split at hopt
    · next hc =>
      obtain ⟨h1, h2, h3⟩ := hc
      injection hopt with hopt
      exact ⟨d1, d2, hp.1.1, hp.1.2, hp.2.1, hp.2.2, h1, h2,
        hopt.symm, hopt ▸ h3⟩
    · contradiction
  · rintro ⟨d1, d2, hd1a, hd1b, hd2a, hd2b, h1, h2, rfl, h3⟩
    unfold Xgrid
    rw [List.mem_filterMap]
    refine ⟨⟨d1, d2⟩, ?_, ?_⟩
    · show (d1, d2) ∈
        ((List.range 9).map fun i => (i : ℤ) - 4) ×ˢ
        ((List.range 9).map fun i => (i : ℤ) - 4)
      rw [List.mem_product]
      show d1 ∈ (List.range 9).map (fun i : ℕ => (i : ℤ) - 4) ∧
        d2 ∈ (List.range 9).map (fun i : ℕ => (i : ℤ) - 4)
      rw [mem_XR_iff, mem_XR_iff]
      exact ⟨⟨hd1a, hd1b⟩, ⟨hd2a, hd2b⟩⟩
    · dsimp only
      rw [if_pos ⟨h1, h2, h3⟩]

theorem zero_mem_sum_range {α : Type*} [AddCommMonoid α]
    [DecidableEq α] (s : ℕ) (B : ℕ → Finset α)
    (h0 : ∀ j, (0 : α) ∈ B j) :
    (0 : α) ∈ ∑ j ∈ Finset.range s, B j := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    simpa using Finset.add_mem_add ih (h0 s)

/-- Iteration de Chowla : si chaque B_j contient 0, que tout
    element non nul de B_j est une unite, et que |B_j| >= q+1,
    alors la somme des s premiers etages a cardinal >=
    min(k, s*q+1) (k = card de l'anneau). -/
theorem sumset_stages (k q : ℕ) [NeZero k]
    (B : ℕ → Finset (ZMod k)) (h0 : ∀ j, (0 : ZMod k) ∈ B j)
    (hu : ∀ j, ∀ x ∈ B j, x ≠ 0 → IsUnit x)
    (hq : ∀ j, q + 1 ≤ (B j).card) (s : ℕ) :
    min k (s * q + 1) ≤
      (∑ j ∈ Finset.range s, B j).card := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have hle : (∑ j ∈ Finset.range s, B j).card ≤
        ((∑ j ∈ Finset.range s, B j) + B s).card := by
      apply Finset.card_le_card
      intro x hx
      have hx' : x = x + (0 : ZMod k) := (add_zero x).symm
      rw [hx']
      exact Finset.add_mem_add hx (h0 s)
    have hchow := chowla k (∑ j ∈ Finset.range s, B j) (B s)
      ⟨(0 : ZMod k), zero_mem_sum_range _ _ h0⟩ (h0 s)
      (fun x hx => (eq_or_ne x 0).elim Or.inl
        (fun hne => Or.inr (hu s x hx hne)))
    have hcard : min k ((∑ j ∈ Finset.range s, B j).card +
        (B s).card - 1) ≤
        ((∑ j ∈ Finset.range s, B j) + B s).card := hchow
    rcases lt_or_ge (s * q + 1) k with hkc | hkc
    · have hSk : s * q + 1 ≤
          (∑ j ∈ Finset.range s, B j).card := by
        rwa [min_eq_right (le_of_lt hkc)] at ih
      calc min k ((s + 1) * q + 1)
          ≤ min k ((∑ j ∈ Finset.range s, B j).card +
              (B s).card - 1) := by
            apply min_le_min_left k
            have hB : q + 1 ≤ (B s).card := hq s
            have h0S : 0 < (∑ j ∈ Finset.range s, B j).card :=
              Finset.card_pos.mpr
                ⟨(0 : ZMod k), zero_mem_sum_range _ _ h0⟩
            rw [show (s + 1) * q + 1 = s * q + q + 1 from by ring]
            omega
        _ ≤ ((∑ j ∈ Finset.range s, B j) + B s).card := hcard
    · -- la somme partielle atteint deja l'univers
      have hSk : k ≤ (∑ j ∈ Finset.range s, B j).card := by
        rwa [min_eq_left hkc] at ih
      have huniv : (∑ j ∈ Finset.range s, B j) =
          Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [ZMod.card]
        refine le_antisymm ?_ hSk
        have h := Finset.card_le_univ
          (∑ j ∈ Finset.range s, B j)
        rwa [ZMod.card] at h
      have hsub : (Finset.univ : Finset (ZMod k)) ⊆
          (∑ j ∈ Finset.range s, B j) + B s := by
        rw [← huniv]
        intro x hx
        simpa using Finset.add_mem_add hx (h0 s)
      calc min k ((s + 1) * q + 1) ≤ k := min_le_left _ _
        _ = (Finset.univ : Finset (ZMod k)).card := by
            rw [Finset.card_univ, ZMod.card]
        _ ≤ ((∑ j ∈ Finset.range s, B j) + B s).card :=
            Finset.card_le_card hsub

/-- Couverture par les etages : si chaque etage a >= q+1
    elements (0 inclus) et s.q >= M-1, la somme des s etages
    est tout ZMod M. C'est sumset_stages applique aux B*_j. -/
theorem stage_cover (M g q s : ℕ) [NeZero M] (xs : List ℤ)
    (hM : 184 < M)
    (hsc : IsUnit ((9 / g : ℕ) : ZMod M))
    (h10 : IsUnit ((10 : ℕ) : ZMod M))
    (hxu : ∀ x ∈ xs, IsUnit (x : ZMod M))
    (hnd : xs.Nodup) (hxb : ∀ x ∈ xs, |x| ≤ 92)
    (hx0 : ∀ x ∈ xs, x ≠ 0)
    (hq : q ≤ xs.length) (hs : M ≤ s * q + 1) :
    ∑ j ∈ Finset.range s, stageSet M (j + 1) g xs = Finset.univ := by
  have hcard : ∀ j, (stageSet M (j + 1) g xs).card =
      xs.length + 1 := by
    intro j
    apply stageSet_card M (j + 1) g xs hM _ hnd hxb hx0
    push_cast
    exact hsc.mul (h10.pow _)
  have hsum := sumset_stages M q
    (fun j => stageSet M (j + 1) g xs)
    (fun j => zero_mem_stageSet _ _ _ _)
    (fun j x hx hx0 =>
      (stageSet_units _ _ _ _ hsc h10 hxu x hx).resolve_left hx0)
    (fun j => by rw [hcard j]; omega)
    s
  rw [min_eq_left hs] at hsum
  have hle2 : (∑ j ∈ Finset.range s, stageSet M (j + 1) g xs).card
      ≤ M := by
    have h := Finset.card_le_univ
      (∑ j ∈ Finset.range s, stageSet M (j + 1) g xs)
    rwa [ZMod.card] at h
  have hfc : Fintype.card (ZMod M) = M := ZMod.card M
  exact Finset.eq_univ_of_card _ (by omega)

/- La cible de couverture : pour L assez grand, tout residu t
    dans le coset compatible (t ≡ L+K mod g) est atteint par une
    fibre de longueur L et somme L+K — c'est-a-dire par une
    fonction u avec u_e <= 8 et somme K = 4L+r0. La preuve
    assemble : dichotomie 3|M (16 unites) / 3 non|M (28 unites),
    couverture par sumset_stages, machine M<=600, alignement
    du coset (g | 9 automatique car g | n), traduction du
    residu en la fonction u. -/

/-- Fonction de base des fibres : u = 4 partout, plus 1 sur r0
    positions libres — les positions 0,1,2 tant que e < r0, et
    3s+3 quand r0 = 4. Les triplets d'echange {3j+3,3j+4,3j+5},
    j < s, ne rencontrent jamais ces positions libres. -/
def ubase (s r0 : ℕ) (e : ℕ) : ℕ :=
  if (e < 3 ∧ e < r0) ∨ (e = 3 * s + 3 ∧ r0 = 4) then 5 else 4

theorem ubase_le (s r0 : ℕ) (hr0 : r0 ≤ 4) (e : ℕ) :
    ubase s r0 e ≤ 8 := by
  rw [ubase]; split_ifs <;> omega

/-- Les triplets d'echange portent la valeur de base 4 :
    indispensable pour que les offsets d in [-4,4] gardent
    u dans [0,8]. -/
theorem ubase_triple (s r0 : ℕ) (j e : ℕ) (hj : j < s)
    (he : e ∈ ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) :
    ubase s r0 e = 4 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rw [ubase, if_neg]
  push_neg
  refine ⟨by omega, fun h => ?_⟩
  rcases he with rfl | rfl | rfl <;> omega

/-- Hors du support (positions >= 3s+4), ubase vaut 4. -/
theorem ubase_out (s r0 e : ℕ) (he : 3 * s + 4 ≤ e) :
    ubase s r0 e = 4 := by
  rw [ubase, if_neg]; push_neg
  refine ⟨by omega, fun h => by omega⟩

/-- Somme de la base auxiliaire : la somme vaut 4L plus le
    nombre de positions libres presentes dans [0,L). -/
theorem ubase_sum_aux (s r0 L : ℕ) :
    ((List.range L).map (ubase s r0)).sum = 4 * L +
      (if 0 < L ∧ 0 < r0 then 1 else 0) +
      (if 1 < L ∧ 1 < r0 then 1 else 0) +
      (if 2 < L ∧ 2 < r0 then 1 else 0) +
      (if 3 * s + 3 < L ∧ r0 = 4 then 1 else 0) := by
  induction' L with L ih
  · simp
  · rw [List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, ih]
    dsimp [ubase]
    split_ifs <;> omega

/-- Somme de la base : Σ_{e<L} ubase e = 4L + r0 des que la
    position libre haute 3s+3 est dans la fibre (L >= 3s+4). -/
theorem ubase_sum (s r0 L : ℕ) (hr0 : r0 ≤ 4)
    (hL : 3 * s + 4 ≤ L) :
    ((List.range L).map (ubase s r0)).sum = 4 * L + r0 := by
  rw [ubase_sum_aux]
  split_ifs <;> omega

/-- Somme des deltas portes par les s triplets equilibres :
    elle est nulle (chaque triplet somme a 0). -/
theorem sum_stages_zero (D : ℕ → ℤ) (L s : ℕ)
    (hL : 3 * s + 3 ≤ L)
    (hT : ∀ e, e ∉ (Finset.range s).biUnion
        (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) → D e = 0)
    (hbal : ∀ j < s,
        D (3*j+3) + D (3*j+4) + D (3*j+5) = 0) :
    ∑ e ∈ Finset.range L, D e = 0 := by
  have hsub : (Finset.range s).biUnion
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) ⊆
      Finset.range L := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨j, hj, hxt⟩ := hx
    rw [Finset.mem_range] at hj ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxt
    rcases hxt with rfl | rfl | rfl <;> omega
  rw [← Finset.sum_subset hsub (fun e _ he => by
    have hde : D e = 0 := hT e he
    rw [hde])]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ)
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) := by
    intro j _ j' _ hjj'
    rw [Function.onFun]
    refine Finset.disjoint_left.mpr fun a ha hb => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with h | h | h <;> omega
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  have hi1 : 3*j+3 ∉ ({3*j+4, 3*j+5} : Finset ℕ) := by simp
  have hi2 : 3*j+4 ∉ ({3*j+5} : Finset ℕ) := by simp
  rw [Finset.sum_insert hi1, Finset.sum_insert hi2,
      Finset.sum_singleton]
  have := hbal j hj; omega

/-- Assemblage de la fonction u a partir d'une suite de
    valeurs de grille x_j (delta d'etage = 9.10^{3(j+1)}.x_j) :
    chaque x_j se decompose en d1 + 11.d2 (grille) ou vaut 0,
    on pose D(3j+3) = -(d1+d2), D(3j+4) = d1, D(3j+5) = d2,
    et u = ubase + D. Alors u in [0,8], somme 4L+r0, et la
    fibre bouge de la somme des deltas d'etage. -/
theorem build_u (s r0 L : ℕ) (hs : 3 * s + 4 ≤ L) (hr0 : r0 ≤ 4)
    (x : ℕ → ℤ)
    (hx : ∀ j < s, (x j = 0) ∨ ∃ d1 d2 : ℤ,
      -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧ d2 ≤ 4 ∧
      -4 ≤ d1 + d2 ∧ d1 + d2 ≤ 4 ∧ x j = d1 + 11 * d2) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 ∧
      ((fibre u L : ℤ) = (fibre (ubase s r0) L : ℤ) +
        ∑ j ∈ Finset.range s,
          9 * 10 ^ (3 * (j + 1)) * x j) := by
  classical
  -- decomposition de grille par choix, (0,0) si x j = 0
  have hdx : ∀ j < s, ∃ d1 d2 : ℤ,
      -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧ d2 ≤ 4 ∧
      -4 ≤ d1 + d2 ∧ d1 + d2 ≤ 4 ∧ x j = d1 + 11 * d2 := by
    intro j hj
    rcases hx j hj with h0 | h
    · exact ⟨0, 0, by omega, by omega, by omega, by omega,
        by omega, by omega, by rw [h0]; ring⟩
    · exact h
  choose! d1 d2 hd using hdx
  -- delta sur les triplets : position e = 3 + (3j + r), r<3
  let D : ℕ → ℤ := fun e =>
    if 3 ≤ e ∧ e < 3 * s + 3 then
      (let j := (e - 3) / 3
       let r := (e - 3) % 3
       if r = 0 then -(d1 j + d2 j)
       else if r = 1 then d1 j else d2 j)
    else 0
  have hDt : ∀ j < s, D (3*j+3) = -(d1 j + d2 j) ∧
      D (3*j+4) = d1 j ∧ D (3*j+5) = d2 j := by
    intro j hj
    have hc1 : 3 ≤ 3*j+3 ∧ 3*j+3 < 3*s+3 := ⟨by omega, by omega⟩
    have hc2 : 3 ≤ 3*j+4 ∧ 3*j+4 < 3*s+3 := ⟨by omega, by omega⟩
    have hc3 : 3 ≤ 3*j+5 ∧ 3*j+5 < 3*s+3 := ⟨by omega, by omega⟩
    have e1 : (3*j+3) - 3 = 3*j := by omega
    have e2 : (3*j+4) - 3 = 3*j+1 := by omega
    have e3 : (3*j+5) - 3 = 3*j+2 := by omega
    have q1 : (3*j+3-3)/3 = j := by rw [e1]; omega
    have q2 : (3*j+4-3)/3 = j := by rw [e2]; omega
    have q3 : (3*j+5-3)/3 = j := by rw [e3]; omega
    have r1 : (3*j+3-3)%3 = 0 := by rw [e1]; omega
    have r2 : (3*j+4-3)%3 = 1 := by rw [e2]; omega
    have r3 : (3*j+5-3)%3 = 2 := by rw [e3]; omega
    simp only [D]
    rw [if_pos hc1, if_pos hc2, if_pos hc3]
    simp only [q1, q2, q3, r1, r2, r3]
    norm_num
  have hT : ∀ e, e ∉ (Finset.range s).biUnion
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) →
      D e = 0 := by
    intro e he
    simp only [D]
    by_cases hcond : 3 ≤ e ∧ e < 3 * s + 3
    · exfalso
      apply he
      rw [Finset.mem_biUnion]
      refine ⟨(e - 3) / 3, ?_, ?_⟩
      · rw [Finset.mem_range]
        have := hcond.2
        omega
      · have h3 : e = 3 * ((e - 3) / 3) + 3 + (e - 3) % 3 := by
          have hdv := Nat.div_add_mod (e - 3) 3
          omega
        have hm : (e - 3) % 3 < 3 := Nat.mod_lt _ (by norm_num)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases (by omega : (e-3) % 3 = 0 ∨ (e-3) % 3 = 1 ∨
            (e-3) % 3 = 2) with hr | hr | hr
        · left; rw [hr] at h3; omega
        · right; left; rw [hr] at h3; omega
        · right; right; rw [hr] at h3; omega
    · rw [if_neg hcond]
  have hbal : ∀ j < s,
      D (3*j+3) + D (3*j+4) + D (3*j+5) = 0 := by
    intro j hj
    obtain ⟨e1, e2, e3⟩ := hDt j hj
    rw [e1, e2, e3]; ring
  -- u = ubase + D (positif : ubase = 4 sur les triplets)
  have hnn : ∀ e, 0 ≤ (ubase s r0 e : ℤ) + D e := by
    intro e
    by_cases hc : 3 ≤ e ∧ e < 3 * s + 3
    · have hj : (e - 3) / 3 < s := by omega
      have hub : ubase s r0 e = 4 := by
        apply ubase_triple s r0 ((e-3)/3) e hj
        have h3 : e = 3 * ((e - 3) / 3) + 3 + (e - 3) % 3 := by
          have hdv := Nat.div_add_mod (e - 3) 3
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases (by omega : (e-3) % 3 = 0 ∨ (e-3) % 3 = 1 ∨
            (e-3) % 3 = 2) with hr | hr | hr
        · left; rw [hr] at h3; omega
        · right; left; rw [hr] at h3; omega
        · right; right; rw [hr] at h3; omega
      rw [hub]
      simp only [D]
      rw [if_pos hc]
      have hb := hd ((e-3)/3) hj
      obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hb
      by_cases hr0' : (e-3) % 3 = 0
      · rw [if_pos hr0']; omega
      · by_cases hr1' : (e-3) % 3 = 1
        · rw [if_neg hr0', if_pos hr1']; omega
        · rw [if_neg hr0', if_neg hr1']; omega
    · simp only [D]; rw [if_neg hc]
      have := ubase_le s r0 hr0 e; omega
  have hle8 : ∀ e < L,
      (Int.toNat ((ubase s r0 e : ℤ) + D e)) ≤ 8 := by
    intro e _
    by_cases hc : 3 ≤ e ∧ e < 3 * s + 3
    · have hj : (e - 3) / 3 < s := by omega
      have hub : ubase s r0 e = 4 := by
        apply ubase_triple s r0 ((e-3)/3) e hj
        have h3 : e = 3 * ((e - 3) / 3) + 3 + (e - 3) % 3 := by
          have hdv := Nat.div_add_mod (e - 3) 3
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases (by omega : (e-3) % 3 = 0 ∨ (e-3) % 3 = 1 ∨
            (e-3) % 3 = 2) with hr | hr | hr
        · left; rw [hr] at h3; omega
        · right; left; rw [hr] at h3; omega
        · right; right; rw [hr] at h3; omega
      rw [hub]
      simp only [D]
      rw [if_pos hc]
      have hb := hd ((e-3)/3) hj
      obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hb
      rw [Int.toNat_le]
      by_cases hr0' : (e-3) % 3 = 0
      · rw [if_pos hr0']; omega
      · by_cases hr1' : (e-3) % 3 = 1
        · rw [if_neg hr0', if_pos hr1']; omega
        · rw [if_neg hr0', if_neg hr1']; omega
    · simp only [D]; rw [if_neg hc]
      rw [Int.toNat_le]
      have := ubase_le s r0 hr0 e; omega
  refine ⟨fun e => Int.toNat ((ubase s r0 e : ℤ) + D e),
    hle8, ?_, ?_⟩
  · -- somme : identique a ubase car Σ D = 0
    have hcast : ∀ e, ((Int.toNat
        ((ubase s r0 e : ℤ) + D e) : ℕ) : ℤ) =
        (ubase s r0 e : ℤ) + D e := fun e =>
      Int.toNat_of_nonneg (hnn e)
    have hsumD : ∑ e ∈ Finset.range L, D e = 0 :=
      sum_stages_zero D L s (by omega) hT hbal
    have hFE : ∀ (f : ℕ → ℕ) (n : ℕ),
        ((List.range n).map f).sum =
          ∑ e ∈ Finset.range n, f e := by
      intro f n; induction n with
      | zero => simp
      | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton, ih,
            Finset.sum_range_succ]
    rw [hFE, ← Nat.cast_inj (R := ℤ), Nat.cast_sum]
    calc ∑ e ∈ Finset.range L,
          ((Int.toNat ((ubase s r0 e : ℤ) + D e) : ℕ) : ℤ)
        = ∑ e ∈ Finset.range L, ((ubase s r0 e : ℤ) + D e) :=
          Finset.sum_congr rfl fun e _ => hcast e
      _ = (∑ e ∈ Finset.range L, (ubase s r0 e : ℤ)) + 0 := by
          rw [Finset.sum_add_distrib, hsumD]
      _ = ((4 * L + r0 : ℕ) : ℤ) := by
          rw [add_zero, ← Nat.cast_sum]
          congr 1
          rw [← hFE]
          exact ubase_sum s r0 L hr0 (by omega)
  · -- fibre : fibre_stages_delta
    have hd' : ∀ e, ((Int.toNat
        ((ubase s r0 e : ℤ) + D e) : ℕ) : ℤ) =
        ubase s r0 e + D e := fun e =>
      Int.toNat_of_nonneg (hnn e)
    have hf := fibre_stages_delta (ubase s r0)
      (fun e => Int.toNat ((ubase s r0 e : ℤ) + D e)) D L s
      (by omega) hd' hT hbal
    rw [hf]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨e1, e2, e3⟩ := hDt j hj
    rw [e2, e3]
    have := hd j hj
    obtain ⟨-, -, -, -, -, -, hxeq⟩ := this
    rw [hxeq]

/-- g = gcd(9,m) est l'un de 1, 3, 9 (diviseur de 9 = 3^2). -/
theorem gcd9mem (m : ℕ) :
    Nat.gcd 9 m = 1 ∨ Nat.gcd 9 m = 3 ∨ Nat.gcd 9 m = 9 := by
  have h : Nat.gcd 9 m ∣ 9 := Nat.gcd_dvd_left 9 m
  obtain ⟨k, hk, hke⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.gcd 9 m ∣ 3 ^ 2 from h)
  rw [hke]
  interval_cases k <;> simp

/-- Couverture machine : pour M <= 184 coprime a 10 (les cas
    realisables : g in {1,3,9} avec 3 non|M quand g < 9), la
    somme de 6 etages couvre tout ZMod M. -/
theorem stage_cover_small_aux :
    ((List.range' 1 184).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((((!(Nat.gcd M 3 == 1)) ||
          (decide ((∑ j ∈ Finset.range 6,
              stageSet M (j+1) 1 Xsmooth235 : Finset (ZMod M)).card
            = M)) &&
          (decide ((∑ j ∈ Finset.range 6,
              stageSet M (j+1) 3 Xsmooth25 : Finset (ZMod M)).card
            = M))) &&
        (decide ((∑ j ∈ Finset.range 6,
            stageSet M (j+1) 9 Xsmooth25 : Finset (ZMod M)).card
          = M))))) = true := by
  native_decide

theorem stage_cover_small (M g : ℕ) [NeZero M] (hM : M ≤ 184)
    (hcop : Nat.Coprime M 10)
    (hg : g = 1 ∨ g = 3 ∨ g = 9)
    (hg3 : g = 1 ∨ g = 3 → ¬ (3 ∣ M)) :
    ∑ j ∈ Finset.range 6, stageSet M (j+1) g
      (if g = 1 then Xsmooth235 else Xsmooth25)
      = Finset.univ := by
  have hM1 : 1 ≤ M := NeZero.pos M
  have hmem : M ∈ List.range' 1 184 := by
    apply List.mem_range'.mpr
    exact ⟨M - 1, by omega, by omega⟩
  have hall := List.all_eq_true.mp stage_cover_small_aux
    M hmem
  have hcopb : Nat.gcd M 10 = 1 := hcop
  rw [hcopb] at hall
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or]
    at hall
  rw [Bool.and_eq_true] at hall
  obtain ⟨h13, h9⟩ := hall
  have huniv : ∀ S : Finset (ZMod M), S.card = M →
      S = Finset.univ := fun S hS =>
    Finset.eq_univ_of_card S (by rw [hS, ZMod.card])
  rcases hg with rfl | rfl | rfl
  · have h3b : Nat.gcd M 3 = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.coprime_comm.mp
        (Nat.prime_three.coprime_iff_not_dvd.mpr
          (hg3 (Or.inl rfl))))
    rw [h3b] at h13
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or,
      Bool.and_eq_true] at h13
    rw [if_pos rfl]
    exact huniv _ (of_decide_eq_true h13.1)
  · have h3b : Nat.gcd M 3 = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.coprime_comm.mp
        (Nat.prime_three.coprime_iff_not_dvd.mpr
          (hg3 (Or.inr rfl))))
    rw [h3b] at h13
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or,
      Bool.and_eq_true] at h13
    rw [if_neg (by norm_num)]
    exact huniv _ (of_decide_eq_true h13.2)
  · rw [if_neg (by norm_num)]
    exact huniv _ (of_decide_eq_true h9)

/-- Pour les trois moduls du coin (11, 19, 23) : 2 etages de
    Xsmooth235 couvrent ZMod m entier (g = 1 dans ces cas). -/
theorem stage_cover_2 (M g : ℕ) [NeZero M] (xs : List ℤ)
    (hM : M = 11 ∨ M = 19 ∨ M = 23) (hg : g = 1)
    (hxs : xs = Xsmooth235) :
    ∑ j ∈ Finset.range 2, stageSet M (j + 1) g xs =
      Finset.univ := by
  subst hg; subst hxs
  rcases hM with rfl | rfl | rfl <;>
    apply Finset.eq_univ_of_card <;>
    rw [ZMod.card] <;>
    native_decide

/-- Certificat machine : pour tout m <= 1656 premier a 10 hors
    {11,19,23} avec M = m / gcd(9,m) <= 184, il existe
    k <= m/27+1 etages couvrant ZMod M. -/
theorem stage_cover_small_aux' :
    ((List.range' 1 1656).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        decide ((∑ j ∈ Finset.range k,
            stageSet (m / Nat.gcd 9 m) (j + 1) (Nat.gcd 9 m)
              (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) :
            Finset (ZMod (m / Nat.gcd 9 m))).card =
          m / Nat.gcd 9 m))) = true := by
  native_decide

/-- Extraction du certificat : couverture en k <= m/27+1 etages
    pour M <= 184 hors coin. -/
theorem stage_cover_small' (m : ℕ) (hm : Nat.Coprime m 10)
    (hM : m / Nat.gcd 9 m ≤ 184)
    (hbad : ¬(m = 11 ∨ m = 19 ∨ m = 23)) :
    ∃ k ≤ m / 27 + 1,
      (∑ j ∈ Finset.range k,
        stageSet (m / Nat.gcd 9 m) (j + 1) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25)).card =
        m / Nat.gcd 9 m := by
  have hgpos : 0 < Nat.gcd 9 m :=
    Nat.gcd_pos_of_pos_left m (by norm_num)
  have hgm : Nat.gcd 9 m ∣ m := Nat.gcd_dvd_right 9 m
  have hgl9 : Nat.gcd 9 m ≤ 9 :=
    Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 9 m)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; norm_num at hm
    · exact h
  have hgl : Nat.gcd 9 m ≤ m := Nat.le_of_dvd hmpos hgm
  have hMpos : 0 < m / Nat.gcd 9 m := Nat.div_pos hgl hgpos
  haveI : NeZero (m / Nat.gcd 9 m) := ⟨Nat.ne_of_gt hMpos⟩
  have hm1656 : m ≤ 1656 := by
    calc m = m / Nat.gcd 9 m * Nat.gcd 9 m :=
          (Nat.div_mul_cancel hgm).symm
      _ ≤ 184 * 9 := Nat.mul_le_mul hM hgl9
      _ = 1656 := by norm_num
  have hmem : m ∈ List.range' 1 1656 :=
    List.mem_range'.mpr ⟨m - 1, by omega, by omega⟩
  have hall := List.all_eq_true.mp stage_cover_small_aux' m hmem
  have hgcop : Nat.gcd m 10 = 1 := hm
  have hcopb : (Nat.gcd m 10 == 1) = true :=
    beq_iff_eq.mpr hgcop
  have hd11 : decide (m = 11) = false :=
    decide_eq_false_iff_not.mpr (fun h => hbad (Or.inl h))
  have hd19 : decide (m = 19) = false :=
    decide_eq_false_iff_not.mpr (fun h => hbad (Or.inr (Or.inl h)))
  have hd23 : decide (m = 23) = false :=
    decide_eq_false_iff_not.mpr (fun h => hbad (Or.inr (Or.inr h)))
  have hdM : decide (m / Nat.gcd 9 m ≤ 184) = true :=
    decide_eq_true_iff.mpr hM
  simp only [hcopb, Bool.not_true, hd11, hd19, hd23, hdM,
    Bool.false_or, Bool.or_self, Bool.or_false] at hall
  obtain ⟨k, hkmem, hk⟩ := List.any_eq_true.mp hall
  have hkl := List.mem_range.mp hkmem
  exact ⟨k, by omega, of_decide_eq_true hk⟩

/-- Certificat de la table witCorner : pour m in {11,19,23},
    L in {7,8,9}, r0 <= 4 et tout residu tv, une entree
    (m, L, tv, code) donne u_e = code/10^e%10 <= 8 de somme
    4L+r0 et de fibre congru a tv. -/
theorem witCorner_all :
    (([11, 19, 23] : List ℕ).all fun m =>
      (List.range' 7 3).all fun L =>
        (List.range 5).all fun r0 =>
          (List.range m).all fun tv =>
            witCorner.any fun e =>
              (e.1 == m) && (e.2.1 == L) && (e.2.2.1 == tv) &&
              (List.range L).all (fun i =>
                decide (e.2.2.2 / 10 ^ i % 10 ≤ 8)) &&
              (((List.range L).map fun i =>
                e.2.2.2 / 10 ^ i % 10).sum == 4 * L + r0) &&
              (fibre (fun i => e.2.2.2 / 10 ^ i % 10) L % m == tv)
            ) = true := by
  native_decide

/-- Extraction d'un temoin de la table pour le coin. -/
theorem corner_witness (m : ℕ) [NeZero m] (t : ZMod m)
    (L r0 : ℕ) (hL7 : 7 ≤ L) (hL9 : L ≤ 9) (hr0 : r0 ≤ 4)
    (hbad : m = 11 ∨ m = 19 ∨ m = 23) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 ∧
      ((fibre u L : ZMod m) = t) := by
  have hall := List.all_eq_true.mp witCorner_all
  have hm' : m ∈ ([11, 19, 23] : List ℕ) := by
    rcases hbad with rfl | rfl | rfl <;> decide
  have h1 := hall m hm'
  have hL' : L ∈ List.range' 7 3 := by
    apply List.mem_range'.mpr
    exact ⟨L - 7, by omega, by omega⟩
  have h2 := List.all_eq_true.mp h1 L hL'
  have hr0' : r0 ∈ List.range 5 :=
    List.mem_range.mpr (by omega)
  have h3 := List.all_eq_true.mp h2 r0 hr0'
  have htv : t.val ∈ List.range m :=
    List.mem_range.mpr (ZMod.val_lt t)
  have h4 := List.all_eq_true.mp h3 t.val htv
  obtain ⟨e, _he, hbool⟩ := List.any_eq_true.mp h4
  obtain ⟨hbool, hfib⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨hbool, hQ⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨hbool, hall8⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨hbool, hptv⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨_hpm, _hpL⟩ := (Bool.and_eq_true _ _).mp hbool
  refine ⟨fun i => e.2.2.2 / 10 ^ i % 10, fun i hi => ?_, ?_, ?_⟩
  · exact of_decide_eq_true (List.all_eq_true.mp hall8 i
      (List.mem_range.mpr hi))
  · exact beq_iff_eq.mp hQ
  · have hf := beq_iff_eq.mp hfib
    have hceq : ((fibre (fun i => e.2.2.2 / 10 ^ i % 10) L : ℕ) :
        ZMod m) = (t.val : ZMod m) := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      rw [Nat.mod_eq_of_lt (ZMod.val_lt t)]
      exact hf
    rw [hceq, ZMod.natCast_rightInverse]

/-- La fibre de la base ubase vaut 5L+r0 modulo g | 9 :
    chaque (1+u_e).10^e vaut (1+u_e) mod g car 10 ≡ 1 (mod g). -/
theorem fibre_ubase_mod (s r0 L g : ℕ) (hr0 : r0 ≤ 4)
    (hL : 3 * s + 4 ≤ L) (hg : g ∣ 9) [NeZero g] :
    ((fibre (ubase s r0) L : ℕ) : ZMod g) =
      ((5 * L + r0 : ℕ) : ZMod g) := by
  have h9 : (9 : ZMod g) = 0 := by
    simpa using (CharP.cast_eq_zero_iff (ZMod g) g 9).mpr hg
  have h10 : (10 : ZMod g) = 1 := by
    have e : (10 : ZMod g) = 9 + 1 := by norm_num
    rw [e, h9, zero_add]
  have hsum : ((List.range L).map (ubase s r0)).sum =
      4 * L + r0 := ubase_sum s r0 L hr0 hL
  have hsumm : ∀ e ∈ Finset.range L,
      (((1 + ubase s r0 e) * 10 ^ e : ℕ) : ZMod g) =
        1 + (ubase s r0 e : ZMod g) := by
    intro e _
    push_cast
    rw [h10, one_pow, mul_one]
  have hFE : ((List.range L).map (ubase s r0)).sum =
      ∑ e ∈ Finset.range L, ubase s r0 e := by
    clear hL hsum hsumm
    induction L with
    | zero => simp
    | succ n ih =>
      rw [List.sum_range_succ, ih, Finset.sum_range_succ]
  rw [fibre_val, Nat.cast_sum, Finset.sum_congr rfl hsumm]
  -- Σ (1 + u_e) = L + Σ u_e = 5L + r0 dans ZMod g
  rw [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one,
    ← Nat.cast_sum, ← hFE, hsum, ← Nat.cast_add]
  congr 1
  ring

theorem residue_reach (m : ℕ) (hm : Nat.Coprime m 10)
    (t : ZMod m) (L r0 : ℕ)
    (hL : 3 * (m / 27 + 1) + 4 ≤ L) (hr0 : r0 ≤ 4)
    (hcos : ∃ c : ℤ, t = ((5 * L + r0 : ℕ) : ZMod m) +
        ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 ∧
      ((fibre u L : ZMod m) = t) := by
  obtain ⟨c, hcos⟩ := hcos
  set g := Nat.gcd 9 m with hgdef
  set M := m / g with hMdef
  have hg9 : g = 1 ∨ g = 3 ∨ g = 9 := gcd9mem m
  have hg9d : g ∣ 9 := Nat.gcd_dvd_left 9 m
  have hgm : g ∣ m := Nat.gcd_dvd_right 9 m
  have hpos : 0 < g := Nat.gcd_pos_of_pos_left m (by norm_num)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; norm_num at hm
    · exact h
  have hMg : m = M * g := (Nat.div_mul_cancel hgm).symm
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h] at hMg; omega
    · exact h
  haveI : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  haveI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  haveI : NeZero g := ⟨Nat.ne_of_gt hpos⟩
  have hMd : M ∣ m := ⟨g, hMg⟩
  have hcopM : Nat.Coprime M 10 :=
    Nat.Coprime.coprime_dvd_left hMd hm
  -- g ∈ {1,3} → 3 ∤ M
  have h3M : g = 1 ∨ g = 3 → ¬ (3 ∣ M) := by
    intro hgc h3M'
    rcases hgc with hg1 | hg3'
    · have h3m : 3 ∣ m := h3M'.trans hMd
      have h3g : 3 ∣ g := Nat.dvd_gcd (by norm_num) h3m
      rw [hg1] at h3g; norm_num at h3g
    · obtain ⟨k', hk'⟩ := h3M'
      have h9m : 9 ∣ m := ⟨k', by rw [hMg, hg3', hk']; ring⟩
      have h9g : 9 ∣ g := Nat.dvd_gcd (dvd_refl 9) h9m
      rw [hg3'] at h9g; norm_num at h9g
  -- jeu d'unites selon g
  set xs := if g = 1 then Xsmooth235 else Xsmooth25 with hxsdef
  have hxsu : ∀ x ∈ xs, IsUnit (x : ZMod M) := by
    intro x hx
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef] at hx
      have h3c : Nat.Coprime M 3 := Nat.coprime_comm.mp
        (Nat.prime_three.coprime_iff_not_dvd.mpr (h3M (Or.inl h)))
      exact xunit235 M (hcopM.mul_right h3c) x hx
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      exact xunit25 M hcopM x hx
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      exact xunit25 M hcopM x hx
  have hnd : xs.Nodup := by
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef]; native_decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; native_decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; native_decide
  have hxb : ∀ x ∈ xs, |x| ≤ 92 := by
    intro x hx
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
  have hx0 : ∀ x ∈ xs, x ≠ 0 := by
    intro x hx
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
  have hsq : M ≤ (m / 27 + 1) * xs.length + 1 := by
    rcases hg9 with h | h | h
    · have hlen : xs.length = 28 := by
        rw [if_pos h] at hxsdef; rw [hxsdef]; native_decide
      rw [hlen, hMdef, h, Nat.div_one]; omega
    · have hlen : xs.length = 16 := by
        rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; native_decide
      rw [hlen, hMdef, h]; omega
    · have hlen : xs.length = 16 := by
        rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; native_decide
      rw [hlen, hMdef, h]; omega
  have hunit : IsUnit ((9 / g : ℕ) : ZMod M) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (scalar_unit m)
  have h10u : IsUnit ((10 : ℕ) : ZMod M) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (Nat.coprime_comm.mp hcopM)
  have htail : ∀ s : ℕ, 3 * s + 4 ≤ L →
      ∑ j ∈ Finset.range s, stageSet M (j + 1) g xs = Finset.univ →
      ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
        ((List.range L).map u).sum = 4 * L + r0 ∧
        ((fibre u L : ZMod m) = t) := by
    intro s hs4' hkcov
    -- fibre ubase ≡ 5L+r0 (mod g)
    have hfibg : ((fibre (ubase s r0) L : ℕ) : ZMod g) =
        ((5 * L + r0 : ℕ) : ZMod g) :=
      fibre_ubase_mod s r0 L g hr0 hs4' hg9d
    -- g | fibre ubase - (5L+r0) en entiers
    have hgdvd : (g : ℤ) ∣
        (fibre (ubase s r0) L : ℤ) - (5 * L + r0 : ℤ) := by
      have hZ : ((fibre (ubase s r0) L : ℤ) : ZMod g) =
          ((5 * L + r0 : ℤ) : ZMod g) := by
        exact_mod_cast hfibg
      rw [ZMod.intCast_eq_intCast_iff] at hZ
      exact Int.modEq_iff_dvd.mp hZ.symm
    set B' := ((fibre (ubase s r0) L : ℤ) - (5 * L + r0 : ℤ)) / g
      with hB'def
    have hgB : g * B' =
        (fibre (ubase s r0) L : ℤ) - (5 * L + r0 : ℤ) := by
      have h := Int.ediv_mul_cancel hgdvd
      rw [← hB'def] at h; rw [mul_comm] at h; exact h
    -- cible : c - B' dans ZMod M
    set ct := ((c - B' : ℤ) : ZMod M) with hctdef
    have hctu : ct ∈
        ∑ j ∈ Finset.range s, stageSet M (j+1) g xs := by
      rw [hkcov]; exact Finset.mem_univ _
    obtain ⟨f, hf, hfsum⟩ := (mem_sum_range
      (fun j => stageSet M (j+1) g xs) ct s).mp hctu
    -- valeur de grille x_j par etage
    have hxj : ∀ j : ℕ, ∃ x : ℤ, (x = 0 ∨ x ∈ xs) ∧
        (j < s → f j = ((9/g : ℕ) * 10^(3*(j+1)) : ZMod M) *
          (x : ZMod M)) := by
      intro j
      by_cases hj : j < s
      · have hmem := hf j hj
        rw [stageSet, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_image] at hmem
        rcases hmem with h0 | ⟨x, hxs, hfx⟩
        · exact ⟨0, Or.inl rfl, fun _ => by rw [h0]; simp⟩
        · exact ⟨x, Or.inr (List.mem_toFinset.mp hxs), fun _ => hfx.symm⟩
      · exact ⟨0, Or.inl rfl, fun h => absurd h hj⟩
    choose xj hxj using hxj
    have hxg : ∀ j < s, (xj j = 0) ∨ ∃ d1 d2 : ℤ,
        -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧ d2 ≤ 4 ∧
        -4 ≤ d1+d2 ∧ d1+d2 ≤ 4 ∧ xj j = d1 + 11 * d2 := by
      intro j hj
      rcases (hxj j).1 with h0 | hxs
      · exact Or.inl h0
      · right
        have hxg' : xj j ∈ Xgrid := by
          rcases hg9 with h | h | h
          · rw [if_pos h] at hxsdef; rw [hxsdef] at hxs
            exact Xsmooth235_sub _ hxs
          · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hxs
            exact Xsmooth25_sub _ hxs
          · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hxs
            exact Xsmooth25_sub _ hxs
        obtain ⟨d1, d2, ha, hb, hc2, hd2, he, hf2, heq, -⟩ :=
          (Xgrid_mem_iff _).mp hxg'
        exact ⟨d1, d2, ha, hb, hc2, hd2, he, hf2, heq⟩
    obtain ⟨u, hu8, hsum, hfib⟩ :=
      build_u s r0 L hs4' hr0 xj hxg
    -- S = Σ (9/g).10^{3i}.x_j ; (S : ZMod M) = ct
    set S := ∑ j ∈ Finset.range s,
      ((9/g : ℕ) : ℤ) * 10^(3*(j+1)) * xj j with hSdef
    have hSM : (S : ZMod M) = ct := by
      rw [hfsum, hSdef]
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow,
        Int.cast_natCast, Int.cast_ofNat, Nat.cast_pow,
        Nat.cast_ofNat]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [(hxj j).2 hj] <;> ring_nf
    -- g*S ≡ g*(c-B') (mod m)
    have hgm2 : (g : ℤ) * S ≡ (g : ℤ) * (c - B')
        [ZMOD (m : ℤ)] := by
      rw [Int.modEq_iff_dvd, ← mul_sub]
      have hmod : S ≡ (c - B') [ZMOD (M : ℤ)] :=
        (ZMod.intCast_eq_intCast_iff ..).mp hSM
      have hdvd := mul_dvd_mul_left (g : ℤ)
        (Int.modEq_iff_dvd.mp hmod)
      have hgi : (g : ℤ) * (M : ℤ) = (m : ℤ) := by
        rw [mul_comm, ← Int.natCast_mul, ← hMg]
      rwa [hgi] at hdvd
    -- fibre u ≡ (5L+r0) + g*c (mod m)
    have hfinal : (fibre u L : ℤ) ≡
        ((5 * L + r0 : ℕ) : ℤ) + (g : ℤ) * c
        [ZMOD (m : ℤ)] := by
      have h9S : (∑ j ∈ Finset.range s,
          9 * 10 ^ (3*(j+1)) * xj j : ℤ) = g * S := by
        rw [hSdef, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have h99 : (9 : ℤ) =
            (g : ℤ) * ((9/g : ℕ) : ℤ) := by
          have h99' := Nat.div_mul_cancel hg9d
          rw [mul_comm] at h99'
          exact_mod_cast h99'.symm
        rw [h99]; ring
      rw [hfib, h9S]
      have hub : (fibre (ubase s r0) L : ℤ) =
          (5 * L + r0 : ℤ) + (g : ℤ) * B' := by
        have h := hgB; omega
      rw [hub]
      have h2 : (g:ℤ)*B' + (g:ℤ)*S ≡ (g:ℤ)*c
          [ZMOD (m:ℤ)] := by
        have e := hgm2.add_right ((g:ℤ)*B')
        have e2 : (g:ℤ)*B' + (g:ℤ)*S =
            (g:ℤ)*S + (g:ℤ)*B' := add_comm _ _
        have e3 : (g:ℤ)*c =
            (g:ℤ)*(c-B') + (g:ℤ)*B' := by ring
        rwa [e2, e3]
      have e := h2.add_left ((5 * L + r0 : ℕ) : ℤ)
      rwa [show (5 * L + r0 : ℤ) + (g:ℤ)*B' + (g:ℤ)*S =
          (5*L+r0:ℤ) + ((g:ℤ)*B' + (g:ℤ)*S) from by ring]
    refine ⟨u, hu8, hsum, ?_⟩
    have hcast : ((fibre u L : ℤ) : ZMod m) =
        ((((5 * L + r0 : ℕ) : ℤ) + (g : ℤ) * c : ℤ) :
          ZMod m) :=
      (ZMod.intCast_eq_intCast_iff ..).mpr hfinal
    push_cast at hcast
    rw [hcast, hcos]
    push_cast <;> ring
  -- aiguillage : coin {11,19,23} / M > 184 / machine M ≤ 184
  by_cases hbad : m = 11 ∨ m = 19 ∨ m = 23
  · by_cases hL10 : 10 ≤ L
    · rcases hbad with rfl | rfl | rfl <;>
        refine htail 2 (by omega) ?_
      all_goals
        have hg1 : g = 1 := by rw [hgdef]; native_decide
        rw [hg1, Nat.div_one] at hMdef
        have hxs1 : xs = Xsmooth235 := by
          rw [if_pos hg1] at hxsdef; exact hxsdef
        refine stage_cover_2 M g xs ?_ hg1 hxs1
        rw [hMdef]; decide
    · push_neg at hL10
      exact corner_witness m t L r0
        (by rcases hbad with rfl | rfl | rfl <;> omega)
        (by omega) hr0 hbad
  · by_cases hM184 : 184 < M
    · exact htail (m / 27 + 1) hL
        (stage_cover M g xs.length (m / 27 + 1) xs hM184 hunit
          h10u hxsu hnd hxb hx0 (le_refl _) hsq)
    · push_neg at hM184
      have hM' : m / Nat.gcd 9 m ≤ 184 := by
        rw [← hgdef, ← hMdef]; exact hM184
      obtain ⟨k, hks, hkc⟩ := stage_cover_small' m hm hM' hbad
      refine htail k (by omega) ?_
      apply Finset.eq_univ_of_card
      rw [ZMod.card]
      exact hkc

theorem coverage (m : ℕ) (hm : Nat.Coprime m 10) (t : ZMod m) :
    ∃ C : ℕ, C ≤ m / 9 + 7 ∧ ∀ L : ℕ, C ≤ L → ∀ r0 : ℕ, r0 ≤ 4 →
      (∃ c : ℤ, t = ((5 * L + r0 : ℕ) : ZMod m) +
          ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) →
      ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
        ((List.range L).map u).sum = 4 * L + r0 ∧
        ((fibre u L : ZMod m) = t) := by
  refine ⟨3 * (m / 27 + 1) + 4, by omega, ?_⟩
  intro L hL r0 hr0 hcos
  exact residue_reach m hm t L r0 hL hr0 hcos

/-- Existence conditionnelle : sous l hypothese de
    couverture, n = R.m avec R | 10^d se traite par
    bloc bas + fibre + CRT. La somme des chiffres exige
    sigma H = n - sigma B, i.e. somme u_e = K. -/
theorem existence_step (n R m B d : ℕ) (hn : n = R * m)
    (hRc : Nat.Coprime R m) (hR10 : R ∣ 10 ^ d)
    (hRB : R ∣ B) (hBl : (Nat.digits 10 B).length = d) (hB0 : B ≠ 0)
    (hBn : allNonzero B)
    (L : ℕ) (u : ℕ → ℕ) (hu : ∀ e < L, u e ≤ 8)
    (hres : (fibre u L : ZMod m) * (10 : ZMod m) ^ d + (B : ZMod m) = 0)
    (hsum : sigma10 B + sigma10 (fibre u L) = n)
    (hlen2 : 2 ≤ d + L)
    (hfibre_nz : allNonzero (fibre u L)) :
    ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        (Nat.digits 10 N).length ≥ 2 := by
  have hdiv : n ∣ B + 10 ^ d * fibre u L := by
    rw [hn]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd hRc
    · exact dvd_concat_base R B _ d hR10 hRB
    · have hz : ((B + 10 ^ d * fibre u L : ℕ) : ZMod m) = 0 := by
        push_cast
        linear_combination hres
      exact (CharP.cast_eq_zero_iff (ZMod m) m _).mp hz
  refine ⟨B + 10 ^ d * fibre u L, hdiv, ?_, ?_, ?_⟩
  · rw [← hBl, nonzero_concat B _ hB0, hBn, hfibre_nz]; rfl
  · rw [← hBl, sigma_concat B _ hB0]; exact hsum
  · rw [← hBl, digits_concat B _ hB0, List.length_append]
    have hfL : (Nat.digits 10 (fibre u L)).length = L := by
      rw [fibre_digits u L hu, List.length_map, List.length_range]
    rw [hfL, hBl]; exact hlen2

/-- Raccord : pour n = R*m (R | 10^d, gcd(R,m)=1, m cop 10),
    bloc bas B + fibre de couverture a somme fixee
    L + K = n - sigma B, K <= 4L. -/
theorem existence_Rm (n R m : ℕ) (hn : n = R * m)
    (hRc : Nat.Coprime R m) (hm : Nat.Coprime m 10)
    (d : ℕ) (hR10 : R ∣ 10 ^ d)
    (B : ℕ) (hRB : R ∣ B) (hBl : (Nat.digits 10 B).length = d)
    (hB0 : B ≠ 0) (hBn : allNonzero B)
    (hsig : sigma10 B < n)
    (L K : ℕ) (hLK : L + K = n - sigma10 B)
    (hm1 : 1 < m)
    (hcov : ∀ t : ZMod m, (∃ c : ℤ, t = ((L + K : ℕ) : ZMod m) +
        ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) →
      ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = K ∧ (fibre u L : ZMod m) = t)
    (hLge : 2 ≤ d + L) :
    ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        (Nat.digits 10 N).length ≥ 2 := by
  -- cible t = -B . (10^d)^{-1} dans ZMod m
  have hunit : IsUnit ((10 : ZMod m) ^ d) := by
    apply IsUnit.pow
    exact (ZMod.isUnit_iff_coprime 10 m).mpr (Nat.coprime_comm.mp hm)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  set t : ZMod m := -(B : ZMod m) * v with ht
  have htgt : t * (10 : ZMod m) ^ d + (B : ZMod m) = 0 := by
    rw [ht, mul_assoc]
    have hv' : (v : ZMod m) * (10 : ZMod m) ^ d = 1 := by
      rw [mul_comm]; exact hv
    rw [hv']; simp
  -- condition de coset : t = ↑(L+K) + g.c (mod m)
  have hcosB : ∃ c : ℤ, t = ((L + K : ℕ) : ZMod m) +
      ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m) := by
    haveI : NeZero m := ⟨by omega⟩
    have hg9 : Nat.gcd 9 m ∣ 9 := Nat.gcd_dvd_left 9 m
    have hgm : Nat.gcd 9 m ∣ m := Nat.gcd_dvd_right 9 m
    set g := Nat.gcd 9 m
    have hmodg : B ≡ sigma10 B [MOD g] := by
      have h9 : (9 : ℤ) ∣ (sigma10 B : ℤ) - B :=
        Nat.ModEq.dvd (Nat.modEq_nine_digits_sum B)
      have hg9z : (g : ℤ) ∣ 9 := Int.natCast_dvd_natCast.mpr hg9
      exact Nat.modEq_of_dvd (dvd_trans hg9z h9)
    have hcast : ZMod.castHom hgm (ZMod g) t =
        ((L + K : ℕ) : ZMod g) := by
      have hcv : ZMod.castHom hgm (ZMod g) v = 1 := by
        have hmul := congrArg (ZMod.castHom hgm (ZMod g)) hv
        rw [map_mul, map_one] at hmul
        have h10d : ZMod.castHom hgm (ZMod g)
            ((10 : ZMod m) ^ d) = 1 := by
          rw [map_pow]
          have h10g : ((10 : ℕ) : ZMod g) = 1 := by
            rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
            exact (Nat.modEq_zero_iff_dvd.mpr hg9).add
              (Nat.ModEq.refl 1)
          rw [show (10 : ZMod m) = ((10 : ℕ) : ZMod m) from rfl,
              map_natCast, h10g, one_pow]
        rw [h10d, one_mul] at hmul
        exact hmul
      have hBg : ((B : ℕ) : ZMod g) = ((sigma10 B : ℕ) : ZMod g) := by
        rw [ZMod.natCast_eq_natCast_iff]; exact hmodg
      have hLKg : ((L + K : ℕ) : ZMod g) =
          -((sigma10 B : ℕ) : ZMod g) := by
        have hsum : L + K + sigma10 B = n := by omega
        have hgn : g ∣ n := dvd_trans hgm ⟨R, by rw [mul_comm]; exact hn⟩
        apply eq_neg_of_add_eq_zero_left
        rw [← Nat.cast_add, hsum]
        exact (CharP.cast_eq_zero_iff (ZMod g) g n).mpr hgn
      rw [ht, map_mul, map_neg, map_natCast, hcv, mul_one, hBg, hLKg]
    -- (t - ↑V).val divisible par g -> le coset c
    set z := t - ((L + K : ℕ) : ZMod m)
    have hz : ZMod.castHom hgm (ZMod g) z = 0 := by
      rw [map_sub, hcast, map_natCast, sub_self]
    have hcv2 : ZMod.castHom hgm (ZMod g) z =
        ((z.val : ℕ) : ZMod g) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val z]
      rw [map_natCast]
    rw [hcv2] at hz
    have hdv : g ∣ z.val :=
      (CharP.cast_eq_zero_iff (ZMod g) g z.val).mp hz
    refine ⟨((z.val / g : ℕ) : ℤ), ?_⟩
    have ht2 : t = ((L + K : ℕ) : ZMod m) + z :=
      (add_sub_cancel _ _).symm
    rw [ht2]; congr 1
    rw [Int.cast_natCast, ← Nat.cast_mul, Nat.mul_div_cancel' hdv,
        ZMod.natCast_zmod_val]
  obtain ⟨u, hu8, huK, hut⟩ := hcov t hcosB
  refine existence_step n R m B d hn hRc hR10 hRB hBl hB0 hBn
    L u hu8 ?_ ?_ hLge ?_
  · rw [hut]; exact htgt
  · have hfs := fibre_sigma u L hu8
    rw [huK] at hfs
    have : sigma10 B + (L + K) = n := by omega
    rw [hfs]; omega
  · have hfd := fibre_digits u L hu8
    rw [allNonzero, List.all_eq_true]
    intro x hx
    rw [hfd] at hx
    rw [List.mem_map] at hx
    obtain ⟨e, -, rfl⟩ := hx
    simp

/-- Decomposition n = R.m : on retire de n toute la 2-partie puis
    toute la 5-partie ; 10 non-divisant n force l'une des deux
    a etre 1, donc R = 2^d ou R = 5^d, et gcd(m,10) = 1. -/
theorem decomp_Rm (n : ℕ) (hn0 : n ≠ 0) (h10 : ¬ 10 ∣ n) :
    ∃ R m d : ℕ, n = R * m ∧ Nat.Coprime m 10 ∧ R ∣ 10 ^ d ∧
      Nat.Coprime R m ∧ (R = 2 ^ d ∨ R = 5 ^ d) := by
  set q1 := Nat.divMaxPow n 2 with hq1
  set a := padicValNat 2 n with ha
  have hq1n : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn0
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, Nat.zero_mul] at hq1n; exact hn0 hq1n.symm
  set m := Nat.divMaxPow q1 5 with hm
  set b := padicValNat 5 q1 with hb
  have hmq : m * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have h5m : ¬ 5 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have hmq1 : m ∣ q1 := ⟨5 ^ b, hmq.symm⟩
  have h2m : ¬ 2 ∣ m := fun h => h2q1 (h.trans hmq1)
  -- a et b ne sont pas tous deux >= 1 (sinon 10 | n)
  have hab : a = 0 ∨ b = 0 := by
    rcases Nat.eq_zero_or_pos a with h | ha1
    · exact Or.inl h
    rcases Nat.eq_zero_or_pos b with h | hb1
    · exact Or.inr h
    exfalso; apply h10
    have h2an : 2 ^ a ∣ n := ⟨q1, by rw [← hq1n]; ring⟩
    have h2n : 2 ∣ n := dvd_trans (dvd_pow_self 2 ha1.ne') h2an
    have h5bn : 5 ^ b ∣ n := ⟨m * 2 ^ a, by rw [← hq1n, ← hmq]; ring⟩
    have h5n : 5 ∣ n := dvd_trans (dvd_pow_self 5 hb1.ne') h5bn
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (by norm_num : Nat.Coprime 2 5) h2n h5n
    exact this
  have h2 : Nat.Coprime m 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr h2m).symm
  have h5 : Nat.Coprime m 5 :=
    ((Nat.prime_five.coprime_iff_not_dvd).mpr h5m).symm
  refine ⟨2 ^ a * 5 ^ b, m, a + b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hq1n, ← hmq]; ring
  · have hc : Nat.Coprime m (2 * 5) := Nat.Coprime.mul_right h2 h5
    rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc
  · have h10a : 2 ^ a ∣ 10 ^ a := pow_dvd_pow_of_dvd (by norm_num) a
    have h10b : 5 ^ b ∣ 10 ^ b := pow_dvd_pow_of_dvd (by norm_num) b
    have h2a5b : Nat.Coprime (2 ^ a) (5 ^ b) :=
      Nat.Coprime.pow_left a (Nat.Coprime.pow_right b
        (by norm_num : Nat.Coprime 2 5))
    have hd := Nat.Coprime.mul_dvd_of_dvd_of_dvd h2a5b
      (h10a.trans (pow_dvd_pow 10 (Nat.le_add_right a b)))
      (h10b.trans (pow_dvd_pow 10 (Nat.le_add_left b a)))
    exact hd
  · exact (Nat.Coprime.mul_right
      (Nat.Coprime.pow_right a h2) (Nat.Coprime.pow_right b h5)).symm
  · rcases hab with h0 | h0
    · refine Or.inr ?_; simp [h0]
    · refine Or.inl ?_; simp [h0]

/-- Table des temoins du LEMME-MACHINE A : pour chaque n <= 200
    hors {1,2,5,11} u 10N, un N a chiffres non nuls avec n | N,
    sigma10 N = n et >= 2 chiffres. Generee par le BFS de
    A077754-ANNEXE.py (176 entrees, longueur max 23). -/
def witTab : List (ℕ × ℕ) := [
  (3, 21), (4, 112), (6, 42), (7, 511), (8, 512), (9, 81),
  (12, 84), (13, 481), (14, 392), (15, 915), (16, 592),
  (17, 782), (18, 972), (19, 874), (21, 966), (22, 9922),
  (23, 4991), (24, 888), (25, 9925), (26, 7982), (27, 999),
  (28, 9856), (29, 9686), (31, 9796), (32, 97952), (33, 99924),
  (34, 98872), (35, 98945), (36, 99972), (37, 99937),
  (38, 89984), (39, 89895), (41, 988961), (42, 88998),
  (43, 99889), (44, 999944), (45, 999945), (46, 979984),
  (47, 969986), (48, 999984), (49, 999796), (51, 899997),
  (52, 9998872), (53, 9999881), (54, 9999882), (55, 99979165),
  (56, 8999984), (57, 9999795), (58, 9998968), (59, 8999978),
  (61, 9998998), (62, 89999882), (63, 99899982), (64, 99889984),
  (65, 99999965), (66, 99999966), (67, 99999778), (68, 99899888),
  (69, 98999889), (71, 998999891), (72, 999999792),
  (73, 999988894), (74, 9999998732), (75, 999999975),
  (76, 998899996), (77, 999899978), (78, 998999898),
  (79, 999899998), (81, 999999999), (82, 9999998974),
  (83, 9999799994), (84, 9998999976), (85, 9999998995),
  (86, 9999799898), (87, 9899899998), (88, 99999988792),
  (89, 9989999999), (91, 99999977896), (92, 99998999984),
  (93, 99999999795), (94, 99989999788), (95, 999899999915),
  (96, 999999989952), (97, 99999999898), (98, 899999998982),
  (99, 9999999997911), (101, 9999999999182), (102, 998999999994),
  (103, 998999989987), (104, 9999989899952), (105, 9999999899925),
  (106, 8999999999962), (107, 9989898999992), (108, 9999999989892),
  (109, 9999998898985), (111, 9999999999768), (112, 9998999999968),
  (113, 8999999999987), (114, 9999999989898), (115, 99989999999935),
  (116, 99999998998892), (117, 99999999899982), (118, 99999998999992),
  (119, 98999998999895), (121, 989999989999933), (122, 98999999989988),
  (123, 99999999998979), (124, 899999999999872),
  (125, 999999999996875), (126, 999999999999882),
  (127, 999999999998794), (128, 999999989998976),
  (129, 999999999999984), (131, 997999999999997),
  (132, 9999999999998844), (133, 999999999989998),
  (134, 9999899999899892), (135, 9999999999999855),
  (136, 9999999989998984), (137, 9999999997998977),
  (138, 8999999999999886), (139, 9999899999999995),
  (141, 9999989999999997), (142, 89999999998999972),
  (143, 99999999999997955), (144, 99999999999999792),
  (145, 99999989999999875), (146, 99999999888999986),
  (147, 98999999999999994), (148, 999999999999988492),
  (149, 99999999998999996), (151, 998999999899998991),
  (152, 899999999999999792), (153, 999999999999899991),
  (154, 999999999999889966), (155, 999999999899999975),
  (156, 999999999999989976), (157, 999899999998999996),
  (158, 999989999999998988), (159, 999999999999998898),
  (161, 9999999999999989882), (162, 9999999999899999982),
  (163, 9999998999999998993), (164, 9999999999999889796),
  (165, 99999999999999989175), (166, 9899999989999999996),
  (167, 9998999999999999996), (168, 99999999999989999952),
  (169, 9998999999999999989), (171, 99999999999989999991),
  (172, 99998999999999989984), (173, 99998999989999999994),
  (174, 99999999999999898986), (175, 999999999999999989725),
  (176, 99999999999999899888), (177, 99999999998999999997),
  (178, 999899999998999999972), (179, 999899899999999999892),
  (181, 999999999899999999785), (182, 999999999999999977888),
  (183, 999999999998989999995), (184, 999999999999999989896),
  (185, 9999999999999999996845), (186, 9999999999989999998962),
  (187, 999998999999999999989), (188, 9999999999999899997992),
  (189, 9999999999999999998883), (191, 9999999899999999998994),
  (192, 9999999999999999998976), (193, 9999999989999999999896),
  (194, 9999999999999999999878), (195, 99999999999999998989935),
  (196, 98999999999999999998972), (197, 99999998999999989999982),
  (198, 99999999999999999999792), (199, 99999999999999989999893)]

/-- Test des 4 proprietes du temoin : divisibilite, chiffres
    non nuls, somme n, au moins 2 chiffres. -/
def witOk (n N : ℕ) : Bool :=
  decide (n ∣ N) && allNonzero N && decide (sigma10 N = n) &&
    decide (2 ≤ (Nat.digits 10 N).length)

/-- Verification exhaustive de la table : pour tout n <= 200,
    soit witTab contient un temoin verifie, soit n est dans
    {1,2,5,11} u 10N. Calcul natif (machine). -/
theorem witSmall_all :
    ((List.range 201).all fun n =>
      match witTab.lookup n with
      | some N => witOk n N
      | none => n == 1 || n == 2 || n == 5 || n == 11 ||
          decide (10 ∣ n)) = true := by
  native_decide

/-- LEMME-MACHINE A (table exhaustive n <= 200 — BFS de
    l'annexe, temoins certifies par witSmall_all). -/
theorem existence_small (n : ℕ) (hle : n ≤ 200)
    (hmem : n ∉ ({1, 2, 5, 11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ)) :
    ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        2 ≤ (Nat.digits 10 N).length := by
  have hn : n ∈ List.range 201 :=
    List.mem_range.mpr (show n < 201 by omega)
  have hall := List.all_eq_true.mp witSmall_all n hn
  cases h : witTab.lookup n with
  | some N =>
    rw [h] at hall
    dsimp only at hall
    unfold witOk at hall
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hall
    obtain ⟨⟨⟨hdvd, hnonz⟩, hsum⟩, hlen⟩ := hall
    exact ⟨N, of_decide_eq_true hdvd, hnonz, of_decide_eq_true hsum,
      of_decide_eq_true hlen⟩
  | none =>
    exfalso; apply hmem
    rw [h] at hall; dsimp only at hall
    have hc : n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 11 ∨ 10 ∣ n := by
      rcases (Bool.or_eq_true _ _).mp hall with h15 | h10
      · rcases (Bool.or_eq_true _ _).mp h15 with h14 | h11
        · rcases (Bool.or_eq_true _ _).mp h14 with h13 | h5
          · rcases (Bool.or_eq_true _ _).mp h13 with h1 | h2
            · exact Or.inl (beq_iff_eq.mp h1)
            · exact Or.inr (Or.inl (beq_iff_eq.mp h2))
          · exact Or.inr (Or.inr (Or.inl (beq_iff_eq.mp h5)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (beq_iff_eq.mp h11))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (of_decide_eq_true h10))))
    rcases hc with rfl | rfl | rfl | rfl | h10n
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inr h10n

/-- log2 n <= n/16 + 4 pour n >= 64 (borne grossiere :
    n < 2^(n/16+5) car n < 16(n/16+1) <= 2^(n/16+5)). -/
theorem log2_le_div16 (n : ℕ) (hn : 64 ≤ n) :
    Nat.log 2 n ≤ n / 16 + 4 := by
  suffices h : Nat.log 2 n < n / 16 + 5 by omega
  apply Nat.log_lt_of_lt_pow (by omega : n ≠ 0)
  set j := n / 16 with hj
  have hmod := Nat.mod_add_div n 16
  have hltm := Nat.mod_lt n (by norm_num : 0 < 16)
  have h1 : n < 16 * (j + 1) := by omega
  have h3 : j + 1 ≤ 2 ^ (j + 1) := (j + 1).lt_two_pow_self.le
  calc n < 16 * (j + 1) := h1
    _ ≤ 16 * 2 ^ (j + 1) := Nat.mul_le_mul_left _ h3
    _ = 2 ^ (j + 5) := by
      have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
      rw [h16, ← pow_add]; congr 1; omega
    _ = 2 ^ (n / 16 + 5) := by rw [hj]

/-- BUDGET ANALYTIQUE + COUVERTURE (SS5-7 : echanges + Chowla +
    lemme-machine M<=600 + bornes en log) : pour m > 1 coprime
    a 10, n > 200, m <= n, si sigma <= 5.log2 n + 5 et
    L = (n-sigma)/5, alors C <= L (borne m/9+7 de coverage)
    et la somme cible n-sigma-L = 4L+r0 est realisee. -/
theorem analytic_budget (n : ℕ) (hn : 200 < n) (m : ℕ)
    (hm10 : Nat.Coprime m 10) (hm1 : 1 < m)
    (σB : ℕ) (hσb : σB ≤ 5 * Nat.log 2 n + 5) (hσn : σB < n)
    (hmn : m ≤ n)
    (L : ℕ) (hL : L = (n - σB) / 5) (t : ZMod m)
    (hcos : ∃ c : ℤ, t = ((n - σB : ℕ) : ZMod m) +
        ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = n - σB - L ∧
      (fibre u L : ZMod m) = t := by
  obtain ⟨C, hCb, hcov⟩ := coverage m hm10 t
  have hlog : Nat.log 2 n ≤ n / 16 + 4 := log2_le_div16 n (by omega)
  have hCL : C ≤ L := by
    have h2 : 5 * (n / 9 + 7) ≤ n - σB := by
      rcases lt_or_ge n 512 with hsm | hbig
      · have hlg : Nat.log 2 n ≤ 8 := by
          have hp : n < 2 ^ 9 := by omega
          have h := Nat.log_lt_of_lt_pow (show n ≠ 0 by omega) hp
          omega
        omega
      · omega
    rw [hL]; omega
  set r0 := (n - σB) % 5 with hr0
  have hr04 : r0 ≤ 4 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))
  obtain ⟨u, hu8, husum, hval⟩ := hcov L hCL r0 hr04 (by
    obtain ⟨c, hc⟩ := hcos
    refine ⟨c, ?_⟩
    have h5r : (5 * L + r0 : ℕ) = n - σB := by
      have := Nat.div_add_mod (n - σB) 5
      rw [hL, hr0]; omega
    rw [h5r]; exact hc)
  refine ⟨u, hu8, ?_, hval⟩
  have hdmod := Nat.div_add_mod (n - σB) 5
  rw [husum]; omega

/-- 5.d < 2^d pour d >= 5 (croissance exponentielle). -/
theorem five_mul_lt_two_pow (d : ℕ) (hd : 5 ≤ d) : 5 * d < 2 ^ d := by
  induction' hd with k hk ih
  · norm_num
  · have h2k : 5 ≤ 2 ^ k := by
      calc (5 : ℕ) ≤ 2 ^ 5 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    calc 5 * (k + 1) = 5 * k + 5 := by ring
      _ < 2 ^ k + 5 := Nat.add_lt_add_right ih 5
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left h2k _
      _ = 2 ^ (k + 1) := by ring

/-- d <= log2 n des que 2^d <= n (re-export pour lisibilite). -/
theorem le_log2_of_pow_le {d n : ℕ} (hn : n ≠ 0) (h : 2 ^ d ≤ n) :
    d ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le (by norm_num) h


/-- Somme d une constante sur List.range . -/
theorem sum_map_const (s l c : ℕ) :
    ((List.range' s l).map fun _ => c).sum = c * l := by
  induction l generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.range'_succ, List.map_cons, List.sum_cons, ih]; ring

/-- Fibre explicite : u_0 = 4 + r0, autres = 4 — somme 4L + r0,
    tous <= 8 des que r0 <= 4 et L >= 1. -/
theorem fibre_u_exists (L : ℕ) (hL : 1 ≤ L) (r0 : ℕ) (hr0 : r0 ≤ 4) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  refine ⟨fun e => if e = 0 then 4 + r0 else 4, ?_, ?_⟩
  · intro e _
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp; omega
    · simp [Nat.ne_of_gt he]
  · rw [List.range_eq_range', List.range'_succ, List.map_cons, List.sum_cons]
    have hmap : (List.range' 1 l).map (fun e => if e = 0 then 4 + r0 else 4)
        = (List.range' 1 l).map fun _ => (4 : ℕ) := by
      apply List.map_congr_left
      intro e he
      have hne : e ≠ 0 := by
        obtain ⟨i, -, rfl⟩ := List.mem_range'.mp he; omega
      simp [hne]
    rw [hmap, sum_map_const]
    simp; ring

/-- 5d + 10 <= 2^d pour d >= 7. -/
theorem five_mul_add_ten_le_two_pow (d : ℕ) (hd : 7 ≤ d) :
    5 * d + 10 ≤ 2 ^ d := by
  induction' hd with k hk ih
  · norm_num
  · have h2k : (5 : ℕ) ≤ 2 ^ k :=
      le_trans (by norm_num : (5:ℕ) ≤ 2 ^ 7)
        (Nat.pow_le_pow_right (by norm_num) hk)
    calc 5 * (k + 1) + 10 = (5 * k + 10) + 5 := by ring
      _ ≤ 2 ^ k + 5 := Nat.add_le_add_right ih 5
      _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left h2k _
      _ = 2 ^ (k + 1) := by ring

/-- Existence complete : n > 200 non exceptionnelle. -/
theorem existence (n : ℕ)
    (hmem : n ∉ ({1, 2, 5, 11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ)) :
    ∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        2 ≤ (Nat.digits 10 N).length := by
  obtain ⟨hne, h10⟩ : ¬ (n ∈ ({1,2,5,11} : Set ℕ)) ∧ ¬ 10 ∣ n := by
    simpa [Set.mem_union, Set.mem_setOf_eq] using hmem
  by_cases hsmall : n ≤ 200
  · exact existence_small n hsmall hmem
  push_neg at hsmall
  have hn0 : n ≠ 0 := by omega
  obtain ⟨R, m, d, hnm, hm10, hRd, hRm, hR⟩ := decomp_Rm n hn0 h10
  have hmpos : 0 < m := Nat.pos_of_ne_zero
    (fun h => by rw [h, Nat.mul_zero] at hnm; exact hn0 hnm)
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · -- d = 0 → R = 1 → n = m : fibre seule (B = 0)
    have hR1 : R = 1 := by rcases hR with h | h <;> simp [h]
    rw [hR1, one_mul] at hnm
    have hm1 : 1 < m := by omega
    set L := n / 5 with hL
    obtain ⟨u, hu8, huK, hut⟩ :=
      analytic_budget n hsmall m hm10 hm1 0 (by omega) (by omega)
        (by omega) L hL (0 : ZMod m) ⟨0, by
          have hnm2 : n = m := by omega
          have h0 : (↑n : ZMod m) = 0 :=
            (CharP.cast_eq_zero_iff (ZMod m) m n).mpr
              ⟨1, hnm2.trans (mul_one m).symm⟩
          rw [Int.cast_zero, mul_zero, add_zero]
          exact h0.symm⟩
    refine ⟨fibre u L, ?_, ?_, ?_, ?_⟩
    · rw [hnm]
      exact (CharP.cast_eq_zero_iff (ZMod m) m _).mp hut
    · rw [allNonzero, List.all_eq_true]
      intro x hx
      rw [fibre_digits u L hu8] at hx
      rw [List.mem_map] at hx
      obtain ⟨e, -, rfl⟩ := hx; simp
    · rw [fibre_sigma u L hu8, huK]
      have : L ≤ n := by omega
      omega
    · rw [fibre_digits u L hu8, List.length_map, List.length_range]
      omega
  · -- d >= 1 : bloc bas (predicat commun 1<=x<=5 aux deux cas)
    obtain ⟨B, hRB, hBl, hBd, hBσ, hBn⟩ :
        ∃ B : ℕ, R ∣ B ∧ (Nat.digits 10 B).length = d ∧
          (∀ x ∈ Nat.digits 10 B, 1 ≤ x ∧ x ≤ 5) ∧ sigma10 B ≤ 5 * d ∧
          allNonzero B := by
      rcases hR with hR2 | hR5
      · obtain ⟨B, hRB, hBl, hBd, hBσ⟩ := lowBlock2 d hd0
        have hBd5 : ∀ x ∈ Nat.digits 10 B, 1 ≤ x ∧ x ≤ 5 :=
          fun x hx => by rcases hBd x hx with rfl | rfl <;> norm_num
        refine ⟨B, by rwa [hR2], hBl, hBd5, hBσ.trans (by omega), ?_⟩
        rw [allNonzero, List.all_eq_true]
        intro x hx; have hx' : x ≠ 0 := by have := hBd5 x hx; omega
        simp [hx']
      · obtain ⟨B, hRB, hBl, hBd, hBσ⟩ := lowBlock5 d hd0
        refine ⟨B, by rwa [hR5], hBl, hBd, hBσ, ?_⟩
        rw [allNonzero, List.all_eq_true]
        intro x hx; have hx' : x ≠ 0 := by have := hBd x hx; omega
        simp [hx']
    have hB0 : B ≠ 0 := by
      rintro rfl; simp at hBl; omega
    have hRn : R ≤ n := by
      rw [hnm]; exact Nat.le_mul_of_pos_right R hmpos
    have h2dn : 2 ^ d ≤ n := by
      rcases hR with hR2 | hR5
      · calc 2 ^ d = R := hR2.symm
          _ ≤ n := hRn
      · calc 2 ^ d ≤ 5 ^ d := Nat.pow_le_pow_left (by norm_num) d
          _ = R := hR5.symm
          _ ≤ n := hRn
    have hσB10 : sigma10 B + 10 ≤ n := by
      rcases Nat.lt_or_ge d 7 with hd | hd
      · have : sigma10 B ≤ 30 := by omega
        omega
      · have h := five_mul_add_ten_le_two_pow d hd
        omega
    have hσBn : sigma10 B < n := by omega
    set L := (n - sigma10 B) / 5 with hL
    set r0 := (n - sigma10 B) % 5 with hr0
    have hr04 : r0 ≤ 4 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))
    have hL2 : 2 ≤ L := by omega
    have hLge : 2 ≤ d + L := by omega
    have hσb : sigma10 B ≤ 5 * Nat.log 2 n + 5 := by
      have hd' : d ≤ Nat.log 2 n := le_log2_of_pow_le hn0 h2dn
      omega
    have hmn : m ≤ n := by
      have hRpos : 0 < R := by
        rcases Nat.eq_zero_or_pos R with hR0 | hR0
        · rw [hR0, zero_mul] at hnm; omega
        · exact hR0
      calc m = 1 * m := (one_mul m).symm
        _ ≤ R * m := Nat.mul_le_mul_right m hRpos
        _ = n := hnm.symm
    by_cases hm1 : 1 < m
    · -- cas general : existence_Rm + budget analytique
      exact existence_Rm n R m hnm hRm hm10 d hRd B hRB hBl hB0 hBn
        hσBn L (n - sigma10 B - L) (by omega) hm1
        (fun t hcost => analytic_budget n hsmall m hm10 hm1
          (sigma10 B) hσb hσBn hmn L hL t (by
            have heq : L + (n - sigma10 B - L) = n - sigma10 B := by
              omega
            obtain ⟨c, hc⟩ := hcost
            refine ⟨c, ?_⟩
            rw [show ((L + (n - sigma10 B - L) : ℕ) : ZMod m) =
                ((n - sigma10 B : ℕ) : ZMod m) from by rw [heq]] at hc
            exact hc)) hLge
    · -- m = 1 : n = R, residu trivial dans ZMod 1
      have hm1' : m = 1 := by omega
      subst hm1'
      obtain ⟨u, hu8, huK⟩ := fibre_u_exists L (by omega) r0 hr04
      refine existence_step n R 1 B d hnm hRm hRd hRB hBl hB0 hBn
        L u hu8 ?_ ?_ hLge ?_
      · exact Subsingleton.elim _ _
      · rw [fibre_sigma u L hu8, huK]; omega
      · rw [allNonzero, List.all_eq_true]
        intro x hx
        rw [fibre_digits u L hu8] at hx
        rw [List.mem_map] at hx
        obtain ⟨e, -, rfl⟩ := hx; simp

/-- Theoreme principal A077754 : tout n hors des exceptions
    admet un multiple a >= 2 chiffres non nuls, somme n. -/
theorem A077754 (n : ℕ) :
    (∃ N : ℕ, n ∣ N ∧ allNonzero N ∧ sigma10 N = n ∧
        (Nat.digits 10 N).length ≥ 2)
    ↔ n ∉ ({1, 2, 5, 11} ∪ {m : ℕ | 10 ∣ m} : Set ℕ) := by
  constructor
  · -- necessite : chaque exception detruit un parametre [T-Lean]
    rintro ⟨N, hdiv, hnon, hsum, hlen⟩ hmem
    have hN10 : N ≥ 10 := by
      by_cases hN0 : N = 0
      · subst hN0; simp [Nat.digits] at hlen
      · have hlen' := Nat.length_digits 10 N (by norm_num) hN0
        have hlog : Nat.log 10 N ≥ 1 := by omega
        have h2 : (10 : ℕ) ^ 1 ≤ 10 ^ Nat.log 10 N :=
          Nat.pow_le_pow_right (by norm_num) hlog
        have h3 := Nat.pow_log_le_self 10 hN0
        omega
    rcases hmem with (rfl | rfl | rfl | rfl) | hten
    · exact exc_1 N hN10 hnon (by rwa [hsum])
    · exact exc_2 N hdiv hN10 hnon (by rwa [hsum])
    · exact exc_5 N hdiv hN10 hnon (by rwa [hsum])
    · exact exc_11 N hdiv hN10 hnon (by rwa [hsum])
    · have hf : allNonzero N = false :=
        exc_10 n hten N hdiv hN10
      exact absurd hnon (by simp [hf])
  · -- existence : voir theorem existence plus bas
    intro hmem
    exact existence n hmem

