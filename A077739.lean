import Mathlib
import A077754

/-!
# A077739 — multiple de n commencant et finissant par n,
somme de chiffres n. Conjecture : a(n)=0 ssi n∈{11,17,19}.

Enonces principaux co-rediges avec argon (accord complet) :
- `A077739` : l'equivalence complete (VERIFICATIONS/
  A077739-resp.txt).
- `L3c` : lemme fibre a somme cible avec seuil
  (VERIFICATIONS/L3c-resp.txt) — remplace L3 refute par
  les contre-exemples (37,2) et (101,3).

Reduction : N = concat(n,c,n) = n*10^(L+d) + c*10^d + n,
donc n|N <=> m'|c avec m' = n/gcd(n,10^d), et sigma(N)=n
<=> sigma(c) = n-2*sigma(n).
-/

/-- Lemme fibre a somme cible s — forme L3d, accord argon.
    Construction : c = fibre u L avec L = s/5 positions ;
    sigma(fibre) = L + (4L + r0) = 5L + r0 = s pour
    r0 = s mod 5 ; residu t = 0 atteint car la condition de
    coset se reduit a g | 5L+r0 = g | s = hypothese (i). -/
theorem L3d (m s : ℕ) (hm : m ≥ 1) (hcop : Nat.Coprime m 10)
    (hi : Nat.gcd 9 m ∣ s) (hii : s ≥ 15 * (m / 27 + 1) + 20) :
    ∃ c : ℕ, m ∣ c ∧ (Nat.digits 10 c).sum = s := by
  obtain ⟨k, hk⟩ := hi
  have hsr : 5 * (s / 5) + s % 5 = s := by omega
  have hL : 3 * (m / 27 + 1) + 4 ≤ s / 5 := by omega
  haveI : NeZero m := ⟨by omega⟩
  have hcos : ∃ c : ℤ, (0 : ZMod m) =
      ((5 * (s / 5) + s % 5 : ℕ) : ZMod m) +
      ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m) := by
    refine ⟨-(k : ℤ), ?_⟩
    rw [hsr, hk]
    push_cast
    ring
  obtain ⟨u, hu8, hsum, hval⟩ := residue_reach m hcop
      (0 : ZMod m) (s / 5) (s % 5) hL (by omega) hcos
  refine ⟨fibre u (s / 5), ?_, ?_⟩
  · exact (CharP.cast_eq_zero_iff (ZMod m) m _).mp hval
  · change sigma10 (fibre u (s / 5)) = s
    rw [fibre_sigma u (s / 5) hu8, hsum]; omega

/-- Reduction : n divise la concatenation n|N <=> m'|c
    avec m' = n/gcd(n,10^d). -/
theorem concat_div_iff (n c L : ℕ) (hn : 1 ≤ n) (d : ℕ) :
    n ∣ (n * 10 ^ (L + d) + c * 10 ^ d + n) ↔
    (n / Nat.gcd n (10 ^ d)) ∣ c := by
  have hsplit : n ∣ (n * 10 ^ (L + d) + c * 10 ^ d + n) ↔
      n ∣ c * 10 ^ d := by
    have h1 : n ∣ n * 10 ^ (L + d) + n :=
      Nat.dvd_add (Nat.dvd_mul_right n _) (dvd_refl n)
    rw [show n * 10 ^ (L + d) + c * 10 ^ d + n =
        (n * 10 ^ (L + d) + n) + c * 10 ^ d from by omega]
    exact Nat.dvd_add_right h1
  rw [hsplit]
  set g := Nat.gcd n (10 ^ d) with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨m', hm'⟩ := Nat.gcd_dvd_left n (10 ^ d)
  obtain ⟨t, ht⟩ := Nat.gcd_dvd_right n (10 ^ d)
  rw [← hg] at hm' ht
  have hm'e : n / g = m' := Nat.div_eq_of_eq_mul_right hgpos hm'
  have hte : 10 ^ d / g = t := Nat.div_eq_of_eq_mul_right hgpos ht
  have hcop : Nat.Coprime m' t := by
    rw [← hm'e, ← hte]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  constructor
  · intro h
    rw [hm'e]
    have h2 : g * m' ∣ c * (g * t) := by
      rw [← hm', ← ht]; exact h
    rw [show c * (g * t) = g * (c * t) from by ring] at h2
    have h3 : m' ∣ c * t := Nat.dvd_of_mul_dvd_mul_left hgpos h2
    exact hcop.dvd_of_dvd_mul_right h3
  · rintro ⟨k, hk⟩
    use k * t
    rw [hk]
    calc (n / g) * k * 10 ^ d
        = (n / g) * g * (k * t) := by rw [ht]; ring
      _ = n * (k * t) := by
          rw [show (n / g) * g * (k * t) =
              n / Nat.gcd n (10 ^ d) * Nat.gcd n (10 ^ d) * (k * t)
              from by rw [hg]]
          rw [Nat.div_mul_cancel (Nat.gcd_dvd_left n (10 ^ d))]

/-- Somme de la concatenation :
    sigma(concat(n,c,n)) = 2*sigma(n) + sigma(c). -/
theorem concat_sigma (n c L : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (hd : d = (Nat.digits 10 n).length)
    (hc : c < 10 ^ L) :
    (Nat.digits 10 (n * 10 ^ (L + d) + c * 10 ^ d + n)).sum
      = 2 * (Nat.digits 10 n).sum + (Nat.digits 10 c).sum := by
  have hnn : 0 < n := by omega
  have hN : n * 10 ^ (L + d) + c * 10 ^ d + n =
      n + 10 ^ d * (c + n * 10 ^ L) := by
    rw [pow_add]; ring
  rw [hN]
  have hlow : Nat.digits 10 (n + 10 ^ d * (c + n * 10 ^ L)) =
      Nat.digits 10 n ++ Nat.digits 10 (c + n * 10 ^ L) := by
    rw [hd]
    exact (Nat.digits_append_digits (by norm_num : (0 : ℕ) < 10)
      (n := n) (m := c + n * 10 ^ L)).symm
  rw [hlow, List.sum_append]
  have hmid : (Nat.digits 10 (c + n * 10 ^ L)).sum =
      (Nat.digits 10 c).sum + (Nat.digits 10 n).sum := by
    have hle : (Nat.digits 10 c).length ≤ L :=
      (Nat.digits_length_le_iff (by norm_num) c).mpr hc
    have he : (Nat.digits 10 c).length +
        (L - (Nat.digits 10 c).length) = L := by omega
    have hz := Nat.digits_append_zeroes_append_digits (b := 10)
      (k := L - (Nat.digits 10 c).length) (m := n) (n := c)
      (by norm_num) hnn
    rw [he] at hz
    have hcomm : c + 10 ^ L * n = c + n * 10 ^ L := by ring
    rw [hcomm] at hz
    rw [← hz, List.sum_append, List.sum_append, List.sum_replicate]
    simp
  rw [hmid]; ring

/-- Liste de chiffres de N = concat(n,c,n) : forme
    dn ++ dc ++ dn (little-endian). -/
theorem concat_digits (n c : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (hd : d = (Nat.digits 10 n).length) :
    Nat.digits 10 (n * 10 ^ ((Nat.digits 10 c).length + d) +
        c * 10 ^ d + n) =
      Nat.digits 10 n ++ Nat.digits 10 c ++ Nat.digits 10 n := by
  have hN : n * 10 ^ ((Nat.digits 10 c).length + d) + c * 10 ^ d + n
      = n + 10 ^ d * (c + 10 ^ (Nat.digits 10 c).length * n) := by
    rw [pow_add]; ring
  rw [hN, hd]
  rw [← Nat.digits_append_digits (b := 10) (by norm_num)
      (n := n) (m := c + 10 ^ (Nat.digits 10 c).length * n)]
  rw [← Nat.digits_append_digits (b := 10) (by norm_num)
      (n := c) (m := n)]
  rw [← List.append_assoc]

/-- Existence a partir du temoin c : si m'|c et
    sigma(c) = n - 2*sigma(n) >= 0, alors N = concat(n,c,n)
    convient. -/
theorem exists_of_wit (n c : ℕ) (hn : 1 ≤ n)
    (hdiv : (n / Nat.gcd n (10 ^ (Nat.digits 10 n).length)) ∣ c)
    (hs : (Nat.digits 10 c).sum + 2 * (Nat.digits 10 n).sum = n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).sum = n ∧
      Nat.digits 10 n <:+ Nat.digits 10 N ∧
      Nat.digits 10 n <+: Nat.digits 10 N := by
  set d := (Nat.digits 10 n).length
  set L := (Nat.digits 10 c).length
  set N := n * 10 ^ (L + d) + c * 10 ^ d + n
  have hd : d = (Nat.digits 10 n).length := rfl
  refine ⟨N, by positivity, ?_, ?_, ?_, ?_⟩
  · exact (concat_div_iff n c L hn d).mpr hdiv
  · rw [show N = n * 10 ^ (L + d) + c * 10 ^ d + n from rfl,
        concat_sigma n c L hn d hd
          (Nat.lt_base_pow_length_digits (by norm_num))]
    omega
  · rw [show N = n * 10 ^ (L + d) + c * 10 ^ d + n from rfl,
        concat_digits n c hn d hd]
    exact ⟨Nat.digits 10 n ++ Nat.digits 10 c, by simp⟩
  · rw [show N = n * 10 ^ (L + d) + c * 10 ^ d + n from rfl,
        concat_digits n c hn d hd]
    exact ⟨Nat.digits 10 c ++ Nat.digits 10 n, by simp⟩

/-- m' = n/gcd(n,10^d) n'est jamais divisible par 10 :
    sinon 10^{d+1} | n, or n < 10^d. -/
theorem mp_not10 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 10 ∣ n / Nat.gcd n (10 ^ (Nat.digits 10 n).length) := by
  intro h10
  set d := (Nat.digits 10 n).length with hd
  set g := Nat.gcd n (10 ^ d) with hg
  set m' := n / g with hm'
  have hn0 : n ≠ 0 := by omega
  have hgpos : 0 < g := by
    rw [hg]; exact Nat.gcd_pos_of_pos_left _ (by omega)
  have hgm : n = g * m' := by
    rw [hm', mul_comm]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n _)).symm
  have hm'0 : m' ≠ 0 := fun h => hn0 (by rw [hgm, h, mul_zero])
  have hvd : ∀ p : ℕ, p.Prime → p ∣ m' → p ∣ 10 →
      d + 1 ≤ padicValNat p n := by
    intro p hp hpd hp10
    haveI : Fact p.Prime := ⟨hp⟩
    have hcd : padicValNat p m' =
        padicValNat p n - padicValNat p g :=
      padicValNat.div_of_dvd (Nat.gcd_dvd_left n (10 ^ d))
    have hfg := Nat.factorization_gcd hn0
      (pow_ne_zero d (show (10 : ℕ) ≠ 0 by norm_num))
    have hcg : padicValNat p g =
        min (padicValNat p n) (padicValNat p (10 ^ d)) := by
      have happ := DFunLike.congr_fun hfg p
      rw [Finsupp.inf_apply] at happ
      rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
          Nat.factorization_def _ hp] at happ
      rw [hg]; exact happ
    have h10v : padicValNat p 10 = 1 := by
      have h1 : 1 ≤ padicValNat p 10 :=
        (padicValNat_dvd_iff_le_of_ne_one hp.ne_one
          (by norm_num)).mp (by simpa using hp10)
      have h2 : padicValNat p 10 < 2 := by
        by_contra h
        push_neg at h
        have hsq : p ^ 2 ∣ 10 :=
          (padicValNat_dvd_iff_le_of_ne_one hp.ne_one
            (by norm_num)).mpr h
        have hle : p ^ 2 ≤ 10 := Nat.le_of_dvd (by norm_num) hsq
        have hp3 : p ≤ 3 := by nlinarith
        interval_cases p <;> revert hsq hp <;> decide
      omega
    have hge1 : 1 ≤ padicValNat p m' :=
      (padicValNat_dvd_iff_le hm'0).mp (by simpa using hpd)
    have hvpd : padicValNat p (10 ^ d) = d := by
      rw [padicValNat.pow, h10v, mul_one]
    rw [hcd, hcg, hvpd] at hge1
    omega
  have h2m : 2 ∣ m' := (by norm_num : (2 : ℕ) ∣ 10).trans h10
  have h5m : 5 ∣ m' := (by norm_num : (5 : ℕ) ∣ 10).trans h10
  have h2n : 2 ^ (d + 1) ∣ n := by
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact (padicValNat_dvd_iff_le hn0).mpr
      (hvd 2 (by norm_num) h2m (by norm_num))
  have h5n : 5 ^ (d + 1) ∣ n := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact (padicValNat_dvd_iff_le hn0).mpr
      (hvd 5 (by norm_num) h5m (by norm_num))
  have h10n : 10 ^ (d + 1) ∣ n := by
    rw [show (10 : ℕ) = 2 * 5 from by norm_num, Nat.mul_pow]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _
        (by norm_num : Nat.Coprime 2 5))) h2n h5n
  have hlt : n < 10 ^ d :=
    Nat.lt_base_pow_length_digits (by norm_num)
  have hle : 10 ^ (d + 1) ≤ n := Nat.le_of_dvd (by omega) h10n
  have hgt : (10 : ℕ) ^ d < 10 ^ (d + 1) := by
    rw [pow_succ]; nlinarith [Nat.one_le_pow d 10 (by norm_num)]
  omega

def wit739 : ℕ → ℕ
  | 10 => 8
  | 12 => 6
  | 13 => 104
  | 14 => 112
  | 15 => 3
  | 16 => 20
  | 18 => 0
  | 20 => 79
  | 21 => 168
  | 22 => 77
  | 23 => 184
  | 24 => 48
  | 25 => 29
  | 26 => 91
  | 27 => 27
  | 28 => 35
  | 29 => 232
  | 30 => 699
  | 31 => 2759
  | 32 => 688
  | 33 => 759
  | 34 => 578
  | 35 => 469
  | 36 => 99
  | 37 => 296
  | 38 => 475
  | 39 => 78
  | 40 => 6998
  | 41 => 18778
  | 42 => 4998
  | 43 => 4988
  | 44 => 5599
  | 45 => 999
  | 46 => 989
  | 47 => 799
  | 48 => 888
  | 49 => 2597
  | 50 => 49999
  | 51 => 68799
  | 52 => 58799
  | 53 => 29998
  | 54 => 19899
  | 55 => 53999
  | 56 => 9898
  | 57 => 17898
  | 58 => 6989
  | 59 => 8968
  | 60 => 399999
  | 61 => 598898
  | 62 => 579979
  | 63 => 199899
  | 64 => 299888
  | 65 => 179998
  | 66 => 339999
  | 67 => 169979
  | 68 => 79798
  | 69 => 66999
  | 70 => 3999989
  | 71 => 1999999
  | 72 => 1999998
  | 73 => 2999789
  | 74 => 3589999
  | 75 => 699999
  | 76 => 699998
  | 77 => 3299989
  | 78 => 599898
  | 79 => 779888
  | 80 => 39999988
  | 81 => 19899999
  | 82 => 28799999
  | 83 => 19799899
  | 84 => 8899989
  | 85 => 7898999
  | 86 => 7799899
  | 87 => 3999999
  | 88 => 12999998
  | 89 => 5988988
  | 90 => 99999999
  | 91 => 499679999
  | 92 => 89999989
  | 93 => 98999988
  | 94 => 89798999
  | 95 => 69889999
  | 96 => 69999888
  | 97 => 58998989
  | 98 => 47899999
  | 99 => 109899999
  | 100 => 89999999999
  | 101 => 89989999999
  | 102 => 79999999899
  | 103 => 79988999999
  | 104 => 59999899999
  | 105 => 49999899999
  | 106 => 48999998999
  | 107 => 39999997999
  | 108 => 19899999999
  | 109 => 19999899989
  | 110 => 889999999999
  | 111 => 888999999999
  | 112 => 799989999998
  | 113 => 698999899999
  | 114 => 499999998999
  | 115 => 399999989999
  | 116 => 389999999998
  | 117 => 297999999999
  | 118 => 198999899999
  | 119 => 99998999989
  | 120 => 6999999999999
  | 121 => 8799999998999
  | 122 => 6899999899999
  | 123 => 6897999999999
  | 124 => 4989899999999
  | 125 => 1999999999999
  | 126 => 999999999999
  | 127 => 1989899999999
  | 128 => 1999999999888
  | 129 => 889999899999
  | 130 => 69899999999999
  | 131 => 78989999998999
  | 132 => 66999999999999
  | 133 => 59989979999999
  | 134 => 48989989999999
  | 135 => 19899999999999
  | 136 => 9999999999989
  | 137 => 8999999899999
  | 138 => 7999999998999
  | 139 => 8988999998999
  | 140 => 599989999999999
  | 141 => 588999999999999
  | 142 => 499998899999999
  | 143 => 699697999999999
  | 144 => 199999999999998
  | 145 => 198989999999999
  | 146 => 98999998999999
  | 147 => 89997999999999
  | 148 => 185999999999999
  | 149 => 68999999899999
  | 150 => 3999999999999999
  | 151 => 3999998999999999
  | 152 => 3899999989999999
  | 153 => 1999999999899999
  | 154 => 4697999999999999
  | 155 => 1799999999999899
  | 156 => 897999999999999
  | 157 => 879999989999999
  | 158 => 879999989899999
  | 159 => 499999998999999
  | 160 => 49999999999999988
  | 161 => 58899999999899989
  | 162 => 19899999999999999
  | 163 => 19998998999999999
  | 164 => 28879999999999999
  | 165 => 42999999999999999
  | 166 => 7979999999999999
  | 167 => 7999988999998999
  | 168 => 4998999999999999
  | 169 => 5898999899999999
  | 170 => 298999999999999999
  | 171 => 199999999999899999
  | 172 => 198999999999999998
  | 173 => 99799999999999999
  | 174 => 88999999999899999
  | 175 => 68999999999999999
  | 176 => 239999999999999998
  | 177 => 59998999999989999
  | 178 => 48899999999999999
  | 179 => 49989998998999999
  | 180 => 999999999999999999
  | 181 => 1998899999999999999
  | 182 => 899899999999999999
  | 183 => 899999899999998999
  | 184 => 789999989999999999
  | 185 => 2479999999999999999
  | 186 => 598989999999999999
  | 187 => 2299989999999998999
  | 188 => 399989999998999999
  | 189 => 298998999999999999
  | 190 => 9999999989999999999
  | 191 => 9999999999998989999
  | 192 => 9999999999999999888
  | 193 => 7989999999999998999
  | 194 => 6999999999999998989
  | 195 => 4899999999999999999
  | 196 => 4999799999999999999
  | 197 => 3999999999899999899
  | 198 => 999999999999999999
  | 199 => 999999999999899999
  | 200 => 7999999999999999999999
  | 201 => 8989999999999999999899
  | 202 => 8987999999999999999999
  | 203 => 7898999999999899999999
  | 204 => 4999998999999999999999
  | 205 => 5798999999999999999999
  | 206 => 3998999999999998999999
  | 207 => 1999999998999999999999
  | 208 => 1899999999999999999998
  | 209 => 999998999999999899999
  | 210 => 79989999999999999999999
  | 211 => 79999999999999998998999
  | 212 => 69998998999999999999999
  | 213 => 49999999999999999999998
  | 214 => 49899999999999999989999
  | 215 => 38999999989999999999999
  | 216 => 19899999999999999999999
  | 217 => 19999999999999899899999
  | 218 => 9999899999999999999989
  | 219 => 9999987999999999999999
  | 220 => 779999999999999999999999
  | 221 => 699989999999899999999999
  | 222 => 777999999999999999999999
  | 223 => 589999998999999989999999
  | 224 => 498999999999999999999988
  | 225 => 99999999999999999999999
  | 226 => 199989999999999999999899
  | 227 => 99998999999999999998999
  | 228 => 79999999999989999999999
  | 229 => 79999898999999999999999
  | 230 => 5989999999999999999999999
  | 231 => 7698999999999999999999999
  | 232 => 3989999999999999999999999
  | 233 => 3999998999999999998999999
  | 234 => 999999999999999999999999
  | 235 => 999999999999999999989999
  | 236 => 998999999999999899999999
  | 237 => 899999979999999999999999
  | 238 => 799999898999999999999999
  | 239 => 899878999999999999999999
  | 240 => 49999999999999999999999998
  | 241 => 58999999999989999998999999
  | 242 => 56999999999999989999999999
  | 243 => 19999999999899999999999999
  | 244 => 19899999998999999999999999
  | 245 => 8999999999998999999999999
  | 246 => 18978999999999999999999999
  | 247 => 7999999899999989999999999
  | 248 => 5998999999999999999999999
  | 249 => 4999899999999999999999999
  | 250 => 299999999999999999999999999
  | 251 => 389999999999999999999989999
  | 252 => 189999999999999999999999999
  | 253 => 559898999999999999999999999
  | 254 => 99999989989999999999999999
  | 255 => 79999899999999999999999999
  | 256 => 99999999999999999999989888
  | 257 => 69989999989999999999999999
  | 258 => 59989998999999999999999999
  | 259 => 79994999999999999999999999
  | 260 => 2899999999999999999999999999
  | 261 => 1999999998999999999999999999
  | 262 => 999999999989999999999999999
  | 263 => 999999999999989999999989999
  | 264 => 3399999999999999999999999999
  | 265 => 788999999999999999999999999
  | 266 => 599989999999999999999999999
  | 267 => 598999999999999999998999999
  | 268 => 399999999999999999999899999
  | 269 => 398999999999999999998999999
  | 270 => 19899999999999999999999999999
  | 271 => 77786999999999999999999999999
  | 272 => 9999999999999989999999999998
  | 273 => 7999899999999999999999999999
  | 274 => 8999899799999999999999999999
  | 275 => 31999999999999999999999999999
  | 276 => 4999999999999999999899999999
  | 277 => 4989999999899999999999999999
  | 278 => 2999999999999989999999999999
  | 279 => 1999999999899999999999999999
  | 280 => 89999999999999999999999999999
  | 281 => 99998999999989999999999999999
  | 282 => 88999999999999989999999999999
  | 283 => 77999999999999999999999999999
  | 284 => 49999999999999999999999999999
  | 285 => 49999989999999999999999999999
  | 286 => 139997999999999999999999999999
  | 287 => 48899999999989999999999999999
  | 288 => 29999999999999999999999999988
  | 289 => 19999999998899999999999999999
  | 290 => 899999999999999999899999999999
  | 291 => 889899999999999999999999999999
  | 292 => 889989989999999999999999999999
  | 293 => 699999999997999999999999999999
  | 294 => 589999999999999999989999999999
  | 295 => 399999999999999999999999899999
  | 296 => 1369999999999999999999999999999
  | 297 => 1099999899999999999999999999999
  | 298 => 199998999999999999998999999999
  | 299 => 98999999999899999999999999999
  | 300 => 699999999999999999999999999999999
  | 301 => 799999989999999899999999999999999
  | 302 => 699999999999999899999999999999998
  | 303 => 796899999999999999999999999999999
  | 304 => 499999999999999899999999999999998
  | 305 => 398999999999999999999999998999999
  | 306 => 99999999999999999999999999999999
  | 307 => 189999999999999999999999899999999
  | 308 => 99998899999999999999999999999999
  | 309 => 88999999999999999999998999999999
  | 310 => 7899999999999899999999999999999999
  | 311 => 6999999999989999999999989999999999
  | 312 => 5889999999999999999999999999999999
  | 313 => 4999899999999999999999989999999999
  | 314 => 3999999999999999989999989999999999
  | 315 => 1999989999999999999999999999999999
  | 316 => 999989999999999999999999999999999
  | 317 => 899999999999999999998999999999999
  | 318 => 899999899899999999999999999999999
  | 319 => 889899999999999999999999989999999
  | 320 => 79999999999999999999999999999999888
  | 321 => 58999999999999999999989999999999999
  | 322 => 48999998999999999999999999999999999
  | 323 => 39899999999999999999999998999999999
  | 324 => 19899999999999999999999999999999999
  | 325 => 19799999999999999999999999999999999
  | 326 => 9998999999999999998999999999999999
  | 327 => 8999989999999999999998999999999999
  | 328 => 8897999999999999999999999999999999
  | 329 => 6979999999999999999999999999999999
  | 330 => 669999999999999999999999999999999999
  | 331 => 489999999999999999999998999999999999
  | 332 => 299999999999999999999999999989999999
  | 333 => 666999999999999999999999999999999999
  | 334 => 189999998999999999999999999999999999
  | 335 => 89999999999999999999998999999999999
  | 336 => 88999999999999999999999999999999998
  | 337 => 79999999999999999999899999999989999
  | 338 => 69989999999999999999999999989999999
  | 339 => 49999999999999998999999999999999999
  | 340 => 3989999999999999999999999999999999999
  | 341 => 6797999999999999999999989999999999999
  | 342 => 999999999999999999999999999999999999
  | 343 => 1998999999999999999999999999999999899
  | 344 => 999989998999999999999999999999999999
  | 345 => 799999999999999999989999999999999999
  | 346 => 799989999999989999999999999999999999
  | 347 => 699999899999999999998999999999999999
  | 348 => 499999999999999999999989999999999999
  | 349 => 499999998999899999999999999999999999
  | 350 => 28999999999999999999999999999999999999
  | 351 => 47998899999999999999999999999999999999
  | 352 => 47999999999999999999999999999999999996
  | 353 => 9999989899999999999999999999999999999
  | 354 => 8989999999999999999999999999999999989
  | 355 => 7989999999999999999989999999999999999
  | 356 => 5999999999999999999999999999999999899
  | 357 => 4999999999999999999999999989999999999
  | 358 => 4999999999899999998999999999999999999
  | 359 => 3899999999899999999999999999999999999
  | 360 => 99999999999999999999999999999999999999
  | 361 => 199999999998999999999999999999999999989
  | 362 => 89999999999999999999999999998999999999
  | 363 => 439999999899999999999999999999999999999
  | 364 => 89988899999999999999999999999999999999
  | 365 => 69999799999999999999999999999999999999
  | 366 => 59989899999999999999999999999999999999
  | 367 => 49999899999999999999999989999999999999
  | 368 => 39999999999899999999999999999999999998
  | 369 => 29988999999999999999999999999999999999
  | 370 => 3959999999999999999999999999999999999999
  | 371 => 1889999999999999999999998999999999999999
  | 372 => 799989999999999999999999999999999999999
  | 373 => 888999999989999999999999999999999999999
  | 374 => 2498999999999998999999999999999999999999
  | 375 => 399999999999999999999999999999999999999
  | 376 => 399999999999999999999999999999899999999
  | 377 => 489999999999999998999999899999999999999
  | 378 => 189999999999999999999999999999999999999
  | 379 => 199999899999999999999999999999989999999
  | 380 => 7999999999999999999999999999999999999999
  | 381 => 8899999999999999999999999998999999999999
  | 382 => 7999999899999999999999989999999999999999
  | 383 => 6999999999999989999999989999999999999999
  | 384 => 6999999999999999999999999999999999999888
  | 385 => 21999899999999999999999999999999999999999
  | 386 => 3999999899999999999999999999999999999998
  | 387 => 2989999989999999999999999999999999999999
  | 388 => 999999999999999999999999999999989999999
  | 389 => 989999999999999999999999999999989999999
  | 390 => 79989999999999999999999999999999999999999
  | 391 => 79999999999899999999999999999999999998999
  | 392 => 59999999999999999999999999999999999999899
  | 393 => 59989999999899999999999999999999999999999
  | 394 => 48999999999999999999999999999999899999999
  | 395 => 38998999999999999999999999999999999999999
  | 396 => 9999999999999999999999999999999999999999
  | 397 => 18999999999999999999999999999999999999989
  | 398 => 9999999999989999998999999999999999999999
  | 399 => 9979989999999999999999999999999999999999
  | 400 => 69999999999999999999999999999999999999999998
  | 401 => 69899999999899999999999999999999999999999999
  | 402 => 49999999999899999999999999999999999999999999
  | 403 => 49999999999999999998999999999899999999999999
  | 404 => 59599999999999999999999999999999999999999999
  | 405 => 19899999999999999999999999999999999999999999
  | 406 => 19999999999998999999999999999999999999989999
  | 407 => 29896999999999999999999999999999999999999999
  | 408 => 7999999989999999999999999999999999999999999
  | 409 => 7999999999999999999999999999999999989999998
  | 410 => 589999999999999999999999999999999999999999999
  | 411 => 699979989999999999999999999999999999999999999
  | 412 => 489999999999899999999999999999999999999999999
  | 413 => 399999999999999989999999989999999999999999999
  | 414 => 99999999999999999999999999999999999999999999
  | 415 => 99999999999999999899999999999999999999999999
  | 416 => 289999999999999999999999999999999999999999996
  | 417 => 89899999999999999999999999999999999999899999
  | 418 => 79999998989999999999999999999999999999999999
  | 419 => 78999989999999999999999999999899999999999999
  | 420 => 4998999999999999999999999999999999999999999999
  | 421 => 4989999999999999999999999989999999999999999999
  | 422 => 3989999999999999999999999899999999999999999999
  | 423 => 1999999999999999999999999899999999999999999999
  | 424 => 1999999899899999999999999999999999999999999999
  | 425 => 899999999899999999999999999999999999999999999
  | 426 => 899998999999999999999999999998999999999999999
  | 427 => 889999999998999999998999999999999999999999999
  | 428 => 698999999999999899999999999999999999999999999
  | 429 => 799797999999999999999999999999999999999999999
  | 430 => 39999999899999999999999999999999999999999999999
  | 431 => 39999999998999999999999999999999998999999999999
  | 432 => 28999999999999999999999999999999999999999999998
  | 433 => 19989999999999999999899999999999999999999999999
  | 434 => 9999989999999999998999999999999999999999999999
  | 435 => 7999999999999999998999999999999999999999999999
  | 436 => 8898999999999999999999999998999999999999999999
  | 437 => 6999999999999999989999999999899999999999999999
  | 438 => 4999998999999999999999999999999999999999999999
  | 439 => 3999999999999999999999999999999999999999989999
  | 440 => 559999999999999999999999999999999999999999999999
  | 441 => 199999999999999999999999999999999899999999999999
  | 442 => 199979999999999999999999999999999999999999999999
  | 443 => 99999999999998999999999989999999999999999999999
  | 444 => 89799999999999999999999999999999999999999999999
  | 445 => 79989999999999999999998999999999999999999999999
  | 446 => 59999999999998999999999999999999999999999999999
  | 447 => 58998999999999999999999999999999999999999999999
  | 448 => 78999899999999999999999999999999999999999999888
  | 449 => 48999999899899999999999999999999999999999999999
  | 450 => 999999999999999999999999999999999999999999999999
  | 451 => 5799989897999999999999999999999999999999999999999
  | 452 => 999899999999999999999999999999999999999999999899
  | 453 => 799999999999999999999999999999999999999899999999
  | 454 => 699999999999999999999999999999899999999999999999
  | 455 => 798889999999999999999999999999999999999999999999
  | 456 => 499999998999999999999999999999999999999999999999
  | 457 => 399999999999999999999999989999999999999999999999
  | 458 => 398999999999999999999999999999999999999999989999
  | 459 => 199999999989999999999999999999999999999999999999
  | 460 => 8999999999999999999999999999999999999999999999999
  | 461 => 9999999999999999999999999989999999999999999999899
  | 462 => 36989799999999999999999999999999999999999999999999
  | 463 => 7999989999999999999999999999999999999998999999999
  | 464 => 6999999999989999999999999999999999999999999999998
  | 465 => 3999999999999999999999999999999999999999999999999
  | 466 => 4989989999999999999999999999999999999999999999999
  | 467 => 3999999998999999999999999999999999999989999999999
  | 468 => 999999999999999999999999999999999999999999999999
  | 469 => 1999999999999989999999999989999999999999999999999
  | 470 => 89999999999999999999999999999999999999899999999999
  | 471 => 89999899999998999999999999999999999999999999999999
  | 472 => 69999999999999999998999999999999999999999999999999
  | 473 => 329899999999999999999999999999999999999999999999999
  | 474 => 67999998999999999999999999999999999999999999999999
  | 475 => 29999999999999999999999999999999999999999999999999
  | 476 => 39899999999999998999999999999999999999999999999999
  | 477 => 28999999999899999999999999999999999999999999999999
  | 478 => 57897989999999999999999999999999999999999999999999
  | 479 => 9999999999999999799999999999999999999999999999999
  | 480 => 899999999999999999999999999999999999999999999999988
  | 481 => 3848999999999999999999999999999999999999999999999999
  | 482 => 699999999999999889999999999999999999999999999999999
  | 483 => 399999999999999999999999999999999999999999999999999
  | 484 => 1299999899999999999999999999999999999999999999999999
  | 485 => 289999999999999999999999999999999999999999999999999
  | 486 => 199999999999989999999999999999999999999999999999999
  | 487 => 199899999999999999999999999998999999999999999999999
  | 488 => 89999989999999999999999999999999999999999999999999
  | 489 => 89999899989999999999999999999999999999999999999999
  | 490 => 6999999999999999999999998999999999999999999999999999
  | 491 => 6999999999999999999999999999999999999899899999999999
  | 492 => 6987999999999999999999999999999999999999999999999999
  | 493 => 4989999999999999999998999999999999999999999999999999
  | 494 => 4998989999999999989999999999999999999999999999999999
  | 495 => 10989999999999999999999999999999999999999999999999999
  | 496 => 999999999999999999999999999999999999999999999999998
  | 497 => 1989999999989999999999999999989999999999999999999999
  | 498 => 899899999999999999999999999999999899999999999999999
  | 499 => 799999799999999999999999999999999999999999999999999
  | _ => 0


/-- Certificat : chaque temoin wit739 verifie m'|c et
    sigma(c) = n - 2*sigma(n) pour n in [10,499] hors
    exceptions. -/
theorem wit739_spec (n : ℕ) (hn10 : 10 ≤ n) (hn500 : n < 500)
    (h11 : n ≠ 11) (h17 : n ≠ 17) (h19 : n ≠ 19) :
    (n / Nat.gcd n (10 ^ (Nat.digits 10 n).length)) ∣ wit739 n ∧
      (Nat.digits 10 (wit739 n)).sum +
        2 * (Nat.digits 10 n).sum = n := by
  interval_cases n <;> first
    | exact absurd rfl h11 | exact absurd rfl h17
    | exact absurd rfl h19 | native_decide

/-- sigma(n) <= 9 * longueur. -/
theorem sigma10_le_9len (n : ℕ) :
    sigma10 n ≤ 9 * (Nat.digits 10 n).length := by
  rw [sigma10]
  by_cases hn : n = 0
  · simp [hn]
  · have h9 : ∀ d ∈ Nat.digits 10 n, d ≤ 9 :=
      fun d hd => Nat.le_of_lt_succ
        (Nat.digits_lt_base (by norm_num) hd)
    have hle : ∀ l : List ℕ, (∀ d ∈ l, d ≤ 9) →
        l.sum ≤ 9 * l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons a l ih =>
        rw [List.sum_cons, List.length_cons]
        have ha := hl a (List.mem_cons_self)
        have hi := ih (fun d hd => hl d
          (List.mem_cons_of_mem a hd))
        omega
    exact hle _ h9

/-- log10 n <= n/125 pour n >= 500. -/
theorem log10_le_125 (n : ℕ) (hn : 500 ≤ n) :
    Nat.log 10 n ≤ n / 125 := by
  set k := Nat.log 10 n
  have hk : 10 ^ k ≤ n := Nat.pow_log_le_self 10 (by omega)
  have h125 : ∀ j : ℕ, 3 ≤ j → 125 * j ≤ 10 ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
      have h9 : 125 ≤ 9 * 10 ^ j := by
        have : (1000 : ℕ) ≤ 10 ^ j :=
          calc (1000 : ℕ) = 10 ^ 3 := by norm_num
            _ ≤ 10 ^ j := Nat.pow_le_pow_right (by norm_num) hj
        omega
      calc 125 * (j + 1) = 125 * j + 125 := by ring
        _ ≤ 10 ^ j + 9 * 10 ^ j := by omega
        _ = 10 ^ (j + 1) := by ring
  by_cases hk3 : 3 ≤ k
  · have : 125 * k ≤ n := le_trans (h125 k hk3) hk
    rw [Nat.mul_comm] at this
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr this
  · have h2 : k ≤ 2 := by omega
    omega

/-- log5 n <= n/100 pour n >= 500. -/
theorem log5_le_100 (n : ℕ) (hn : 500 ≤ n) :
    Nat.log 5 n ≤ n / 100 := by
  set k := Nat.log 5 n
  have hk : 5 ^ k ≤ n := Nat.pow_log_le_self 5 (by omega)
  have h100 : ∀ j : ℕ, 4 ≤ j → 100 * j ≤ 5 ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
      have h4 : 100 ≤ 4 * 5 ^ j := by
        have : (625 : ℕ) ≤ 5 ^ j :=
          calc (625 : ℕ) = 5 ^ 4 := by norm_num
            _ ≤ 5 ^ j := Nat.pow_le_pow_right (by norm_num) hj
        omega
      calc 100 * (j + 1) = 100 * j + 100 := by ring
        _ ≤ 5 ^ j + 4 * 5 ^ j := by omega
        _ = 5 ^ (j + 1) := by ring
  by_cases hk4 : 4 ≤ k
  · have : 100 * k ≤ n := le_trans (h100 k hk4) hk
    rw [Nat.mul_comm] at this
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr this
  · have : k ≤ 3 := by omega
    omega

/-- Etape de concatenation a somme libre : c = B + 10^d.F
    avec R.m | c (R | B, R | 10^d, residu fibre). -/
theorem middle_step (R m B d s : ℕ)
    (hRc : Nat.Coprime R m) (hR10 : R ∣ 10 ^ d) (hRB : R ∣ B)
    (hBl : (Nat.digits 10 B).length = d) (hB0 : B ≠ 0)
    (L : ℕ) (u : ℕ → ℕ) (hu : ∀ e < L, u e ≤ 8)
    (hres : (fibre u L : ZMod m) * (10 : ZMod m) ^ d +
        (B : ZMod m) = 0)
    (hsum : sigma10 B + sigma10 (fibre u L) = s) :
    ∃ c : ℕ, R * m ∣ c ∧ sigma10 c = s := by
  have hdiv : R * m ∣ B + 10 ^ d * fibre u L := by
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd hRc
    · exact dvd_concat_base R B _ d hR10 hRB
    · have hz : ((B + 10 ^ d * fibre u L : ℕ) : ZMod m) = 0 := by
        push_cast
        linear_combination hres
      exact (CharP.cast_eq_zero_iff (ZMod m) m _).mp hz
  refine ⟨B + 10 ^ d * fibre u L, hdiv, ?_⟩
  rw [← hBl, sigma_concat B _ hB0]; exact hsum

/-- Variante de existence_Rm a somme cible s libre.
    Le coset est garanti par g | s (avec L+K = s - sigma B). -/
theorem middle_Rm (s R m : ℕ)
    (hRc : Nat.Coprime R m) (hm : Nat.Coprime m 10)
    (d : ℕ) (hR10 : R ∣ 10 ^ d)
    (B : ℕ) (hRB : R ∣ B) (hBl : (Nat.digits 10 B).length = d)
    (hB0 : B ≠ 0) (hsB : sigma10 B ≤ s)
    (hgs : Nat.gcd 9 m ∣ s)
    (L K : ℕ) (hLK : L + K = s - sigma10 B)
    (hm1 : 1 < m)
    (hcov : ∀ t : ZMod m, (∃ c : ℤ, t = ((L + K : ℕ) : ZMod m) +
        ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) →
      ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = K ∧
        (fibre u L : ZMod m) = t) :
    ∃ c : ℕ, R * m ∣ c ∧ sigma10 c = s := by
  have hunit : IsUnit ((10 : ZMod m) ^ d) := by
    apply IsUnit.pow
    exact (ZMod.isUnit_iff_coprime 10 m).mpr
      (Nat.coprime_comm.mp hm)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  set t : ZMod m := -(B : ZMod m) * v with ht
  have htgt : t * (10 : ZMod m) ^ d + (B : ZMod m) = 0 := by
    rw [ht, mul_assoc]
    have hv' : (v : ZMod m) * (10 : ZMod m) ^ d = 1 := by
      rw [mul_comm]; exact hv
    rw [hv']; simp
  have hcosB : ∃ c : ℤ, t = ((L + K : ℕ) : ZMod m) +
      ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m) := by
    haveI : NeZero m := ⟨by omega⟩
    have hg9 : Nat.gcd 9 m ∣ 9 := Nat.gcd_dvd_left 9 m
    have hgm : Nat.gcd 9 m ∣ m := Nat.gcd_dvd_right 9 m
    set g := Nat.gcd 9 m
    have hmodg : B ≡ sigma10 B [MOD g] := by
      have h9 : (9 : ℤ) ∣ (sigma10 B : ℤ) - B :=
        Nat.ModEq.dvd (Nat.modEq_nine_digits_sum B)
      have hg9z : (g : ℤ) ∣ 9 :=
        Int.natCast_dvd_natCast.mpr hg9
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
      have hBg : ((B : ℕ) : ZMod g) =
          ((sigma10 B : ℕ) : ZMod g) := by
        rw [ZMod.natCast_eq_natCast_iff]; exact hmodg
      have hLKg : ((L + K : ℕ) : ZMod g) =
          -((sigma10 B : ℕ) : ZMod g) := by
        have hsum : L + K + sigma10 B = s := by omega
        apply eq_neg_of_add_eq_zero_left
        rw [← Nat.cast_add, hsum]
        exact (CharP.cast_eq_zero_iff (ZMod g) g s).mpr hgs
      rw [ht, map_mul, map_neg, map_natCast, hcv, mul_one,
          hBg, hLKg]
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
    rw [Int.cast_natCast, ← Nat.cast_mul,
        Nat.mul_div_cancel' hdv, ZMod.natCast_zmod_val]
  obtain ⟨u, hu8, huK, hut⟩ := hcov t hcosB
  refine middle_step R m B d s hRc hR10 hRB hBl hB0 L u hu8
    ?_ ?_
  · rw [hut]; exact htgt
  · have hfs := fibre_sigma u L hu8
    rw [huK] at hfs
    have : sigma10 B + (L + K) = s := by omega
    rw [hfs]; omega

/-- Variante de analytic_budget a somme s : il suffit que
    5*(m/9+7) <= s - sigma B. -/
theorem middle_budget (s m : ℕ)
    (hm10 : Nat.Coprime m 10) (hm1 : 1 < m)
    (σB : ℕ) (hσm : 5 * (m / 9 + 7) ≤ s - σB) (hσn : σB ≤ s)
    (L : ℕ) (hL : L = (s - σB) / 5) (t : ZMod m)
    (hcos : ∃ c : ℤ, t = ((s - σB : ℕ) : ZMod m) +
        ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = s - σB - L ∧
      (fibre u L : ZMod m) = t := by
  obtain ⟨C, hCb, hcov⟩ := coverage m hm10 t
  have hCL : C ≤ L := by
    rw [hL]; omega
  set r0 := (s - σB) % 5 with hr0
  have hr04 : r0 ≤ 4 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))
  obtain ⟨u, hu8, husum, hval⟩ := hcov L hCL r0 hr04 (by
    obtain ⟨c, hc⟩ := hcos
    refine ⟨c, ?_⟩
    have h5r : (5 * L + r0 : ℕ) = s - σB := by
      have := Nat.div_add_mod (s - σB) 5
      rw [hL, hr0]; omega
    rw [h5r]; exact hc)
  refine ⟨u, hu8, ?_, hval⟩
  have hdmod := Nat.div_add_mod (s - σB) 5
  rw [husum]; omega

/-- Budget : pour n >= 500 on a
    5*(n/9+7) + (n/8+8) + 18*len(n) <= n. -/
theorem budget_500 (n : ℕ) (hn : 500 ≤ n) :
    5 * (n / 9 + 7) + (n / 8 + 8) +
      18 * (Nat.digits 10 n).length ≤ n := by
  have hlog : Nat.log 10 n ≤ n / 125 := log10_le_125 n hn
  have hlen : (Nat.digits 10 n).length = Nat.log 10 n + 1 :=
    Nat.length_digits 10 n (by norm_num) (by omega)
  omega

/-- Existence du bloc milieu pour n >= 500 :
    m' | c et sigma(c) = n - 2*sigma(n). -/
theorem middle_large (n : ℕ) (hn : 500 ≤ n) :
    ∃ c : ℕ,
      (n / Nat.gcd n (10 ^ (Nat.digits 10 n).length)) ∣ c ∧
      sigma10 c + 2 * sigma10 n = n := by
  set d := (Nat.digits 10 n).length with hd
  set g := Nat.gcd n (10 ^ d) with hg
  set m' := n / g with hm'
  have hn0 : n ≠ 0 := by omega
  have hgpos : 0 < g := by
    rw [hg]; exact Nat.gcd_pos_of_pos_left _ (by omega)
  have hgm : n = g * m' := by
    rw [hm', mul_comm]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n _)).symm
  have hm'1 : 1 ≤ m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · rw [h, mul_zero] at hgm; omega
    · exact h
  have h10 : ¬ 10 ∣ m' := mp_not10 n (by omega)
  obtain ⟨R, m, D, hdecomp, hm10, hR10, hRc, hR25⟩ :=
    decomp_Rm m' (by omega) h10
  have hm'n : m' ≤ n := Nat.div_le_self n g
  -- Bloc B selon la forme de R = 2^D ou 5^D (D = 0 -> R = 1)
  obtain ⟨B, dB, hRB, hBl, hB0, hR10d, hσB8⟩ :
      ∃ B dB : ℕ, R ∣ B ∧ (Nat.digits 10 B).length = dB ∧
        B ≠ 0 ∧ R ∣ 10 ^ dB ∧ sigma10 B ≤ n / 8 + 8 := by
    rcases hR25 with rfl | rfl
    · rcases Nat.eq_zero_or_pos D with rfl | hD
      · have hsig1 : sigma10 1 = 1 := by
          norm_num [sigma10, Nat.digits, Nat.digitsAux]
        refine ⟨1, 1, by norm_num, ?_, by norm_num, by norm_num,
            by omega⟩
        norm_num [Nat.digits, Nat.digitsAux]
      · obtain ⟨B, hRB, hBl, -, hσB⟩ := lowBlock2 D hD
        have hB0 : B ≠ 0 := by
          rintro rfl; simp at hBl; omega
        have h2D : 2 ^ D ≤ n :=
          le_trans (Nat.le_of_dvd hm'1 ⟨m, hdecomp⟩) hm'n
        refine ⟨B, D, hRB, hBl, hB0,
          pow_dvd_pow_of_dvd (by norm_num) D, ?_⟩
        have hDle : D ≤ Nat.log 2 n :=
          le_log2_of_pow_le hn0 h2D
        have hlog := log2_le_div16 n (by omega)
        omega
    · rcases Nat.eq_zero_or_pos D with rfl | hD
      · have hsig1 : sigma10 1 = 1 := by
          norm_num [sigma10, Nat.digits, Nat.digitsAux]
        refine ⟨1, 1, by norm_num, ?_, by norm_num, by norm_num,
            by omega⟩
        norm_num [Nat.digits, Nat.digitsAux]
      · obtain ⟨B, hRB, hBl, -, hσB⟩ := lowBlock5 D hD
        have hB0 : B ≠ 0 := by
          rintro rfl; simp at hBl; omega
        have h5D : 5 ^ D ≤ n :=
          le_trans (Nat.le_of_dvd hm'1 ⟨m, hdecomp⟩) hm'n
        refine ⟨B, D, hRB, hBl, hB0,
          pow_dvd_pow_of_dvd (by norm_num) D, ?_⟩
        have hDle : D ≤ Nat.log 5 n :=
          Nat.le_log_of_pow_le (by norm_num) h5D
        have hlog := log5_le_100 n (by omega)
        omega
  -- somme cible s = n - 2*sigma(n)
  set s := n - 2 * sigma10 n
  have hsdef : s = n - 2 * sigma10 n := rfl
  have hσn9 : sigma10 n ≤ 9 * d := by
    rw [hd]; exact sigma10_le_9len n
  have hb := budget_500 n hn
  have hm'm : m ≤ m' := Nat.le_of_dvd hm'1
    ⟨R, by rw [hdecomp]; ring⟩
  have hmn : m ≤ n := le_trans hm'm hm'n
  have hσBs : sigma10 B ≤ s := by
    rw [hd] at hσn9; omega
  -- g | s car g | n et sigma(n) ≡ n (mod 9)
  have hgs : Nat.gcd 9 m ∣ s := by
    have hg9 : Nat.gcd 9 m ∣ 9 := Nat.gcd_dvd_left 9 m
    have hg9m : Nat.gcd 9 m ∣ m := Nat.gcd_dvd_right 9 m
    have hgm' : Nat.gcd 9 m ∣ m' :=
      hg9m.trans ⟨R, by rw [mul_comm]; exact hdecomp⟩
    have hgn : Nat.gcd 9 m ∣ n :=
      hgm'.trans ⟨g, by rw [hgm]; ring⟩
    have hmod : sigma10 n ≡ n [MOD Nat.gcd 9 m] := by
      have h9 := Nat.modEq_nine_digits_sum n
      exact (h9.of_dvd hg9).symm
    have hσg : sigma10 n ≡ 0 [MOD Nat.gcd 9 m] :=
      hmod.trans (Nat.modEq_zero_iff_dvd.mpr hgn)
    have hσn : Nat.gcd 9 m ∣ sigma10 n :=
      Nat.modEq_zero_iff_dvd.mp hσg
    have h2σ : Nat.gcd 9 m ∣ 2 * sigma10 n := hσn.mul_left 2
    -- g | n - 2*sigma(n) par factorisation explicite
    obtain ⟨a, ha⟩ := hgn
    obtain ⟨b, hb2⟩ := h2σ
    have hg9pos : 0 < Nat.gcd 9 m := Nat.gcd_pos_of_pos_left m (by omega)
    have hba : b ≤ a := by
      have hle : Nat.gcd 9 m * b ≤ Nat.gcd 9 m * a := by
        rw [← hb2, ← ha]; omega
      exact Nat.le_of_mul_le_mul_left hle hg9pos
    refine ⟨a - b, ?_⟩
    have hdist : Nat.gcd 9 m * (a - b) =
        Nat.gcd 9 m * a - Nat.gcd 9 m * b :=
      Nat.mul_sub_left_distrib _ a b
    rw [hsdef, hb2, ha, hdist]
  have hbud : 5 * (m / 9 + 7) ≤ s - sigma10 B := by
    have h1 : 5 * (m / 9 + 7) ≤ 5 * (n / 9 + 7) := by
      have hdiv : m / 9 ≤ n / 9 := Nat.div_le_div_right hmn
      omega
    omega
  set L := (s - sigma10 B) / 5
  have hLdef : L = (s - sigma10 B) / 5 := rfl
  set r0 := (s - sigma10 B) % 5
  have hr04 : r0 ≤ 4 := Nat.lt_succ_iff.mp
    (Nat.mod_lt _ (by norm_num))
  by_cases hm1 : 1 < m
  · obtain ⟨c, hdiv, hsg⟩ := middle_Rm s R m hRc hm10 dB hR10d
      B hRB hBl hB0 hσBs hgs L (s - sigma10 B - L) (by omega)
      hm1 (fun t hcost =>
        middle_budget s m hm10 hm1 (sigma10 B) hbud hσBs
          L rfl t (by
            have heq : L + (s - sigma10 B - L) =
                s - sigma10 B := by omega
            obtain ⟨c, hc⟩ := hcost
            refine ⟨c, ?_⟩
            rw [show ((L + (s - sigma10 B - L) : ℕ) : ZMod m) =
              ((s - sigma10 B : ℕ) : ZMod m) from by rw [heq]]
              at hc
            exact hc))
    exact ⟨c, hdecomp ▸ hdiv, by omega⟩
  · have hm10' : m = 1 := by
      have hpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hdecomp; omega
        · exact h
      omega
    subst hm10'
    obtain ⟨u, hu8, huK⟩ := fibre_u_exists L (by omega) r0 hr04
    obtain ⟨c, hdiv, hsg⟩ := middle_step R 1 B dB s hRc hR10d
      hRB hBl hB0 L u hu8 (Subsingleton.elim _ _) (by
        have hfs := fibre_sigma u L hu8
        rw [huK] at hfs
        have h5r : 5 * L + r0 = s - sigma10 B :=
          Nat.div_add_mod _ 5
        omega)
    exact ⟨c, hdecomp ▸ hdiv, by omega⟩

/-- Si `p` est à la fois préfixe et suffixe de `l` avec `2·|p| ≤ |l|`,
alors `l = p ++ mid ++ p` pour un bloc médian `mid`. -/
theorem prefix_suffix_mid {p l : List ℕ} (hp : p <+: l) (hs : p <:+ l)
    (hlen : 2 * p.length ≤ l.length) : ∃ mid, l = p ++ mid ++ p := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hs
  have hla : a.length = l.length - p.length := by
    have := congrArg List.length ha
    simp [List.length_append] at this; omega
  have hlb : b.length = l.length - p.length := by
    have := congrArg List.length hb
    simp [List.length_append] at this; omega
  have hd : List.drop (l.length - p.length) l = p := by
    have h : List.drop b.length (b ++ p) = p := List.drop_left
    rw [hb, hlb] at h; exact h
  set n := a.length - p.length with hn_def
  have hda : List.drop n a = p := by
    have hd' : List.drop a.length l = p := by rw [hla]; exact hd
    have ha_eq : a = List.drop p.length l := by
      have h : List.drop p.length (p ++ a) = a := List.drop_left
      rw [ha] at h; exact h.symm
    have e2 : p.length + n = a.length := by omega
    rw [ha_eq, List.drop_drop, e2]
    exact hd'
  refine ⟨a.take n, ?_⟩
  have hsplit : a = a.take n ++ a.drop n :=
    (List.take_append_drop n a).symm
  calc l = p ++ a := ha.symm
    _ = p ++ (a.take n ++ a.drop n) := by rw [← hsplit]
    _ = p ++ (a.take n ++ p) := by rw [hda]
    _ = p ++ a.take n ++ p := by rw [← List.append_assoc]

/-- `alternatingSum` en récursion simple (définition par paires). -/
theorem alternatingSum_cons (a : ℤ) (l : List ℤ) :
    (a :: l).alternatingSum = a - l.alternatingSum := by
  induction l generalizing a with
  | nil => simp [List.alternatingSum, sub_eq_add_neg]
  | cons b t ih =>
    cases t with
    | nil => simp [List.alternatingSum, sub_eq_add_neg]
    | cons c u =>
      show a + -b + (c :: u).alternatingSum =
        a - (b :: c :: u).alternatingSum
      rw [ih b]; ring

/-- Majoration de la somme alternée par la somme des chiffres. -/
theorem altSum_abs_le (l : List ℕ) :
    |(l.map fun (e : ℕ) => (e : ℤ)).alternatingSum| ≤ (l.sum : ℤ) := by
  induction l with
  | nil => simp [List.alternatingSum]
  | cons d ds ih =>
    show |((d : ℤ) :: (ds.map fun (e : ℕ) => (e : ℤ))).alternatingSum| ≤
        ((d :: ds).sum : ℤ)
    rw [alternatingSum_cons, List.sum_cons]
    calc |(d : ℤ) - (ds.map fun (e : ℕ) => (e : ℤ)).alternatingSum|
        ≤ |(d : ℤ)| + |(ds.map fun (e : ℕ) => (e : ℤ)).alternatingSum| :=
          abs_sub _ _
      _ ≤ (d : ℤ) + (ds.sum : ℤ) := by
          rw [abs_of_nonneg (Int.natCast_nonneg d)]
          omega
      _ = ((d + ds.sum : ℕ) : ℤ) := by push_cast; ring

/-- La somme alternée a la parité de la somme des chiffres. -/
theorem altSum_modEq_two (l : List ℕ) :
    (l.map fun (e : ℕ) => (e : ℤ)).alternatingSum ≡ (l.sum : ℤ) [ZMOD 2] := by
  induction l with
  | nil => simp [List.alternatingSum, Int.ModEq]
  | cons d ds ih =>
    show ((d : ℤ) :: (ds.map fun (e : ℕ) => (e : ℤ))).alternatingSum ≡
        ((d :: ds).sum : ℤ) [ZMOD 2]
    rw [alternatingSum_cons, List.sum_cons]
    have hneg : ∀ x : ℤ, -x ≡ x [ZMOD 2] := by
      intro x
      have hd2 : (2 : ℤ) ∣ x - -x := ⟨x, by ring⟩
      exact Int.modEq_iff_dvd.mpr hd2
    have hs : (ds.sum : ℤ) ≡ -(ds.sum : ℤ) [ZMOD 2] := (hneg _).symm
    have e := (Int.ModEq.refl (d : ℤ)).sub (ih.trans hs)
    have hcast : ((d + ds.sum : ℕ) : ℤ) = (d : ℤ) + (ds.sum : ℤ) := by
      push_cast; ring
    rw [hcast]
    simpa [sub_neg_eq_add] using e

/-- Si `l.sum = 0`, tous les chiffres sont nuls et `ofDigits` vaut 0. -/
theorem ofDigits_eq_zero {l : List ℕ} (h : l.sum = 0) :
    Nat.ofDigits 10 l = 0 := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [List.sum_cons] at h
    have hd : d = 0 := by omega
    have hs : ds.sum = 0 := by omega
    calc Nat.ofDigits 10 (d :: ds) = d + 10 * Nat.ofDigits 10 ds := rfl
      _ = 0 + 10 * 0 := by rw [hd, ih hs]
      _ = 0 := by norm_num

/-- Un entier dont les chiffres (dans une écriture quelconque) somment à 1
est une puissance de 10. -/
theorem ofDigits_sum_one {l : List ℕ} (h : l.sum = 1) :
    ∃ j, Nat.ofDigits 10 l = 10 ^ j := by
  induction l with
  | nil => simp at h
  | cons d ds ih =>
    rw [List.sum_cons] at h
    rcases Nat.eq_zero_or_pos d with hd | hd
    · obtain ⟨j, hj⟩ := ih (by omega)
      refine ⟨j + 1, ?_⟩
      calc Nat.ofDigits 10 (d :: ds) = d + 10 * Nat.ofDigits 10 ds := rfl
        _ = 10 ^ (j + 1) := by rw [hd, hj]; ring
    · have hd1 : d = 1 := by omega
      have hs0 : ds.sum = 0 := by omega
      refine ⟨0, ?_⟩
      calc Nat.ofDigits 10 (d :: ds) = d + 10 * Nat.ofDigits 10 ds := rfl
        _ = 10 ^ 0 := by rw [hd1, ofDigits_eq_zero hs0]; ring

theorem A077739 (n : ℕ) (hn : 1 ≤ n) :
    (∃ N : ℕ, 0 < N ∧ n ∣ N ∧
      (Nat.digits 10 N).sum = n ∧
      Nat.digits 10 n <:+ Nat.digits 10 N ∧
      Nat.digits 10 n <+: Nat.digits 10 N) ↔
    n ∉ ({11, 17, 19} : Set ℕ) := by
  constructor
  · -- direction zero : n ∈ {11,17,19} -> pas de temoin
    rintro ⟨N, hN0, hdv, hsum, hsuf, hpre⟩ hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl
    · -- n = 11 : somme alternée de c ≡ 0 mod 11 impossible (|·| ≤ 7, impair)
      have hdn : Nat.digits 10 11 = [1, 1] := by decide
      rw [hdn] at hsuf hpre
      rcases lt_or_ge (Nat.digits 10 N).length 4 with hl | hl
      · obtain ⟨a, ha⟩ := hpre
        obtain ⟨b', hb'⟩ := hsuf
        rcases a with _ | ⟨x, a'⟩
        · rw [List.append_nil] at ha
          rw [← ha] at hsum; norm_num at hsum
        · rcases a' with _ | ⟨y, a''⟩
          · have hb1 : b'.length = 1 := by
              have := congrArg List.length hb'
              rw [← ha] at this; simp at this; omega
            obtain ⟨b0, hb0⟩ : ∃ b0, b' = [b0] := by
              rcases b' with _ | ⟨b0, b''⟩
              · simp at hb1
              · rcases b'' with _ | ⟨b2, b3⟩
                · exact ⟨b0, rfl⟩
                · simp at hb1
            rw [hb0] at hb'
            have e : ([b0, 1, 1] : List ℕ) = Nat.digits 10 N := hb'
            have e2 : ([1, 1, x] : List ℕ) = Nat.digits 10 N := ha
            have e3 := e.trans e2.symm
            simp only [List.cons.injEq] at e3
            rcases e3 with ⟨hb0e, -, hxe, -⟩
            subst hb0e; subst x
            rw [← ha] at hsum; norm_num at hsum
          · have := congrArg List.length ha
            simp at this; omega
      · obtain ⟨mid, hmid⟩ := prefix_suffix_mid hpre hsuf (by simp; omega)
        have hσmid : mid.sum = 7 := by
          rw [hmid] at hsum; simp [List.sum_append] at hsum; omega
        have hof : Nat.ofDigits 10 [1, 1] = 11 := by decide
        have hN : N = 11 + 100 * Nat.ofDigits 10 mid +
            11 * 10 ^ (mid.length + 2) := by
          conv_lhs => rw [← Nat.ofDigits_digits 10 N]
          rw [hmid]
          repeat rw [Nat.ofDigits_append]
          rw [hof]
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          ring_nf
        have h11M : (11 : ℕ) ∣ Nat.ofDigits 10 mid := by
          obtain ⟨t, ht⟩ := hdv
          have hk : 11 * (t - (1 + 10 ^ (mid.length + 2))) =
              100 * Nat.ofDigits 10 mid := by omega
          exact (by decide : Nat.Coprime 11 100).dvd_of_dvd_mul_left
            ⟨t - (1 + 10 ^ (mid.length + 2)), hk.symm⟩
        -- 11 | ofDigits mid → somme alternée ≡ 0 mod 11
        have hcong : ((Nat.ofDigits (10 : ℕ) mid : ℕ) : ℤ) ≡
            (mid.map fun (e : ℕ) => (e : ℤ)).alternatingSum [ZMOD 11] := by
          have h1 : Nat.ofDigits (10 : ℤ) mid ≡
              Nat.ofDigits (-1 : ℤ) mid [ZMOD 11] :=
            Nat.ofDigits_zmodeq' 10 (-1) 11 (by decide) mid
          rw [Nat.ofDigits_neg_one] at h1
          rw [Nat.coe_ofDigits, Nat.cast_ofNat]
          exact h1
        have h11z : ((Nat.ofDigits (10 : ℕ) mid : ℕ) : ℤ) ≡ 0 [ZMOD 11] :=
          Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr h11M)
        have halt := hcong.symm.trans h11z
        have h11dvd : (11 : ℤ) ∣
            (mid.map fun (e : ℕ) => (e : ℤ)).alternatingSum :=
          Int.modEq_zero_iff_dvd.mp halt
        obtain ⟨k, hk⟩ := h11dvd
        have habs := altSum_abs_le mid
        rw [hσmid] at habs
        have hk0 : k = 0 := by
          rw [hk] at habs
          have h2 := abs_le.mp habs
          omega
        rw [hk0] at hk; simp at hk
        -- parité : alt ≡ 7 mod 2 mais alt = 0
        have hpar := altSum_modEq_two mid
        rw [hσmid, hk] at hpar
        exact absurd hpar (by decide)
    · -- n = 17 : σmid = 1 force c = 10^j, 17 ne divise pas
      have hdn : Nat.digits 10 17 = [7, 1] := by decide
      rw [hdn] at hsuf hpre
      rcases lt_or_ge (Nat.digits 10 N).length 4 with hl | hl
      · obtain ⟨a, ha⟩ := hpre
        obtain ⟨b', hb'⟩ := hsuf
        rcases a with _ | ⟨x, a'⟩
        · rw [List.append_nil] at ha
          rw [← ha] at hsum; norm_num at hsum
        · rcases a' with _ | ⟨y, a''⟩
          · have hb1 : b'.length = 1 := by
              have := congrArg List.length hb'
              rw [← ha] at this; simp at this; omega
            obtain ⟨b0, hb0⟩ : ∃ b0, b' = [b0] := by
              rcases b' with _ | ⟨b0, b''⟩
              · simp at hb1
              · rcases b'' with _ | ⟨b2, b3⟩
                · exact ⟨b0, rfl⟩
                · simp at hb1
            rw [hb0] at hb'
            have e : ([b0, 7, 1] : List ℕ) = Nat.digits 10 N := hb'
            have e2 : ([7, 1, x] : List ℕ) = Nat.digits 10 N := ha
            have e3 := e.trans e2.symm
            simp only [List.cons.injEq] at e3
            rcases e3 with ⟨-, h71, -⟩
            norm_num at h71
          · have := congrArg List.length ha
            simp at this; omega
      · obtain ⟨mid, hmid⟩ := prefix_suffix_mid hpre hsuf (by simp; omega)
        have hσmid : mid.sum = 1 := by
          rw [hmid] at hsum; simp [List.sum_append] at hsum; omega
        have hof : Nat.ofDigits 10 [7, 1] = 17 := by decide
        have hN : N = 17 + 100 * Nat.ofDigits 10 mid +
            17 * 10 ^ (mid.length + 2) := by
          conv_lhs => rw [← Nat.ofDigits_digits 10 N]
          rw [hmid]
          repeat rw [Nat.ofDigits_append]
          rw [hof]
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          ring_nf
        have h17M : (17 : ℕ) ∣ Nat.ofDigits 10 mid := by
          obtain ⟨t, ht⟩ := hdv
          have hk : 17 * (t - (1 + 10 ^ (mid.length + 2))) =
              100 * Nat.ofDigits 10 mid := by omega
          exact (by decide : Nat.Coprime 17 100).dvd_of_dvd_mul_left
            ⟨t - (1 + 10 ^ (mid.length + 2)), hk.symm⟩
        obtain ⟨j, hj⟩ := ofDigits_sum_one hσmid
        rw [hj] at h17M
        have hcop : Nat.Coprime 17 (10 ^ j) :=
          Nat.Coprime.pow_right j (by decide : Nat.Coprime 17 10)
        have h1 : (17 : ℕ) ∣ Nat.gcd 17 (10 ^ j) :=
          Nat.dvd_gcd dvd_rfl h17M
        have hgc : Nat.gcd 17 (10 ^ j) = 1 := hcop
        rw [hgc] at h1
        exact absurd h1 (by decide)
    · -- n = 19 : σmid < 0 impossible
      have hdn : Nat.digits 10 19 = [9, 1] := by decide
      rw [hdn] at hsuf hpre
      rcases lt_or_ge (Nat.digits 10 N).length 4 with hl | hl
      · obtain ⟨a, ha⟩ := hpre
        obtain ⟨b', hb'⟩ := hsuf
        rcases a with _ | ⟨x, a'⟩
        · rw [List.append_nil] at ha
          rw [← ha] at hsum; norm_num at hsum
        · rcases a' with _ | ⟨y, a''⟩
          · have hb1 : b'.length = 1 := by
              have := congrArg List.length hb'
              rw [← ha] at this; simp at this; omega
            obtain ⟨b0, hb0⟩ : ∃ b0, b' = [b0] := by
              rcases b' with _ | ⟨b0, b''⟩
              · simp at hb1
              · rcases b'' with _ | ⟨b2, b3⟩
                · exact ⟨b0, rfl⟩
                · simp at hb1
            rw [hb0] at hb'
            have e : ([b0, 9, 1] : List ℕ) = Nat.digits 10 N := hb'
            have e2 : ([9, 1, x] : List ℕ) = Nat.digits 10 N := ha
            have e3 := e.trans e2.symm
            simp only [List.cons.injEq] at e3
            rcases e3 with ⟨-, h91, -⟩
            norm_num at h91
          · have := congrArg List.length ha
            simp at this; omega
      · obtain ⟨mid, hmid⟩ := prefix_suffix_mid hpre hsuf (by simp; omega)
        rw [hmid] at hsum
        simp [List.sum_append] at hsum
        omega
  · intro hmem
    have h11 : n ≠ 11 := by intro he; apply hmem; rw [he]; simp
    have h17 : n ≠ 17 := by intro he; apply hmem; rw [he]; simp
    have h19 : n ≠ 19 := by intro he; apply hmem; rw [he]; simp
    rcases lt_or_ge n 10 with h10 | h10
    · -- 1 <= n <= 9 : N = n
      refine ⟨n, hn, dvd_refl n, ?_, ?_, ?_⟩
      · rw [Nat.digits_of_lt 10 n (by omega) (by omega),
            List.sum_singleton]
      · exact ⟨[], by simp⟩
      · exact ⟨[], by simp⟩
    · by_cases hlt : n < 500
      · -- 10 <= n <= 499 : table de temoins
        obtain ⟨hdv, hsum⟩ := wit739_spec n h10 hlt h11 h17 h19
        exact exists_of_wit n (wit739 n) hn hdv hsum
      · -- n >= 500 : machinerie fibre (L3d + bloc mixte)
        obtain ⟨c, hdiv, hsum⟩ := middle_large n (by omega)
        exact exists_of_wit n c hn hdiv hsum

/-- A077740 : quotient A077739(n)/n — corollaire direct de
    l'enonce A077739 (meme predicats, N = n*q).
    Pour n ∉ {11,17,19}, il existe q > 0 tel que n*q soit de
    somme n et commence et finisse par n. -/
theorem A077740 (n : ℕ) (hn : 1 ≤ n)
    (hne : n ∉ ({11, 17, 19} : Set ℕ)) :
    ∃ q : ℕ, 0 < q ∧
      (Nat.digits 10 (n * q)).sum = n ∧
      Nat.digits 10 n <:+ Nat.digits 10 (n * q) ∧
      Nat.digits 10 n <+: Nat.digits 10 (n * q) := by
  obtain ⟨N, hN0, hdv, hsum, hsuf, hpre⟩ := (A077739 n hn).mpr hne
  obtain ⟨q, rfl⟩ := hdv
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hz | hp
    · rw [hz, mul_zero] at hN0; omega
    · exact hp
  exact ⟨q, hq, hsum, hsuf, hpre⟩
