import Mathlib

/-! ## Certificats bitmap A077754 — module compile separement

    Isole du fichier maitre pour disposer du plafond memoire
    kernel complet en processus frais (le `decide` monolithique
    sur ~1656 elements explosait la reserve accumulee par
    l'elaboration des ~1600 lignes precedentes du fichier
    principal). `checkCoverB` evalue la couverture de la somme
    de Minkowski sur un bitmap `Nat` (bit r = residu r mod M) —
    `decide` peu cher en kernel (arithmetique GMP),
    contrairement a l'evaluation directe de `Finset (ZMod M)`. -/

/-- les elements {2,5}-smooth de X : 16 signes. -/
def Xsmooth25 : List ℤ :=
  [1, 2, 4, 8, 10, 20, 32, 40, -1, -2, -4, -8, -10, -20, -32, -40]

/-- les elements {2,3,5}-smooth de X : 28 signes. -/
def Xsmooth235 : List ℤ :=
  [1, 2, 3, 4, 8, 9, 10, 12, 18, 20, 24, 30, 32, 40,
   -1, -2, -3, -4, -8, -9, -10, -12, -18, -20, -24, -30, -32, -40]

/-- residu canonique de `x : Int` dans `[0, M)` en `Nat`. -/
def xres (M : Nat) (x : Int) : Nat := (((x % (M : Int)) + M) % M).toNat

/-- etage `j` en residus `Nat` (coefficient `(9/g)*10^{3j} mod M`). -/
def stageRes (M j g : Nat) (xs : List Int) : List Nat :=
  let c := ((9 / g) * 10 ^ (3 * j)) % M
  (xs.map (fun x => (c * xres M x) % M)).eraseDups

/-- positions `< M` a bit `1`. -/
def setBits (M : Nat) (bits : Nat) : List Nat :=
  (List.range M).filter fun r => bits.testBit r

/-- `acc ∪ (acc + stage mod M)` en bits. -/
def step (M : Nat) (acc : Nat) (stage : List Nat) : Nat :=
  (setBits M acc).foldl
    (fun a r => stage.foldl (fun a2 s => a2 ||| (1 <<< ((r + s) % M))) a)
    acc

/-- `jmax` etages depuis le bit `0`. -/
def coverBits (M g : Nat) (xs : List Int) (jmax : Nat) : Nat :=
  (List.range jmax).foldl (fun acc j => step M acc (stageRes M (j+1) g xs)) 1

/-- certificat bitmap : tous les bits `< M` poses. -/
def checkCoverB (M g : Nat) (xs : List Int) (jmax : Nat) : Bool :=
  coverBits M g xs jmax == (1 <<< M) - 1

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

private theorem aux_cA : ((List.range' 1 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cB : ((List.range' 13 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cC : ((List.range' 25 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cD : ((List.range' 37 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cE : ((List.range' 49 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cF : ((List.range' 61 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cG : ((List.range' 73 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cH : ((List.range' 85 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cI : ((List.range' 97 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cJ : ((List.range' 109 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cK : ((List.range' 121 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cL : ((List.range' 133 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cM : ((List.range' 145 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cN : ((List.range' 157 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cO : ((List.range' 169 12).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

private theorem aux_cP : ((List.range' 181 4).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  decide

/-- Couverture machine : pour M <= 184 coprime a 10 (les cas
    realisables : g in {1,3,9} avec 3 non|M quand g < 9), la
    somme de 6 etages couvre tout ZMod M. -/
theorem stage_cover_small_aux :
    ((List.range' 1 184).all fun M =>
      (!(Nat.gcd M 10 == 1)) ||
      ((!(Nat.gcd M 3 == 1)) ||
        ((checkCoverB M 1 Xsmooth235 6) &&
          (checkCoverB M 3 Xsmooth25 6))) &&
      (checkCoverB M 9 Xsmooth25 6)) = true := by
  have hsplit : List.range' 1 184 =
      List.range' 1 12 ++ List.range' 13 12 ++ List.range' 25 12 ++ List.range' 37 12 ++ List.range' 49 12 ++ List.range' 61 12 ++ List.range' 73 12 ++ List.range' 85 12 ++ List.range' 97 12 ++ List.range' 109 12 ++ List.range' 121 12 ++ List.range' 133 12 ++ List.range' 145 12 ++ List.range' 157 12 ++ List.range' 169 12 ++ List.range' 181 4 := by
    decide
  rw [hsplit, List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append,
      List.all_append, aux_cA, aux_cB, aux_cC, aux_cD, aux_cE, aux_cF, aux_cG, aux_cH, aux_cI, aux_cJ, aux_cK, aux_cL, aux_cM, aux_cN, aux_cO, aux_cP]
  decide

private theorem auxp_cA : ((List.range' 1 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

private theorem auxp_cB : ((List.range' 415 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

private theorem auxp_cC : ((List.range' 829 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

private theorem auxp_cD : ((List.range' 1243 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

/-- Certificat machine : pour tout m <= 1656 premier a 10 hors
    {11,19,23} avec M = m / gcd(9,m) <= 184, il existe
    k <= m/27+1 etages couvrant ZMod M. -/
theorem stage_cover_small_aux' :
    ((List.range' 1 1656).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  have hsplit : List.range' 1 1656 =
      List.range' 1 414 ++ List.range' 415 414 ++ List.range' 829 414 ++ List.range' 1243 414 := by
    decide
  rw [hsplit, List.all_append, List.all_append,
      List.all_append, auxp_cA, auxp_cB, auxp_cC, auxp_cD]
  decide
