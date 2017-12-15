Add LoadPath "/Users/alex/Documents/Research/projects/brass15/teee/teee/Models/Measuring/cpdt/src" as Cpdt.
Add LoadPath "/home/paul/Documents/TEEE/teee/Models/Measuring/cpdt/src" as Cpdt.
Add LoadPath "C:\Users\Paul\Documents\coqStuff\TEEE\teee\Models\Measuring\cpdt\src" as Cpdt. 

Require Import BareNecessities. 
Require Import Bool.
Require Import Nat. 
(** A Better Units Library
This library gives innate equality-- no axioms needed (well, one I suppose).
The cost is pretty printing.
 *)

Inductive BaseUnit :=
 | Ampere
 | Candela
 | Kelvin
 | KiloGram
 | Meter
 | Mole
 | Second.

Theorem eq_dec_BaseUnit : equality BaseUnit. 
Proof. equal. Defined.
 
Inductive mZ :=
 | pos : nat -> mZ
 | neg : nat -> mZ.
Axiom posNegZero : neg 0 = pos 0.

Theorem eq_dec_mZ : equality mZ. 
Proof. equal. Defined. 
(* 
Inductive DerivedUnit :=
 | Void : DerivedUnit
 | Mult : DerivedUnit -> DerivedUnit -> DerivedUnit
 | Div : DerivedUnit -> DerivedUnit -> DerivedUnit. 
 *)
 
Inductive DerivedUnit :=
 | derivedUnit : mZ -> mZ ->mZ ->mZ ->mZ ->mZ ->mZ -> DerivedUnit.

Definition Void := derivedUnit (pos 0) (pos 0) (pos 0) (pos 0) (pos 0) (pos 0) (pos 0).

Definition mkUnit (b : BaseUnit) : DerivedUnit := 
 match b with
 | Ampere =>    derivedUnit (pos 1) (pos 0) (pos 0) (pos 0) (pos 0) (pos 0) (pos 0)
 | Candela =>   derivedUnit (pos 0) (pos 1) (pos 0) (pos 0) (pos 0) (pos 0) (pos 0)
 | Kelvin =>       derivedUnit (pos 0) (pos 0) (pos 1) (pos 0) (pos 0) (pos 0) (pos 0)
 | KiloGram => derivedUnit (pos 0) (pos 0) (pos 0) (pos 1) (pos 0) (pos 0) (pos 0)
 | Meter =>      derivedUnit (pos 0) (pos 0) (pos 0) (pos 0) (pos 1) (pos 0) (pos 0)
 | Mole =>        derivedUnit (pos 0) (pos 0) (pos 0) (pos 0) (pos 0) (pos 1) (pos 0)
 | Second =>    derivedUnit (pos 0) (pos 0) (pos 0) (pos 0) (pos 0) (pos 0) (pos 1)
end.
Hint Unfold mkUnit. 

Theorem eq_dec_DerivedUnit : equality DerivedUnit.
Proof. equal. Defined.

Definition zadd (x y : mZ) : mZ :=
 match (x,y) with
  | (pos xv, pos yv) => pos (xv + yv)
  | (neg xv, neg yv) => neg (xv + yv)
  | (pos xv, neg yv) => if eqb xv yv then
      pos 0 else
       if ltb xv yv then 
          neg (yv - xv) else 
          pos (xv - yv)
  | (neg xv, pos yv) => if eqb xv yv then
      pos 0 else
       if ltb xv yv then 
          pos (yv - xv) else 
          neg (xv - yv)
  end.

Definition Mult (x y : DerivedUnit) : DerivedUnit :=
 match (x,y) with 
  | (derivedUnit a b c d e f g, derivedUnit a' b' c' d' e' f' g') =>
      derivedUnit (zadd a a') (zadd b b') (zadd c c') 
                  (zadd d d') (zadd e e') (zadd f f')
                  (zadd g g')
 end. 

Definition invert (z : mZ) : mZ :=
match z with
 | pos x => neg x
 | neg x => pos x
end.

Definition flipPowers (du : DerivedUnit) : DerivedUnit :=
match du with
 | derivedUnit a b c d e f g => derivedUnit (invert a) (invert b) (invert c)
                                            (invert d) (invert e) (invert f)
                                            (invert g) 
end.

Definition Div (x y : DerivedUnit) : DerivedUnit := 
 Mult x (flipPowers y).

Definition mkPosZero (z : mZ) : mZ :=
match z with
 | neg 0 => pos 0
 | _ => z 
end. 

Definition mkPosZeros (x : DerivedUnit) : DerivedUnit :=
match x with
 | derivedUnit a b c d e f g => 
    derivedUnit (mkPosZero a) (mkPosZero b) (mkPosZero c)
                (mkPosZero d) (mkPosZero e) (mkPosZero f)
                (mkPosZero g)
end.

Notation "x \ y" := (Div x y) (at level 60).
Notation "x ** y" := (Mult x y) (at level 60).


Definition mult_nat (x : mZ) (n : nat) : mZ :=
match x with
 | pos v => pos (v * n)
 | neg v => neg (v * n)
end. 

Fixpoint Pow_nat (du : DerivedUnit) (n : nat) : DerivedUnit :=
match du with
 | derivedUnit a b c d e f g => 
     derivedUnit (mult_nat a n) (mult_nat b n) (mult_nat c n)
                 (mult_nat d n) (mult_nat e n) (mult_nat f n)
                 (mult_nat g n)
  end.

Notation "x ^ y" := (Pow_nat x y).
Notation "x ^- y" := (Pow_nat (flipPowers x) y)  (at level 60).

Section PopularUnits. 
  Definition meter := mkUnit Meter. 
  Definition kelvin := mkUnit Kelvin.
  Definition second := mkUnit Second.
  Definition candela := mkUnit Candela.
  Definition amp := mkUnit Ampere.
  Definition kilogram := mkUnit KiloGram.
  Definition mole := mkUnit Mole.

  Definition Newton := (kilogram ** meter) \ (second^2).
  Definition Volt   := (kilogram ** (meter ^2)) \ ((second^3) ** amp).
  Definition Newton2 :=(Mult meter kilogram) \ (second^2).
  Definition VolumetricFlow := meter^3 \ second.
End PopularUnits.    
 Example Newtons_Same :  Newton = Newton2. 
 Proof. compute. reflexivity.
 Qed.
