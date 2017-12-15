Add LoadPath "/home/paul/Documents/TEEE/teee/Models/Measuring".
Add LoadPath "/Users/alex/Documents/Research/projects/brass15/teee/teee/Models/Measuring/cpdt/src" as Cpdt. 
Add LoadPath "/home/paul/Documents/TEEE/teee/Models/Measuring/cpdt/src" as Cpdt.
Add LoadPath "C:\Users\Paul\Documents\coqStuff\TEEE\teee\Models\Measuring\cpdt\src" as Cpdt. 
Require Import Units.
Require Import BareNecessities.
Require Import Nums.
Require Import String.
Module UnitEvalTypesM (nums : Nums). 

Definition N := nums.NumType. 


(**
For typed variables/values
*)

Inductive TYPE : Set := 
 | NUMERIC
 | BOOL
 | FUN.
Theorem eq_dec_TYPE : equality TYPE.
Proof. equal. Defined.

Inductive NumericValue : DerivedUnit -> Set :=
   | numericValue : forall u,  N -> NumericValue u.

Definition getValue {U} (V : NumericValue U) : N :=
match V with
 | numericValue _ v => v
end.

Inductive Value : TYPE -> DerivedUnit -> Set :=
 | valNum  : forall U, NumericValue U -> Value NUMERIC U
 | valBool : bool -> Value BOOL Void
 | valF : (N -> N) ->  Value FUN Void.


Inductive TVarID : TYPE -> DerivedUnit -> Set :=
 | vnat  : forall T U, nat -> TVarID T U
 | vString : forall T U, string -> TVarID T U
 | vReturn : forall T U, TVarID T U.
 
Theorem eq_dec_string : equality string. 
Proof. equal. Defined.
Hint Resolve eq_dec_string : autoEq.

Theorem eq_dec_VarId : forall T U, equality (TVarID T U). 
Proof. dep_equal.  (*  
 case_eq (eq_dec_string s s0). 
(* destruct m, m0; *) 
  repeat cbn_H;  
  try (solve [auto | jmeq | inversion_any | (subst; right; no) ]). 
 *)Defined.  

Theorem eq_dec_nat : equality nat. 
Proof. equal. Defined.

Definition VarF  := forall T U, TVarID T U -> option (Value T U). 
Print VarF.



Definition TYPEdenote (T : TYPE) : Set :=
match T with
 | NUMERIC => N
 | BOOL => bool
 | FUN => (N -> N)
end.


End UnitEvalTypesM.  
