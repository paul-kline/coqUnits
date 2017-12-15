Add LoadPath "/home/paul/Documents/TEEE/teee/Models/Measuring".
Add LoadPath "/Users/alex/Documents/Research/projects/brass15/teee/teee/Models/Measuring/cpdt/src" as Cpdt. 
Add LoadPath "/home/paul/Documents/TEEE/teee/Models/Measuring/cpdt/src" as Cpdt.
Add LoadPath "C:\Users\Paul\Documents\coqStuff\TEEE\teee\Models\Measuring\cpdt\src" as Cpdt. 
Add LoadPath "C:\Users\Paul\Documents\coqStuff\TEEE\teee\Models\Measuring ". 
Require Import Units.
Require Import Nums. 
Require Import UnitEvalTypes. 
Require Import BareNecessities.
 
Module UnitsEval (nums : Nums).
Definition N := nums.NumType.

 Module unitEvalTypes := UnitEvalTypesM nums.
 Export unitEvalTypes.


Definition combineValues {U1} {U2}
(combU : DerivedUnit -> DerivedUnit -> DerivedUnit)
(combV : N -> N -> N )
(V1 : NumericValue U1) (V2 : NumericValue U2) : NumericValue (combU U1 U2) :=
 numericValue (combU U1 U2) (combV (getValue V1) (getValue V2))
 .

Definition addValues {U} (r1 r2 : NumericValue U) 
   : NumericValue U.
exact (combineValues (fun _ _ => U) nums.add  r1 r2).
Defined.

Definition subValues {U} (r1 r2 : NumericValue U) 
   : NumericValue U.
exact (combineValues (fun _ _ => U) nums.minus  r1 r2).
Defined.

Definition multValues {U1} {U2} (v1 : NumericValue U1) (v2 : NumericValue U2) 
   : NumericValue (Mult U1 U2). 
exact (combineValues Mult nums.mult v1 v2).
Defined.

Definition divValues {U1} {U2} (v1 : NumericValue U1) (v2 : NumericValue U2) 
   : NumericValue (Div U1 U2). 
exact (combineValues Div nums.div v1 v2).
Defined.

(** 
An Inductive type specifically for numberic values
or variables. This is so TypedCalculation expressions can contain
constants or variables. With dependent types, it is easy to guarentee the
type of the variable by restricting ourselves to NUMERIC.
*)
Inductive NumTerm : DerivedUnit -> Set :=
 | numTermVar   {U}: TVarID NUMERIC U -> NumTerm U
 | numTermValue {U}: NumericValue U -> NumTerm U.

(**
Calculations can be (1)values (a value or variable, no expression),
(1) an addition, (2) a subtraction, (3) a multiplication, (4) or a division.

Addition & subtraction can only be performed on numbers of the same units.

'Mult' & 'Div' are type level (used here) functions which combine the 
units of the subterms accordingly.Power is not a constructor here due to the
complexities introduced. For integer powers, repeated multiplaction will do
your trick. For non-integer powers, this involese square roots which change
our units to potentially non-integer values, which doesn't really make sense,
nor is it currently representable. Perhaps, if needed later, square roots can be
added with the additional check that the units work out to integer values. i.e.
taking the square root of meters^2 is okay. 
*) 

Inductive TypedCalculation : DerivedUnit -> Set := 
 | TcalcValue {U} : NumTerm U -> TypedCalculation U
 | TcalcAdd   {U}  : TypedCalculation U -> 
                     TypedCalculation U ->  
                     TypedCalculation U
 | TcalcSubtract {U}:TypedCalculation U -> 
                     TypedCalculation U ->  
                     TypedCalculation U
 | TcalcMult {U1} {U2}:  TypedCalculation U1 -> 
                         TypedCalculation U2 -> 
                         TypedCalculation (Mult U1 U2)
 | TcalcDiv {U1} {U2} : 
     TypedCalculation U1 -> 
     TypedCalculation U2 -> 
     TypedCalculation (Div U1 U2).

Notation "x +C+ y" := (TcalcAdd x y) (at level 60). 
Notation "x -C- y" := (TcalcSubtract x y) (at level 60).
Notation "x *C* y" := (TcalcMult x y) (at level 60).
Notation "x /C/ y" := (TcalcDiv x y) (at level 60).

Fixpoint mkAdd' {U} (ls : list (NumericValue U)) : TypedCalculation U :=
match ls with
 | nil => TcalcValue (numTermValue (numericValue U (nums.natToNum 0)))
 | cons t ls' => TcalcAdd (TcalcValue (numTermValue t)) (mkAdd' ls')
end
. 

Fixpoint mkAdd {U} (ls : list (NumTerm U)) : TypedCalculation U :=
match ls with
 | nil => TcalcValue (numTermValue (numericValue U (nums.natToNum 0)))
 | cons t ls' => TcalcAdd (TcalcValue t) (mkAdd ls')
end
.

Theorem thm_definedp0 : forall n : nat, n = n + 0. 
Proof. induction n.  reflexivity. 
simpl. rewrite <- IHn. reflexivity. 
Defined.

Lemma thm_zAddZero : forall z : mZ, zadd z (pos 0) = z. 
Proof. intros. destruct z.  simpl. cbn. rewrite <-thm_definedp0. auto. 
cbn.
destruct n. simpl. rewrite posNegZero. auto. 
simpl.  auto. 
Defined.

Theorem thm_multVoid : forall U : DerivedUnit, U = U ** Void. 
Proof.  intros. simpl. unfold Mult. destruct U. simpl. repeat rewrite thm_zAddZero. auto. 
Defined.  

Theorem thm_divVoid : forall U : DerivedUnit, U = U \ Void. 
Proof. intros. unfold Div . simpl. repeat rewrite posNegZero. 
apply thm_multVoid. 
Defined.

Definition mkAverage' {U} (ls : list (NumericValue U)) : TypedCalculation U.
pose(t := (mkAdd' ls)).
pose (count := (@TcalcValue Void (numTermValue (numericValue Void (nums.natToNum (length ls)))) )). rewrite thm_divVoid. 
exact (TcalcDiv t count).
Defined. 

Definition mkAverage {U} (ls : list (NumTerm U)) : TypedCalculation U.
pose(t := (mkAdd ls)).
pose (count := (@TcalcValue Void (numTermValue (numericValue Void (nums.natToNum (length ls)))) )). rewrite thm_divVoid. 
exact (TcalcDiv t count).
Defined.

Definition natToNumTerm (U : DerivedUnit) (n : nat) : NumTerm U :=
numTermValue (numericValue U (nums.natToNum n)).
 
 Definition numsls1 := cons (natToNumTerm Void 1) (cons (natToNumTerm Void 2) (cons (natToNumTerm Void 3) nil)).
  
Example average1 : TypedCalculation Void :=
 mkAverage numsls1.
 
 Print average1.   
 Eval cbv in average1.



(**
The function used to store our variable state.
Each access it must be given the type as well.
For implementation, this may need to change.
*)

Fixpoint ArePresent {U} (expr : TypedCalculation U) (vf : VarF) : Prop :=
match expr with
 | @TcalcValue U nt => match nt with
       | @numTermVar U x => match (vf NUMERIC U x ) with 
                            | None => False
                            | Some _ => True
                           end
       | @numTermValue U x => True
      end
 | @TcalcAdd U t1 t2 => and (ArePresent t1 vf) (ArePresent t2 vf)
 | @TcalcSubtract U t1 t2 => and (ArePresent t1 vf) (ArePresent t2 vf)
 | @TcalcMult U1 U2 t1 t2 => and (ArePresent t1 vf) (ArePresent t2 vf)
 | @TcalcDiv U1 U2 t1 t2 => and (ArePresent t1 vf) (ArePresent t2 vf)
 end.

Inductive ArePresentI : forall U,  TypedCalculation U -> VarF -> Prop :=
 | arePresentValueValue : forall U val vf, 
      ArePresentI U (@TcalcValue U (@numTermValue U val)) vf
 | arePresentValueVar : forall U var vf val, 
        vf NUMERIC U var = Some val -> 
        ArePresentI U (@TcalcValue U (@numTermVar U var)) vf  
 |arePresentTcalcAdd : forall U t1 t2 vf, ArePresentI U t1 vf -> 
   ArePresentI U t2 vf -> 
   ArePresentI U (TcalcAdd t1 t2) vf
 | arePresentTcalcSubtract : forall U t1 t2 vf, ArePresentI U t1 vf -> 
   ArePresentI U t2 vf -> 
   ArePresentI U (TcalcSubtract t1 t2) vf
 | arePresentTcalcMult : forall U1 U2, 
     forall (t1 : TypedCalculation U1) (t2 : TypedCalculation U2) vf,
     ArePresentI U1 t1 vf -> 
     ArePresentI U2 t2 vf -> 
     ArePresentI (U1 ** U2) (TcalcMult t1 t2) vf
 | arePresentTcalcDiv : forall U1 U2, 
     forall (t1 : TypedCalculation U1) (t2 : TypedCalculation U2) vf,
     ArePresentI U1 t1 vf -> 
     ArePresentI U2 t2 vf -> 
     ArePresentI (U1 \ U2) (TcalcDiv t1 t2) vf.
Hint Constructors ArePresentI.

Require Import Coq.Logic.Eqdep_dec. 
Theorem thm_ArePresentEquivalence : 
 forall U, forall (t : TypedCalculation U) vf, 
  ArePresent t vf <-> ArePresentI U t vf.
Proof. split. intros. induction t; intros.
intros. destruct n eqn:hh. simpl in H. destruct (vf NUMERIC U t) eqn:hhh.
eapply arePresentValueVar.  rewrite hhh.  auto. elim H. 
constructor.
intros. constructor. inversion H. apply IHt1.  auto. 
apply IHt2. inversion H. auto.

constructor. inversion H. apply IHt1.  auto. 
apply IHt2. inversion H. auto.  

constructor. inversion H. apply IHt1.  auto. 
apply IHt2. inversion H. auto.

constructor. inversion H. apply IHt1.  auto. 
apply IHt2. inversion H. auto.
(* other case *)
intros.  induction t. destruct n eqn:hh. simpl. intros. 
inversion H.  subst. apply inj_pair2_eq_dec in H0. subst.
 destruct (vf NUMERIC U t) eqn:hhh. auto. 
 inversion H2. apply inj_pair2_eq_dec in H0. subst. 
 intros.  apply eq_dec_DerivedUnit.
 intros.  apply eq_dec_DerivedUnit.
 simpl; auto. 
 simpl. intros. inversion H. subst. apply inj_pair2_eq_dec in H0.
 apply inj_pair2_eq_dec in H1. subst.  split. auto. auto. 
 apply eq_dec_DerivedUnit. apply eq_dec_DerivedUnit. 
 
 intros. inversion H. subst. apply inj_pair2_eq_dec in H0.
 apply inj_pair2_eq_dec in H1. subst.  split. auto. auto. 
 apply eq_dec_DerivedUnit. apply eq_dec_DerivedUnit.
 
 intros. inversion H. subst. apply inj_pair2_eq_dec in H5.
 apply inj_pair2_eq_dec in H6. subst.  split. auto. auto. 
 apply eq_dec_DerivedUnit. apply eq_dec_DerivedUnit.
 
 intros. inversion H. subst. apply inj_pair2_eq_dec in H5.
 apply inj_pair2_eq_dec in H6. subst.  split. auto. auto. 
 apply eq_dec_DerivedUnit. apply eq_dec_DerivedUnit.
 Qed.

(* bug: if you switch vf and expr in argument order, coq says can't define fixpoint. *)
Fixpoint typedCalcEval {U} (vf : VarF) (expr : TypedCalculation U)  : (ArePresent expr vf) -> (NumericValue U).
intros. 
destruct expr eqn:hh.
destruct n  eqn:hhh.
simpl in H. destruct (vf NUMERIC U t) eqn:hhhh.
dep_destruct v. 
exact n0.
exfalso; auto.
exact n0. 
simpl in H. destruct H.
pose proof (typedCalcEval U vf t1 H) as x1.
pose proof (typedCalcEval U vf t2 H0) as x2.
exact (addValues x1 x2).
(*sub case *)
simpl in H. destruct H.
pose proof (typedCalcEval U vf t1 H) as x1.
pose proof (typedCalcEval U vf t2 H0) as x2.
exact (subValues x1 x2).
(*mult case *)
simpl in H. destruct H.
pose proof (typedCalcEval U1 vf t1 H) as x1.
pose proof (typedCalcEval U2 vf t2 H0) as x2.
exact (multValues x1 x2).
(* div case *)
simpl in H. destruct H.
pose proof (typedCalcEval U1 vf t1 H) as x1.
pose proof (typedCalcEval U2 vf t2 H0) as x2.
exact (divValues x1 x2).
Defined. 
(* couldn't use this because coq is too dumb to know that the current term is the destructed expr *)

(* same definition bug as above *)
Fixpoint typedCalcEvalO {U} (vf : VarF) (expr : TypedCalculation U)  : option (NumericValue U).
intros. 
destruct expr eqn:hh.
destruct n  eqn:hhh.
destruct (vf NUMERIC U t) eqn:hhhh.
dep_destruct v. 
exact (Some n0).
exact None. 
exact (Some n0). 

pose proof (typedCalcEvalO U vf t1) as x1.
pose proof (typedCalcEvalO U vf t2) as x2.
destruct x1 eqn:h. destruct x2 eqn:hhh. exact (Some (addValues n n0)).
exact None. exact None. 

(*sub case *)
pose proof (typedCalcEvalO U vf t1) as x1.
pose proof (typedCalcEvalO U vf t2) as x2.
destruct x1 eqn:h. destruct x2 eqn:hhh. exact (Some (subValues n n0)).
exact None. exact None. 

(*mult case *)
pose proof (typedCalcEvalO U1 vf t1) as x1.
pose proof (typedCalcEvalO U2 vf t2) as x2.
destruct x1 eqn:h. destruct x2 eqn:hhh. exact (Some (multValues n n0)).
exact None. exact None. 

(* div case *)
pose proof (typedCalcEvalO U1 vf t1) as x1.
pose proof (typedCalcEvalO U2 vf t2) as x2.
destruct x1 eqn:h. destruct x2 eqn:hhh. exact (Some (divValues n n0)).
exact None. exact None. 
Defined.
 
(* couldn't use this because coq is too dumb to know that the current term is the destructed expr *)

 
(*
 refine (fun p => 
match expr as xx with
 | @TcalcValue U t => _ (* match t with
      | @numTermVar U x => _
      | @numTermValue U x => x
end *)

 | @TcalcAdd U t1 t2 => addValues  (typedCalcEval U t1 st _) (typedCalcEval U t2 st _)
 | @TcalcSubtract U t1 t2 => subValues (typedCalcEval U t1 st _) (typedCalcEval U t2 st _)
 | @TcalcMult U1 U2 t1 t2 => multValues (typedCalcEval U1 t1 st _) (typedCalcEval U2 t2 st _)
 | @TcalcDiv U1 U2 t1 t2 => divValues (typedCalcEval U1 t1 st _) (typedCalcEval U2 t2 st _)
end).
destruct t eqn:hh. induction expr.  
 *)

Inductive EvalTypedCalcR : forall U, TypedCalculation U -> VarF -> NumericValue U -> Prop:=
 | eval_TcalcValueValue : forall U, forall (nm : NumericValue U) vf,
     EvalTypedCalcR U (TcalcValue (numTermValue nm)) vf nm
 | eval_TcalcValueVar : forall U, forall (tvar : TVarID NUMERIC U) vf val,
     vf NUMERIC U tvar = Some (valNum U val) ->
     EvalTypedCalcR U (TcalcValue (numTermVar tvar)) vf val
 | eval_TcalcAdd : forall U t1 v1 t2 v2 vf,
     EvalTypedCalcR U t1 vf v1 -> 
     EvalTypedCalcR U t2 vf v2 ->
     EvalTypedCalcR U (TcalcAdd t1 t2) vf (addValues v1 v2) 
 | eval_TcalcSub : forall U t1 v1 t2 v2 vf,
     EvalTypedCalcR U t1 vf v1 -> 
     EvalTypedCalcR U t2 vf v2 ->
     EvalTypedCalcR U (TcalcSubtract t1 t2) vf (subValues v1 v2)
 | eval_TcalcMult : forall U1 U2 t1 t2 v1 v2 vf, 
     EvalTypedCalcR U1 t1 vf v1 -> 
     EvalTypedCalcR U2 t2 vf v2 ->
     EvalTypedCalcR (U1 ** U2) (TcalcMult t1 t2) vf (multValues v1 v2)
 | eval_TcalcDiv : forall U1 U2 t1 t2 v1 v2 vf, 
     EvalTypedCalcR U1 t1 vf v1 -> 
     EvalTypedCalcR U2 t2 vf v2 ->
     EvalTypedCalcR (U1 \ U2) (TcalcDiv t1 t2) vf (divValues v1 v2).
Hint Constructors EvalTypedCalcR. 

Theorem thm_isPresent : forall U t vf,
ArePresentI U (TcalcValue (numTermVar t)) vf -> exists val,
  vf NUMERIC U t = Some val.
Proof. 
intros. 
inversion H. subst. apply inj_pair2_eq_dec in H0. subst. eauto. 
apply eq_dec_DerivedUnit. 
Defined.

Require Import Coq.Program.Equality.
Set Printing All. 
Theorem thm_TypedEvalEquivalence : forall U vf term val, EvalTypedCalcR U term vf val -> (typedCalcEvalO vf term) = Some val.
Proof. intros.
einduction H. simpl.  auto. 
simpl.
Admitted. 
Theorem thm_TypedEvalEquivalence2 : forall U vf term val, (typedCalcEvalO vf term) = Some val -> EvalTypedCalcR U term vf val .
Proof.
Admitted. 
(*
Fixpoint typedCalcEval2 {U} (expr : TypedCalculation U) (st : State) : (ArePresentI U expr st) -> (NumericValue U).
intros.
destruct expr.
destruct n.
destruct st.   
destruct H.  
destruct expr eqn:e.
destruct n eqn:nn.
apply thm_isPresent in H. 
inversion H. 
cbn in H. 
inversion H. 
simpl in H.   *)
(*
Theorem thm_typedEvalEquivalence : forall U t st p,
EvalTypedCalcR U t st (typedCalcEval t st p).
intros. 
dep_destruct t. 
dep_destruct n.
specialize thm_ArePresentEquivalence. intros.
edestruct H.
*)

Definition emptyVarF : VarF. unfold VarF.  intros.  exact None. 
Defined. 
 Eval compute in typedCalcEvalO emptyVarF average1.



End UnitsEval.   