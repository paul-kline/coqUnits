Add LoadPath "/Users/alex/Documents/Research/projects/brass15/teee/teee/Models/Measuring/cpdt/src" as Cpdt.
Add LoadPath "/home/paul/Documents/TEEE/teee/Models/Measuring/cpdt/src" as Cpdt.
Add LoadPath "C:\Users\Paul\Documents\coqStuff\TEEE\teee\Models\Measuring\cpdt\src" as Cpdt. 
Require Import Coq.Program.Equality.
Require Export Cpdt.CpdtTactics.

Definition xor (A : Prop) (B: Prop) := (A \/ B) /\ ~(A /\ B).


(** We define a short hand for equality
 *)
Definition equality (A :Type) := forall x y : A, {x = y} + {x <> y}.  
Hint Unfold equality : unfoldEq.


(** proof command that aids in simple proofs of equality.
 *)
Ltac equal := autounfold with unfoldEq; repeat decide equality.

(** 
Handy Ltac  for simplifying Hypothesis' since simpl doesn't do it.
Note: it will fail if the hypothesis doesn't change.
*)
Ltac simpl_H :=
 match goal with 
  [ H : ?T |- _] => progress (autounfold in H; (simpl in H))
  end.
Ltac cbn_H :=
 match goal with 
  [ H : ?T |- _] => progress (autounfold with * in H ; (cbn in H))
  end.
  
(** 
The actual command to use in proofs.
will continue to apply until it fails. 
*)
Tactic Notation "sh" := repeat simpl_H.
Tactic Notation "simplAll" := sh; autounfold; simpl.
Tactic Notation "refl" := reflexivity.
Tactic Notation "no" := (unfold not; let nm := fresh "H" in intro nm; inversion nm).

Ltac case_equals' name:= match goal with 
 [ x : ?T,
   y : ?T |- _] =>  assert ({x = y} + {x <> y}) as name; auto with *
 end. 
Tactic Notation "case_equals" := let name := fresh "equals" in case_equals' name. 
Tactic Notation "intro_equals" := intros; autounfold with unfoldEq; intros. 

 
Ltac jmeq := match goal with 
 [ H : ?T1 ~= ?T2 |- _] => apply JMeq_eq in H; auto
 end. 
Ltac jmeq_more := match goal with 
 [ jmeq : ?T1 ~= ?T2 |- {?x = ?T2} + {?x <> ?T2} ] => apply JMeq_eq in jmeq;auto
 end.
  
Ltac dep_equal := intro_equals;
match goal with 
 [ x : ?T,
   y : ?T |- {?x = ?y} + {?x <> ?y} ] => dep_destruct x; dep_destruct y;
   (try (let eqName := fresh "equals" in (case_equals' eqName; destruct eqName))) ;
   (solve  [(left; subst; auto)| right; no; auto]) + jmeq + idtac "jmeq tactic failed. Destruct so that your types match!"
    
 end. 
Ltac inversion_any' := match goal with 
[H : ?x = ?y |- _] => progress ( inversion H)
end.
Ltac inversion_any := solve [(repeat inversion_any')]. 
