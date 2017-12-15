Add LoadPath "/home/paul/Documents/TEEE/teee/Models/Measuring".
Add LoadPath "/Users/alex/Documents/Research/projects/brass15/teee/teee/Models/Measuring/cpdt/src" as Cpdt. 
Add LoadPath "/home/paul/Documents/TEEE/teee/Models/Measuring/cpdt/src" as Cpdt.

Require Import UnitsEvaluation.
Require Import Nums. 

Module natUnitEval := UnitsEval Nats.
Import natUnitEval. 
Require Import Units. 
Definition emptyVars : VarF.  unfold VarF. 
intros. exact None. 
Defined. 

Fixpoint add {U} (ls : list (NumericValue U)) : TypedCalculation U :=
match ls with
 | nil => 
 | cons x x0 => _
end

Fixpoint average' {U} (ls : list (NumericValue U)) (n :nat) : TypedCalculation U :=
match ls with
 | nil => 
 | cons x x0 => _
end.

Fixpoint average {U} (ls : list (NumericValue U)) : TypedCalculation U :=
match ls with
 | nil => _
 | cons x x0 => _
end
 
   

