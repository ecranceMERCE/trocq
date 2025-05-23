From Trocq Require Import Trocq.
From mathcomp Require Import all_ssreflect zify lra.
From monae Require Import preamble hierarchy monad_lib monad_model.

Set Implicit Arguments.

Local Open Scope do_notation.
Local Open Scope monae_scope.

Section with_cache.
Variable res : eqType.
Definition cache := nat -> option res.
Variable M : stateRunMonad cache idfun.
Variable f : nat -> res.

Definition update n v : M unit :=
  do c <- get; let c' x := if x == n then Some v else c x in put c'.

Definition lookup_or_compute n (m : M res) :=
  do c <- get;
  if c n is Some x then Ret x else
  do x <- m; do _ <- update n x; Ret x.

Definition goodcache (c : cache) :=
  forall n, if c n is Some x then x == f n else true.

Require Import EqdepFacts.

Definition R {X} (s : M X) (n : (idfun : monad) X) : Type :=
  forall c, goodcache c ->
            (runStateT s c).1 = n /\ goodcache (runStateT s c).2.

(*
Lemma Rget : R get ?.
Proof.
move=> c Hc.
by rewrite runStateTget.
Qed.
*)

Lemma Rret A (a : A) : R (Ret a) a.
Proof.
move=> c Hc.
by rewrite runStateTret.
Qed.

Lemma Rupdate k : R (update k (f k)) tt.
Proof.
move=> c Hc.
rewrite /update runStateTbind runStateTget bindretf runStateTput /=.
split => // x.
by case: ifPn (Hc x) => [/eqP ->|].
Qed.

Lemma Rbind A B (m : M A) m' :
  R m m' -> forall (g : A -> M B) g',
      (R (g m') (g' m')) ->
      R (m >>= g) (m' >>= g').
Proof.
move=> Rmm' g g' Rgg' c Hc.
rewrite runStateTbind.
case: (Rmm' _ Hc).
case: (runStateT m c) => n2 c2 /= -> Hc2.
rewrite bindretf /=.
by case: (Rgg' _ Hc2) => ->.
Qed.

Lemma Rlookup_or_compute n (m : M res) :
  R m (f n) ->
  R (lookup_or_compute n m) (f n).
Proof.
rewrite /lookup_or_compute => Rmm' /= c Hc.
rewrite runStateTbind runStateTget bindretf /=.
case: (c n) (Hc n) => [a /eqP -> | _].
  by rewrite runStateTret.
move: c Hc; rewrite -/(R _ _).
have -> : f n = Ret (f n) >>= fun x => Ret tt >> Ret x
        :> (idfun : monad) _ by rewrite bindretf.
exact/(Rbind Rmm')/Rbind/Rret/Rupdate.
Qed.
End with_cache.

From elpi Require Import elpi.
From Trocq Require Import Param.

From Trocq.Elpi Extra Dependency "util-rocq.elpi" as util_rocq.
From Trocq.Elpi Extra Dependency "annot.elpi" as annot.
From Trocq.Elpi Extra Dependency "param-class-util.elpi" as param_class_util.
From Trocq.Elpi.constraints Extra Dependency "simple-graph.elpi" as simple_graph.
From Trocq.Elpi.constraints Extra Dependency "constraint-graph.elpi" as constraint_graph.
From Trocq.Elpi.constraints Extra Dependency "constraints.elpi" as constraints.
From Trocq.Elpi Extra Dependency "vernac.elpi" as vernac.

Section fibo_with_cache.
Variable M : stateRunMonad (cache nat) idfun.

Fixpoint fibo n :=
  match n with
  | 0 => 0
  | 0.+1 => 0.+1
  | (m.+1 as n).+1 => fibo m + fibo n
  end.

Fixpoint fibo_memo n : M nat :=
  lookup_or_compute M n
    match n with
    | 0 => Ret 0
    | (0 as n).+1 =>
        (* need a recursive call to ensure fibo 0 is in the cache for fibo 1 *)
        do _ <- fibo_memo n;
        Ret 0.+1
    | (m.+1 as n).+1 =>
        do x <- fibo_memo m;
        do y <- fibo_memo n;
        Ret (x+y)
    end.

End fibo_with_cache.

Elpi Command CustomTrocq.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File util_rocq.
Elpi Accumulate File annot.
Elpi Accumulate File param_class_util.
Elpi Accumulate File simple_graph.
Elpi Accumulate File constraint_graph.
Elpi Accumulate File constraints.
Elpi Accumulate File vernac.
Elpi Query lp:"
  param {{fibo_memo}} X Y Z.
".


Lemma fibo_memo_ok : forall M n, R M fibo (fibo_memo n) (fibo n).
Proof.
elim/ltn_ind => -[|n] IH;
rewrite [fibo_memo _]/=;
apply: Rlookup_or_compute.
  exact: Rret.
case: n IH => [|n] IH.
  have -> : fibo 1 = Ret 0 >> Ret (fibo 1) :> (idfun : monad) _ by [].
  exact/Rbind/Rret/IH.
have -> : fibo n.+2 = Ret (fibo n) >> (Ret (fibo n.+1) >> Ret (fibo n.+2))
        :> (idfun : monad) nat by [].
apply/Rbind/Rbind/Rret/IH => //.
exact: IH.
Qed.

Fixpoint fibo' n :=
  match n with
  | 0 => (0, 0.+1)
  | m.+1 => let (a,b) := fibo' m in (b, a+b)
  end.
End fibo_with_cache.
