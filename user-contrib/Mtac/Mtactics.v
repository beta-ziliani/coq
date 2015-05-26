Require Export mtac.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

Definition AssumptionNotFound {T} (x : T) : Exception. exact exception. Qed.
Program Definition assumption {P : Type} : M P :=
  hs <- hypotheses; 
  let f := mfix f (s : list Hyp) : M P :=
    mmatch s return M P with
    | [(x:P) t s'] (@ahyp P x t :: s') => ret x
    | [a s'] (a :: s') => f s'
    | _ => raise (AssumptionNotFound P)
    end
  in f hs.

Tactic Notation "rrun" open_constr(t) := (refine (run t)).

Example test_ass (P Q : Prop) (p:P) (q:Q) : P /\ Q.
  split; rrun assumption.
Qed.

Definition test_case := fun (G : Type) => run (constrs (list G)).
Print test_case.

(* Bad error messages *)
Fail Definition test_case' := run (constrs list).
(* Definition test_case' := run (constrs (le 0 0)). *)


Definition CantApply {T1 T2} (x:T1) (y:T2) : Exception. exact exception. Qed.
Program Definition apply {P T} (l : T) :=
  (mfix2 app (T : _) (l' : T) : M P :=
    mtry unify P T (fun a=>a) (fun _ => l')
    with NotUnifiableException =>
      mmatch T with
      | [T1 T2] (forall x:T1, T2 x) => [H]
          e <- evar T1;
          l' <- retS (eq_rect T _ l' (forall x1 : T1, T2 x1) H e);
          app (T2 e) l'
      | _ => raise (CantApply P l)
      end
    end) _ l.

Example test_apply (P Q : Prop) (p:P -> Q) (q:P) : Q.
  rrun (apply p).
  rrun assumption.
Qed.

Example test_badapply (P Q : Prop) (p:P -> Q) (q:P) : Q.
  Fail rrun (apply q).
Abort.

Program Definition eapply {P T} (l : T)  :=
  (mfix3 app (T : _) (l' : T) (es : list dyn) : M (P * list dyn)%type :=
    mtry unify P T (fun a=>(a*list dyn)%type) (fun _ => (l', es))
    with NotUnifiableException =>
      mmatch T with
      | [T1 T2] T1 -> T2 =m> [H]
          e <- evar T1;
          l' <- retS (eq_rect T _ l' (T1 -> T2) H e);
          app T2 l' (Dyn _ e :: es)
      | [T1 T2] (forall x:T1, T2 x) =m> [H]
          e <- evar T1;
          l' <- retS (eq_rect T _ l' (forall x1 : T1, T2 x1) H e);
          app (T2 e) l' es
      | _ => raise (CantApply P l)
      end
    end) _ l [].

Example test_eapply (P Q : Prop) (p: forall T1, T1 -> Q) (q:P) : Q.
  rrun (rs <- eapply p; ass <- retS (snd rs); print_term ass;; ret (fst rs)).
Abort.


Fixpoint try_all (t : forall T, T -> M unit)  ls :=
  match ls with
  | [] => ret tt
  | (Dyn _ e :: ls') => 
    b <- is_evar e; 
    if b then t _ e;; try_all t ls' else try_all t ls'
  end.

Definition eassumption' T (e:T) :=
  r <- @assumption T;
  mmatch r with e => ret tt | _ => raise exception end.

Example test_eapply (P Q : Prop) (p:P -> Q) (q:P) : Q.
  rrun (ps <- eapply p; (try_all eassumption' (snd ps));; ret (fst ps)).
Qed.


Definition try_once_each_constr {P} T (x : T) : M P :=
  cs <- constrs x;
  (fix f (cs : list dyn) :=
    match cs with
    | [] => evar _
    | (Dyn _ c :: cs') =>
      mtry 
        ps <- eapply c; 
        ass <- retS (rev (snd ps));
        try_all eassumption' ass;;
        ret (fst ps)
      with _ => f cs' end
    end) cs.

Definition MyException (x:nat) : Exception. exact exception. Qed.
Program Definition test_exception : M nat :=
  mtry
    e <- evar nat;
    raise (MyException e)
  with [e] MyException e =m> ret e
  end.

Check (run test_exception).

