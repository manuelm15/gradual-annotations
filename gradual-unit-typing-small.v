Require Export SfLib.
Require Export QArith_base.
Require Export Coq.Logic.FunctionalExtensionality.

(* in this context, graduality (with a reasonable progress property) can be achieved
   by having exact typing rules for primitive operations and the condition of the
   conditional - they don't accept argument with dynamic annotations. This is no
   restriction because each of them can be protected with a suitable cast.
   Well, it may be a restriction for primops nevertheless because they might be
   used polymorphically if admitted on dynamically annotated arguments.
   But with that option, each primop may fail - not much of a progress property.
   *)

Inductive op : Set :=
| add : op
| sub : op
| mul : op
| div : op
.

Lemma op_eq_dec : forall o1 o2 : op, {o1 = o2} + { o1 <> o2 }.
Proof.
  decide equality.
Qed.

(* Operations on integers Q*)
Definition op_int (o : op) : Q -> Q -> Q :=
  match o with
  | add => Qplus
  | sub => Qminus
  | mul => Qmult
  | div => Qdiv
  end.

(* the annotation algebra might (usually) have laws *)
Inductive ann : Set :=		(* annotation algebra - should this be a logic? *)
| anon : ann 			(* neutral element - no annotation *)
| acst : id -> ann                (* annoted id *)
| aprm : op -> ann -> ann -> ann  (* operation on annotation*)
.

Lemma Id_eq_dec : forall x y : id, {x=y} + {x<>y} .
Proof.
  decide equality.
  decide equality.
Qed.

Lemma ann_eq_dec : forall x y : ann, {x=y} + {x<>y} .
Proof.
  decide equality.
  apply Id_eq_dec.
  apply op_eq_dec.
Qed.

(* value annotations: static and dynamic annotations *)
Inductive vann : Set :=
| vs : ann -> vann
| vd : ann -> vann.

Lemma vann_eq_dec : forall x y : vann, {x=y} + {x<>y} .
Proof.
  decide equality;
  apply ann_eq_dec.
Qed.

(* the type annotation algebra extends annotations with a single dynamic annotation *)
Inductive tyann : Set :=
| taann : ann -> tyann (*static type annotation*)
| tadyn : tyann  (*dynamic annotation*)
.


(* relation for cast-related subtyping *)
Inductive tyann_le : tyann -> tyann -> Prop :=
| tyann_le_eq : forall tya,
  tyann_le tya tya (* all type annotations ta le ta *)
| tyann_le_dyn : forall tya,
  tyann_le tya tadyn (* all type annotation ta le tadynn*)
.

Definition an_int (o:op) (a1:ann) (a2:ann) :=
  aprm o a1 a2.

(* if we use operations on annotations ... *)
Inductive an_rel: op -> ann -> ann -> ann -> Prop :=
| an_add : forall a,
  an_rel add a a a (* a + a = a*)
| an_sub : forall a,
  an_rel sub a a a (* a - a = a*)
| an_mul : forall a1 a2,
  an_rel mul a1 a2 (an_int mul a1 a2)  (* use annotation algebra for integers*)
| an_div : forall a1 a2,
  an_rel div a1 a2 (an_int div a1 a2). (* use annotation algebra for integers*)

(* what we don't get when we apply operations on annotations*)
(* complement of an_rel, this will be shown in the following...*)
Inductive nan_rel: op -> ann -> ann -> ann -> Prop :=
| nan_add : forall a1 a2 a3,
  (a1 <> a3 \/ a2 <> a3) ->
  nan_rel add a1 a2 a3 (* if not a1 = a2 = a3, then not a1 + a2 = a3*)
| nan_sub : forall a1 a2 a3,
  (a1 <> a3 \/ a2 <> a3) ->
  nan_rel sub a1 a2 a3 (* if not a1 = a2 = a3, then not a1 - a2 = a3*)
| nan_mul : forall a1 a2 a3,
  an_int mul a1 a2 <> a3 ->
  nan_rel mul a1 a2 a3 (* mul a1 a2 doesn't yield a3 according to annotiation algebra*)
| nan_div : forall a1 a2 a3,
  an_int div a1 a2 <> a3 ->
  nan_rel div a1 a2 a3.

(* for a qaudruple of operation and three annotations o a1 a2 a3,
 o a1 a2 cannot at the same time yield a3 and not yield a3*)
Lemma not_an_and_nan : forall o a1 a2 a3,
  ~ (an_rel o a1 a2 a3 /\ nan_rel o a1 a2 a3).
Proof.
  intros.
  intro.
  inversion H.
  induction H0; inversion H1; subst.
  destruct H0;
  unfold not in H0; apply H0;
  reflexivity.
  destruct H0; unfold not in H0; apply H0; reflexivity.
  unfold not in H0; apply H0; reflexivity.
  unfold not in H0; apply H0; reflexivity.
Qed.  

(*tuple in an_rel -> tuple not in an_not_nan*)
Lemma an_not_nan : forall o a1 a2 a3,
  an_rel o a1 a2 a3 -> ~ nan_rel o a1 a2 a3.
Proof.
  intros. intro.
  induction H; inversion H0; unfold not in H.
  destruct H; apply H; reflexivity.
  destruct H; apply H; reflexivity.
  apply H; reflexivity.
  apply H; reflexivity.
Qed.


(* tuple in nan_rel -> not in an_rel*)
Lemma nan_not_an : forall o a1 a2 a3,
  nan_rel o a1 a2 a3 -> ~ an_rel o a1 a2 a3.
Proof.
  intros. intro.
  induction H; inversion H0; subst; unfold not in H.
  destruct H; apply H; reflexivity.
  destruct H; apply H; reflexivity.
  apply H; reflexivity.
  apply H; reflexivity.
Qed.

(* all tuples are in an_rel or in nan_rel *)
Lemma an_or_nan : forall o a1 a2 a3,
  an_rel o a1 a2 a3 \/ nan_rel o a1 a2 a3.
Proof.
  intros.
  destruct o.
  Case "add". (*add*)
  pose (ann_eq_dec a1 a3) as a1a3.
  pose (ann_eq_dec a2 a3) as a2a3.
  destruct a1a3. destruct a2a3.
  left. subst. constructor.
  right. constructor. right. assumption.
  right. constructor. left. assumption.
  Case "sub". (*sub*)
  pose (ann_eq_dec a1 a3) as a1a3.
  pose (ann_eq_dec a2 a3) as a2a3.
  destruct a1a3. destruct a2a3.
  left. subst. constructor.
  right. constructor. right. assumption.
  right. constructor. left. assumption.
  Case "mul". (*mul*)
  pose (ann_eq_dec (an_int mul a1 a2) a3).
  destruct s.
  subst. left. constructor.
  right. constructor. assumption.
  Case "div". (*div*)
  pose (ann_eq_dec (an_int div a1 a2) a3).
  destruct s.
  subst. left. constructor.
  right. constructor. assumption.
Qed.

(*for all operations o applied to two annotations a1 a2,
 there exists an a3 such that either o a1 a2 a3 is either in an_rel or nan_rel.*)
Lemma exists_an_or_nan : forall o a1 a2,
  exists a3, an_rel o a1 a2 a3 \/ nan_rel o a1 a2 a3.
Proof.
  intros.
  destruct o.
  Case "add".
  pose (ann_eq_dec a1 a2).
  destruct s.
  SCase "a1=a2".
    exists a1.
    left. subst. constructor.
  SCase "a1 <> a2".
    exists a2. right. constructor. left. assumption.
  
  Case "sub".
  pose (ann_eq_dec a1 a2).
  destruct s.
  SCase "a1=a2".
    exists a1.
    left. subst. constructor.
  SCase "a1 <> a2".
    exists a2. right. constructor. left. assumption.
  
  Case "mul".
    exists (aprm mul a1 a2). left. constructor.
  Case "div".
    exists (aprm div a1 a2). left. constructor.
Qed.


(* relation for value annotations, lifted from an_rel *)
Inductive van_rel (o:op) : vann -> vann -> vann -> Prop :=
| vr_static : forall a1 a2 a,
  an_rel o a1 a2 a ->
  van_rel o (vs a1) (vs a2) (vs a)
| vr_dynamic : forall a1 a2 a,
  an_rel o a1 a2 a ->
  van_rel o (vd a1) (vd a2) (vd a).

(* relation for type annotations, lifted from an_rel *)
Inductive taan_rel : op -> tyann -> tyann -> tyann -> Prop :=
| taan_rel_dyn : forall o,
  taan_rel o tadyn tadyn tadyn
| taan_rel_stat : forall o a1 a2 a,
  an_rel o a1 a2 a ->
  taan_rel o (taann a1) (taann a2) (taann a)
.
(* an_rel is a function, this means:
  forall o, a1, a2 there is at most one a such that an_rel o a1 a2 a*)
Lemma an_rel_function : forall o a1 a2 a a',
  an_rel o a1 a2 a ->
  an_rel o a1 a2 a' ->
  a = a'.
Proof.
  intros.
  destruct o;
  inversion H;
  inversion H0; subst.
  assumption.
  assumption.
  reflexivity.
  reflexivity.
Qed.

(* the set of all types *)
Inductive typ : Set :=
| tann : rtyp -> tyann -> typ (*an annotated base-type is a type*)
| tfun : typ -> typ -> typ (*a function type is a type*)
| tprod : typ -> typ -> typ (*a product type is a type*)
with rtyp : Set :=
| tnum : rtyp
.

(* two type annotations are compatible if...*)
Inductive ann_compatible : tyann -> tyann -> Prop :=
| ac_equ : forall a,
  ann_compatible (taann a) (taann a) (* they are equal*)
| ac_dyn_left : forall a,
  ann_compatible tadyn (taann a) (* forall a, a~?*)
| ac_dyn_right : forall a,
  ann_compatible (taann a) tadyn (* for all a, ? ~ a*)
| ac_dyn_both :
  ann_compatible tadyn tadyn. (* for all a, a ~ ?*)

(* compatible types...*)
Inductive compatible : typ -> typ -> Prop :=
| c_num : forall ta1 ta2,
  ann_compatible ta1 ta2 ->
  compatible (tann tnum ta1) (tann tnum ta2)
| c_fun : forall t1a t1b t2a t2b,
  compatible t1b t1a ->
  compatible t2a t2b ->
  compatible (tfun t1a t2a) (tfun t1b t2b)
| c_prod : forall t1a t1b t2a t2b,
  compatible t1a t1b ->
  compatible t2a t2b ->
  compatible (tprod t1a t2a) (tprod t1b t2b)
.

Inductive blame : Set :=
| pos_blame : blame
| neg_blame : blame
.

Definition flip (p:blame) :=
  match p with
    | pos_blame => neg_blame
    | neg_blame => pos_blame
  end.

Inductive exp : Set :=
| evar : id -> exp
| eapp : exp -> exp -> exp
| ecst : Q -> vann -> exp
| elam : id -> exp -> exp
| eprm : op -> exp -> exp -> exp
| ecnd : exp -> exp -> exp -> exp
| ecast : exp -> typ -> typ -> blame -> exp
.

Fixpoint ssubst (e1:exp) (i:id) (e2:exp) :=
  match e1 with
    | evar j => if beq_id i j then e2 else evar j
    | eapp e1' e2' => eapp (ssubst e1' i e2) (ssubst e2' i e2)
    | ecst q a => ecst q a
    | elam j e' => if beq_id i j then elam j e' else elam j (ssubst e' i e2)
    | eprm o e1' e2' => eprm o (ssubst e1' i e2) (ssubst e2' i e2)
    | ecnd e1' e2' e3' => ecnd (ssubst e1' i e2) (ssubst e2' i e2) (ssubst e3' i e2)
    | ecast e' t1 t2 p => ecast (ssubst e' i e2) t1 t2 p
  end.

Inductive value : exp -> Prop :=
| val_cst : forall n a,
  value (ecst n a)
| val_lam : forall i e,
  value (elam i e).

Inductive vann_compatible (a:ann) : vann -> Prop :=
| vcs : 
  vann_compatible a (vs a)
| vcd :
  vann_compatible a (vd a).

Inductive vtann_compatible (a:ann) : vann -> tyann -> Prop :=
| vtcs : 
  vtann_compatible a (vs a) (taann a)
| vtcd :
  vtann_compatible a (vd a) tadyn.

Inductive vtann_compatible2 : vann -> tyann -> Prop :=
| vtcs2 : forall a,
  vtann_compatible2 (vs a) (taann a)
| vtcd2 : forall a,
  vtann_compatible2 (vd a) tadyn.

Inductive vcast : exp -> typ -> typ -> exp -> blame -> Prop :=
| vc_num : forall n a va1 va2 ta1 ta2 p,
  vtann_compatible a va1 ta1 ->
  vtann_compatible a va2 ta2 ->
  vcast (ecst n va1) (tann tnum ta1) (tann tnum ta2) (ecst n va2) p
| vc_lam : forall i e t1a t1b t2a t2b p,
  vcast
  (elam i e)
  (tfun t1a t1b)
  (tfun t2a t2b)
  (elam i (eapp (elam i (ecast e t1b t2b p)) (ecast (evar i) t2a t1a (flip p))))
  p.

Inductive smallstep : exp -> exp -> Prop :=
| ss_beta : forall i e1 e2,
  value e2 ->
  smallstep (eapp (elam i e1) e2) (ssubst e1 i e2)
| ss_prim : forall o n1 n2 a1 a2 a,
  van_rel o a1 a2 a ->
  smallstep (eprm o (ecst n1 a1) (ecst n2 a2)) (ecst (op_int o n1 n2) a)
| ss_true : forall n1 e2 e3 va,
  ~ (n1 == 0) ->
  vann_compatible anon va ->
  smallstep (ecnd (ecst n1 va) e2 e3) e2
| ss_fals : forall n1 e2 e3 va,
  n1 == 0 ->
  vann_compatible anon va ->
  smallstep (ecnd (ecst n1 va) e2 e3) e3
| ss_cast : forall e t1 t2 v p,
  value e ->
  vcast e t1 t2 v p ->
  smallstep (ecast e t1 t2 p) v
| ss_ctx1 : forall e1 e1' e2,
  smallstep e1 e1' ->
  smallstep (eapp e1 e2) (eapp e1' e2)
| ss_ctx11 : forall i e1 e2 e2',
  smallstep e2 e2' ->
  smallstep (eapp (elam i e1) e2) (eapp (elam i e1) e2')
| ss_ctx2 : forall o e1 e1' e2,
  smallstep e1 e1' ->
  smallstep (eprm o e1 e2) (eprm o e1' e2)
| ss_ctx3 : forall o n1 a1 e2 e2',
  smallstep e2 e2' ->
  smallstep (eprm o (ecst n1 a1) e2) (eprm o (ecst n1 a1) e2')
| ss_ctx4 : forall e1 e2 e3 e1',
  smallstep e1 e1' ->
  smallstep (ecnd e1 e2 e3) (ecnd e1' e2 e3)
| ss_ctx5 : forall e e' t1 t2 p,
  smallstep e e' ->
  smallstep (ecast e t1 t2 p) (ecast e' t1 t2 p).

Definition tenv := partial_map typ.

Inductive typing : tenv -> exp -> typ -> Prop :=
| ty_cst : forall te n va ta,
  vtann_compatible2 va ta ->
  typing te (ecst n va) (tann tnum ta)
| ty_var : forall te t i,
  Some t = te i ->
  typing te (evar i) t
| ty_lam : forall te i e t1 t2,
  typing (extend te i t1) e t2 ->
  typing te (elam i e) (tfun t1 t2)
| ty_app : forall te e1 e2 t1 t2,
  typing te e1 (tfun t2 t1) ->
  typing te e2 t2 ->
  typing te (eapp e1 e2) t1
| ty_prm : forall te o e1 e2 ta ta1 ta2,
  typing te e1 (tann tnum ta1) ->
  typing te e2 (tann tnum ta2) ->
  taan_rel o ta1 ta2 ta ->
  typing te (eprm o e1 e2) (tann tnum ta)
| ty_cnd : forall te e1 e2 e3 t va ta,
  vtann_compatible anon va ta ->
  typing te e1 (tann tnum ta) ->
  typing te e2 t ->
  typing te e3 t ->
  typing te (ecnd e1 e2 e3) t
| ty_cast : forall te e t1 t2 p,
  typing te e t1 ->
  compatible t1 t2 ->
  typing te (ecast e t1 t2 p) t2
.

Lemma values_dont_reduce : forall e,
  value e -> ~ (exists e' , smallstep e e').
Proof.
  unfold not.
  intros.
  inversion H0; subst.
  inversion H; subst.
  inversion H1.
  inversion H1.
Qed.

(* a stuck term is
   - a failing cast
   - a failing primitive operation
   *)

Inductive stuckterm : exp -> Prop :=
| fc_base : forall n t a a' p,
  a <> a' ->
  stuckterm (ecast (ecst n (vd a)) t (tann tnum (taann a')) p)
| fc_prm : forall o a0 a1 a2 n1 n2,
  ~ an_rel o a1 a2 a0 -> 
  stuckterm (eprm o (ecst n1 (vd a1)) (ecst n2 (vd a2)))
| fc_cnd : forall n1 va1 e2 e3,
  ~ vtann_compatible anon va1 tadyn ->
  stuckterm (ecnd (ecst n1 va1) e2 e3)
| fc_app_left : forall e1 e2,
  stuckterm e1 ->
  stuckterm (eapp e1 e2)
| fc_app_right : forall e1 e2,
  value e1 ->
  stuckterm e2 ->
  stuckterm (eapp e1 e2)
| fc_prm_left : forall o e1 e2,
  stuckterm e1 ->
  stuckterm (eprm o e1 e2)
| fc_prm_right : forall o e1 e2,
  value e1 ->
  stuckterm e2 ->
  stuckterm (eprm o e1 e2)
| fc_cnd_cond : forall e1 e2 e3,
  stuckterm e1 ->
  stuckterm (ecnd e1 e2 e3)
| fc_cast : forall e t1 t2 p,
  stuckterm e ->
  stuckterm (ecast e t1 t2 p).

Lemma progress : forall e t,
  typing empty e t ->
  (value e \/ (exists e', smallstep e e') \/ stuckterm e).
Proof.
  intros e t H.
  remember (@empty typ) as Gamma.
  induction H; intros; subst.
  (*ecst*)
  left.
  constructor.
  (*evar*)
  inversion H.
  (*elam*)
  left; constructor.
  (*eapp*)
  destruct IHtyping1.
  reflexivity.
  right.
  destruct IHtyping2.
  reflexivity.
  inversion H1; subst.
  inversion H.
  left.
  exists (ssubst e i e2).
  constructor.
  assumption.
  inversion H2 as [e2'_H2' | FCe2].
  inversion e2'_H2' as [e2' H2'].
  left.
  exists (eapp e1 e2'). 
  inversion H1; subst.
  inversion H; subst.
  constructor. assumption.
  right.
  constructor 5. assumption.
  inversion H2. assumption. assumption.
  right.
  inversion H1.
  left.
  inversion H2 as [e1' H1'].
  exists (eapp e1' e2).
  constructor. assumption.
  right.
  constructor. assumption.
  (*eprm*)
  right.
  destruct IHtyping1.
  reflexivity.
  destruct IHtyping2.
  reflexivity.
  inversion H2; subst; inversion H3; subst.
  inversion H; subst; inversion H0; subst.
  inversion H1; subst.
  inversion H6; inversion H7; subst.
  destruct (exists_an_or_nan o a1 a2) as [a3 anornan].
  destruct anornan as [Pan | Pnan].
  inversion Pan. 
  left.
  exists (ecst (op_int add n n0) (vd a3)).
  constructor. constructor. constructor.
  left.
  exists (ecst (op_int sub n n0) (vd a3)).
  constructor. constructor. constructor.
  left.
  exists (ecst (op_int mul n n0) (vd a3)).
  constructor. constructor. rewrite <- H9. constructor.
  left.
  exists (ecst (op_int div n n0) (vd a3)).
  constructor. constructor. rewrite <- H9. constructor.
  inversion Pnan.
  right.
  apply fc_prm with a3.
  apply nan_not_an. rewrite <- H5 in Pnan. assumption.
  right.
  apply fc_prm with a3.
  apply nan_not_an. rewrite <- H5 in Pnan. assumption.
  right.
  apply fc_prm with a3.
  apply nan_not_an. rewrite <- H5 in Pnan. assumption.
  right.
  apply fc_prm with a3.
  apply nan_not_an. rewrite <- H5 in Pnan. assumption.
  (*static cases*)
  inversion H6; subst. inversion H7; subst.
  left. exists (ecst (op_int o n n0) (vs a3)).
  constructor. constructor. assumption.
  (*impossible cases*)
  inversion H0.
  inversion H.
  inversion H.
  (*inductive cases*)
  inversion H2.
  destruct H3.
  inversion H3 as [e2' H3'].
  left. exists (eprm o (ecst n a) e2').
  constructor. assumption.
  right. apply fc_prm_right. constructor. assumption.
  subst. inversion H.
  (*inductive cases, left*)
  inversion H2.
  inversion H3 as [e1' H3'].
  left; exists (eprm o e1' e2).
  constructor. assumption.
  right. constructor. assumption.
  (*ecnd*)
  right.
  destruct IHtyping1.
  reflexivity.
  inversion H3; subst.
  inversion H; subst.
  inversion H0; subst.
  inversion H6; subst.
  pose (Qeq_dec n 0) as dec_n_0.
  destruct dec_n_0.
  left; exists e3.
  constructor.
  assumption.
  constructor.
  left; exists e2.
  constructor.
  assumption.
  constructor.

  inversion H0. subst.
  inversion H6; subst.
  destruct a0.
  pose (Qeq_dec n 0) as dec_n_0.
  destruct dec_n_0.
  left. exists e3.
  constructor. assumption. constructor.
  left. exists e2.
  constructor. assumption. constructor.

  right. constructor. intro. inversion H4.
  right. constructor. intro. inversion H4.

  inversion H0.

  destruct H3.

  inversion H3 as [e1' H3'].
  left; exists (ecnd e1' e2 e3); constructor; assumption.
  right; constructor; assumption.
  (*ecast*)
  right.
  destruct IHtyping as [value_e | se_fe].
  reflexivity.
  inversion value_e; subst.
  inversion H; subst.
  inversion H0; subst.
  inversion H2; subst.
  left; exists (ecst n a).
  constructor. assumption.
  inversion H5; subst.
  apply vc_num with a0. constructor. constructor. 

  inversion H5; subst.
  pose (ann_eq_dec a1 a0) as Hdec_a0_a1.
  destruct Hdec_a0_a1.

  subst.
  left; exists (ecst n (vs a0)).
  constructor. 
  constructor.
  eauto using vcast, vtann_compatible.

  right. constructor. assumption.

  inversion H5; subst.
  left; exists (ecst n (vd a0)).
  constructor. constructor.
  eauto using vcast, vtann_compatible.

  inversion H5; subst.
  left; exists (ecst n (vd a0)).
  constructor. assumption.
  eauto using vcast, vtann_compatible.

  inversion H0; subst.
  inversion H.
  left; exists (elam i (eapp (elam i (ecast e0 t2a t2b p)) (ecast (evar i) t1b t1a (flip p)))).
  constructor. assumption.
  constructor.
  inversion H.
  inversion se_fe as [Smallstep_e | failing_e].
  inversion Smallstep_e as [e' Smallstep].
  left; exists (ecast e' t1 t2 p).
  constructor 11. assumption.
  right; constructor.
  assumption.
Qed.

Inductive occurs_free (i : id) :  exp -> Prop :=
| of_var : 
  occurs_free i (evar i)
| of_app1 : forall e1 e2,
  occurs_free i e1 ->
  occurs_free i (eapp e1 e2)
| of_app2 : forall e1 e2,
  occurs_free i e2 ->
  occurs_free i (eapp e1 e2)
| of_lam : forall i' e,
  occurs_free i e ->
  i <> i' ->
  occurs_free i (elam i' e)
| of_prm1 : forall o e1 e2,
  occurs_free i e1 ->
  occurs_free i (eprm o e1 e2)
| of_prm2 : forall o e1 e2,
  occurs_free i e2 ->
  occurs_free i (eprm o e1 e2)
| of_cnd1 : forall e1 e2 e3,
  occurs_free i e1 ->
  occurs_free i (ecnd e1 e2 e3)
| of_cnd2 : forall e1 e2 e3,
  occurs_free i e2 ->
  occurs_free i (ecnd e1 e2 e3)
| of_cnd3 : forall e1 e2 e3,
  occurs_free i e3 ->
  occurs_free i (ecnd e1 e2 e3)
| of_cast : forall e t1 t2 p,
  occurs_free i e ->
  occurs_free i (ecast e t1 t2 p)
.

Hint Constructors occurs_free.

Definition closed (e:exp) :=
  forall x, ~ occurs_free x e.

Inductive non_binding_context (e : exp) : exp -> Prop :=
| nb_app_left : forall e2,
  non_binding_context e (eapp e e2)
| nb_app_right : forall e1,
  non_binding_context e (eapp e1 e)
| nb_prm_left : forall o e2,
  non_binding_context e (eprm o e e2)
| nb_prm_right : forall o e1,
  non_binding_context e (eprm o e1 e)
| nb_cnd : forall e2 e3,
  non_binding_context e (ecnd e e2 e3)
| nb_cast : forall t1 t2 p,
  non_binding_context e (ecast e t1 t2 p).

Lemma weaken_free_ctx : forall (te:tenv) te' e ec,
  non_binding_context e ec -> 
  (forall x:id, occurs_free x ec -> te x = te' x)
  ->
  (forall x:id, occurs_free x e -> te x = te' x).
Proof.
  intros.
  inversion H; subst; auto.
Qed.


Lemma weaken_free_3 : forall (te:tenv) te' o e1 e2,
  (forall x : id, occurs_free x (eprm o e1 e2) -> te x = te' x)
  ->
  (forall x : id, occurs_free x e1 -> te x = te' x).
Proof.
  auto.
Qed.

Lemma weaken_free_4 : forall (te:tenv) te' o e1 e2,
  (forall x : id, occurs_free x (eprm o e1 e2) -> te x = te' x)
  ->
  (forall x : id, occurs_free x e2 -> te x = te' x).
Proof.
  auto.
Qed.

Lemma weaken_free_cnd2 : forall (te:tenv) te' e1 e2 e3,
  (forall x : id, occurs_free x (ecnd e1 e2 e3) -> te x = te' x)
  ->
  (forall x : id, occurs_free x e2 -> te x = te' x).
Proof.
  auto.
Qed.

Lemma weaken_free_cnd3 : forall (te:tenv) te' e1 e2 e3,
  (forall x : id, occurs_free x (ecnd e1 e2 e3) -> te x = te' x)
  ->
  (forall x : id, occurs_free x e3 -> te x = te' x).
Proof.
  auto.
Qed.

Lemma context_invariance : forall te te' e t,
  (forall x, occurs_free x e -> te x = te' x) ->
  typing te e t ->
  typing te' e t.
Proof.
  intros.
  generalize dependent te'.
  induction H0; intros.
  constructor.
  assumption.
  constructor. rewrite H. apply H0. constructor.
  constructor. apply IHtyping.
  intros. unfold extend.
  remember (beq_id i x) as beq_id_i_x.
  destruct (beq_id_i_x).
  reflexivity.
  apply H.
  constructor. assumption.
  apply beq_id_false_not_eq.
  symmetry. rewrite beq_id_sym. assumption.
  specialize (IHtyping1 te' ).
  specialize (IHtyping2 te').
  pose (weaken_free_ctx te te' e1 (eapp e1 e2)).
  specialize (e (nb_app_left e1 e2) H).
  specialize (IHtyping1 e).
  pose (weaken_free_ctx te te' e2 (eapp e1 e2)).
  specialize (e0 (nb_app_right e2 e1) H).
  specialize (IHtyping2 e0).
  econstructor. eassumption.
  assumption.
  (*eprm*)
  pose (weaken_free_3 te te' o e1 e2 H0).
  specialize (IHtyping1 te' e).
  pose (weaken_free_4 te te' o e1 e2 H0).
  specialize (IHtyping2 te' e0).
  econstructor. eassumption. eassumption. assumption.
  (*ecnd*)
  pose (weaken_free_ctx te te' e1 (ecnd e1 e2 e3)).
  specialize (e (nb_cnd e1 e2 e3) H0).
  specialize (IHtyping1 te' e).
  pose (weaken_free_cnd2 te te' e1 e2 e3 H0).
  specialize (IHtyping2 te' e0).
  pose (weaken_free_cnd3 te te' e1 e2 e3 H0).
  specialize (IHtyping3 te' e4).
  econstructor. eapply H. assumption. assumption. assumption.
  (*ecast*)
  pose (weaken_free_ctx te te' e (ecast e t1 t2 p) (nb_cast e t1 t2 p) H1).
  specialize (IHtyping te' e0).
  constructor. assumption. assumption.
Qed.

Lemma free_in_context : forall te x e t,
  occurs_free x e ->
  typing te e t ->
  exists t', te x = Some t'.
Proof.
  intros te x e t Free Typing.
  generalize dependent te.
  generalize dependent t.
  induction Free; intros t te Typing; inversion Typing; subst.
  symmetry in H1.
  exists t. assumption.
  apply (IHFree (tfun t2 t)). assumption.
  apply (IHFree t2). assumption.
  specialize (IHFree t2). apply IHFree in H4.
  apply not_eq_beq_id_false in H.
  rewrite extend_neq in H4. assumption. rewrite  beq_id_sym. assumption.
  eapply IHFree. eassumption.
  eapply IHFree. eassumption.
  eapply IHFree. eassumption.
  eapply IHFree. eassumption.
  eapply IHFree. eassumption.
  eapply IHFree. eassumption.
Qed.

Lemma typable_empty_closed : forall e t,
  typing empty e t ->
  closed e.
Proof.
  intros.
  remember (@empty typ) as Gamma.
  unfold closed. unfold not.
  intros.
  induction H.
  subst; inversion H0.
  subst; inversion H.
  inversion H0; subst.
  pose (free_in_context (extend empty i t1) x e t2 H3).
  apply e0 in H.
  apply not_eq_beq_id_false in H4.
  rewrite extend_neq in H.
  inversion H. inversion H1.
  rewrite beq_id_sym. assumption.
  specialize (IHtyping1 HeqGamma).
  specialize (IHtyping2 HeqGamma).
  inversion H0; subst.
  apply IHtyping1 in H3. contradiction.
  apply IHtyping2 in H3. contradiction.
  (*eprm*)
  specialize (IHtyping1 HeqGamma).
  specialize (IHtyping2 HeqGamma).
  inversion H0; subst.
  apply IHtyping1 in H4. contradiction.
  apply IHtyping2 in H4. contradiction.
  (*ecnd*)
  specialize (IHtyping1 HeqGamma).
  specialize (IHtyping2 HeqGamma).
  specialize (IHtyping3 HeqGamma).
  inversion H0; subst.
  apply IHtyping1. assumption.
  apply IHtyping2. assumption.
  apply IHtyping3. assumption.
  (*ecast*)
  specialize (IHtyping HeqGamma).
  inversion H0; subst.
  apply IHtyping in H3. contradiction.
Qed.


Lemma typing_empty_typing_te : forall te e t,
  typing empty e t ->
  typing te e t.
Proof.
  intros.
  apply (context_invariance empty).
  apply typable_empty_closed in H.
  intros.
  unfold closed in H.
  apply H in H0. contradiction.
  assumption.
Qed.

Lemma extend_swap : forall A (ctxt: partial_map A) t1 t2 x1 x2,
  x1 <> x2 ->
  forall x, extend (extend ctxt x1 t1) x2 t2 x = extend (extend ctxt x2 t2) x1 t1 x.
Proof.
  intros.
  remember (beq_id x1 x) as beq_id_x1_x.
  remember (beq_id x2 x) as beq_id_x2_x.
  destruct beq_id_x1_x.
  destruct beq_id_x2_x.
  apply beq_id_eq in Heqbeq_id_x1_x.
  apply beq_id_eq in Heqbeq_id_x2_x.
  apply not_eq_beq_id_false in H.
  subst.
  unfold beq_id in H.
  destruct x.
  rewrite <- beq_nat_refl in H.
  inversion H.
  unfold extend.
  rewrite <- Heqbeq_id_x2_x.
  rewrite <- Heqbeq_id_x1_x.
  reflexivity.
  destruct beq_id_x2_x.
  unfold extend.
  rewrite <- Heqbeq_id_x1_x.
  rewrite <- Heqbeq_id_x2_x.
  reflexivity.
  unfold extend.
  rewrite <- Heqbeq_id_x2_x.
  rewrite <- Heqbeq_id_x1_x.
  reflexivity.
Qed.

Lemma closed_substitution : forall te e1 e2 i t t2, 
  typing empty e2 t2 ->
  typing (extend te i t2) e1 t ->
  typing te (ssubst e1 i e2) t.
Proof.
  intros te e1 e2 i t t2 Typing_e2 Typing_e1.
  remember (@empty typ) as Gamma.
  generalize dependent t. 
  generalize dependent te.
  induction e1; intros te tt Typing_e1.
  unfold ssubst.
  inversion Typing_e1; subst.
  remember (beq_id i i0) as beq_id_i_i0.
  destruct beq_id_i_i0.
  inversion H1; subst.
  apply typing_empty_typing_te. 
  pose (extend_eq typ te i0 t2).
  apply beq_id_eq in Heqbeq_id_i_i0; subst.
  symmetry in H0.
  inversion H0; subst.
  rewrite e in H1. inversion H1.
  assumption.
  apply (context_invariance (extend te i t2)).
  intros.
  inversion H; subst.
  apply extend_neq.
  symmetry. assumption. assumption.
  (*eapp*)
  inversion Typing_e1; subst.
  apply IHe1_1 in H2.
  apply IHe1_2 in H4.
  unfold ssubst. fold ssubst.
  econstructor. eapply H2.
  assumption.
  unfold ssubst.
  inversion Typing_e1; subst.
  constructor.
  (*elam*)
  unfold ssubst. fold ssubst.
  inversion Typing_e1; subst.
  assumption.
  remember (beq_id i i0) as beq_id_i_i0.
  destruct beq_id_i_i0.
  unfold ssubst. fold ssubst.
  rewrite <- Heqbeq_id_i_i0.
  inversion Typing_e1; subst.
  apply ty_lam.
  pose (fun x => extend_shadow typ te t2 t1 x i0).
  apply beq_id_eq in Heqbeq_id_i_i0; subst.
  apply functional_extensionality in e.
  rewrite e in H3. assumption.
  (* i <> i0 *)
  symmetry in Heqbeq_id_i_i0. apply beq_id_false_not_eq in Heqbeq_id_i_i0.
  inversion Typing_e1; subst.
  pose (extend_swap typ te t2 t1 i i0 Heqbeq_id_i_i0).
  apply functional_extensionality in e.
  rewrite e in H3.
  specialize (IHe1 (extend te i0 t1)).
  apply IHe1 in H3.
  unfold ssubst. fold ssubst.
  apply not_eq_beq_id_false in Heqbeq_id_i_i0.
  rewrite Heqbeq_id_i_i0.
  constructor. assumption.
  (*eprm*)
  unfold ssubst; fold ssubst.
  inversion Typing_e1; subst.
  econstructor.
  eapply IHe1_1.
  eapply H3.
  eapply IHe1_2.
  eapply H5.
  assumption.
  (*ecnd*)
  unfold ssubst. fold ssubst.
  inversion Typing_e1; subst.
  apply ty_cnd with va ta.
  assumption.
  apply IHe1_1.
  apply H4.
  apply IHe1_2.
  apply H6.
  apply IHe1_3.
  apply H7.
  (*ecast*)
  unfold ssubst. fold ssubst.
  inversion Typing_e1; subst.
  constructor.
  apply IHe1.
  assumption.
  assumption.
Qed.

Lemma typing_preservation : forall e e' t,
  typing empty e t ->
  smallstep e e' ->
  typing empty e' t.
Proof.
  intros e e' t Typing Smallstep.
  generalize dependent t.
  induction Smallstep; intros t Typing; inversion Typing; subst.
    (*ss_beta*)
    inversion H3; subst.
    apply closed_substitution with t2.
    apply H5.
    apply H2.
    (*eprm*)
    inversion H4; subst.
    inversion H6; subst.
    inversion H7; subst. inversion H2; subst. inversion H3; subst.
    inversion H; subst. constructor. constructor.
    inversion H2; subst. inversion H3; subst.
    inversion H. subst.
    apply (an_rel_function o a0 a3 a4 a5) in H0.
    subst. constructor. constructor. assumption.
    (*if_true*)
    assumption. assumption. 
    (*ecast*)
    inversion H; subst. inversion H0; subst. inversion H10; subst.
    constructor. constructor.
    constructor. constructor.
    inversion H7; subst.
    inversion H8; subst.
    inversion H0; subst.
    constructor.
    apply ty_app with t0.
    constructor.
    constructor.
    pose (fun x => extend_shadow typ empty t1b t0 x i).
    apply functional_extensionality in e.
    rewrite e.
    assumption. assumption.
    constructor.
    constructor.
    rewrite extend_eq.
    reflexivity.
    assumption.
    (*ctx_app_left*)
    apply IHSmallstep in H2. econstructor. eapply H2. assumption.
    (*ctx_app_right*)
    apply IHSmallstep in H4. econstructor. eapply H2. assumption.
    (*ctx_prm_left*)
    apply IHSmallstep in H3. econstructor. eapply H3. eassumption. assumption.
    (*ctx_prm_right*)
    apply IHSmallstep in H5. econstructor. eapply H3. eassumption. assumption.
    (*ctx_cnd*)
    apply IHSmallstep in H4. econstructor. eassumption. assumption. assumption. assumption.
    (*ctx_cast*)
    apply IHSmallstep in H5.
    constructor. assumption. assumption.
Qed.

Lemma transitive_type_preservation : forall e e' t,
  typing empty e t ->
  refl_step_closure smallstep e e' ->
  typing empty e' t.
Proof.
  intros e e' t Typing Multistep.
  induction Multistep. 
  assumption.
  apply IHMultistep.
  apply typing_preservation with x.
  assumption.
  assumption.
Qed.

Definition stuck (e:exp) :=
  ~ (exists e', smallstep e e') /\ ~ value e /\ ~ stuckterm e.

Theorem type_soundness : forall e e' t,
  typing empty e t ->
  refl_step_closure smallstep e e' ->
  ~ stuck e'.
Proof.
  intros e e' t Typing Multistep.
  unfold stuck.
  intros [Hnf Hnv].
  inversion Hnv.
  induction Multistep.
  apply progress in Typing.
  inversion Typing as [Tv | Tss].
  apply Hnv in Tv. contradiction.
  inversion Tss as [Ts | Tstuck].
  apply Hnf in Ts. contradiction.
  apply H0 in Tstuck.
  contradiction.
  apply typing_preservation with x y t in Typing.
  apply IHMultistep.
  assumption.
  apply progress in Typing.
  inversion Typing as [Tv | Ts].
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Inductive subtype_tyann : tyann -> tyann -> Prop :=
| subtype_tyann_static : forall a,
  subtype_tyann (taann a) (taann a)
| subtype_tyann_dynamic : 
  subtype_tyann tadyn tadyn.

Inductive subtype : typ -> typ -> Prop :=
| subtype_base : forall ta1 ta2,
  subtype_tyann ta1 ta2 ->
  subtype (tann tnum ta1) (tann tnum ta2)
| subtype_fun : forall t11 t12 t21 t22,
  subtype t21 t11 ->
  subtype t12 t22 ->
  subtype (tfun t11 t12) (tfun t21 t22)
| subtype_prod : forall t11 t12 t21 t22,
  subtype t11 t21 ->
  subtype t12 t22 ->
  subtype (tprod t11 t12) (tprod t21 t22).

Inductive subtype_pos_tyann : tyann -> tyann -> Prop :=
| subtype_pos_tyann_static : forall a,
  subtype_pos_tyann (taann a) (taann a)
| subtype_pos_tyann_dynamic : 
  subtype_pos_tyann tadyn tadyn
| subtype_pos_tyann_mixed : forall a,
  subtype_pos_tyann (taann a) tadyn.

Inductive subtype_neg_tyann : tyann -> tyann -> Prop :=
| subtype_neg_tyann_static : forall a,
  subtype_neg_tyann (taann a) (taann a)
| subtype_neg_tyann_dynamic : 
  subtype_neg_tyann tadyn tadyn
| subtype_neg_tyann_mixed : forall a,
  subtype_neg_tyann tadyn (taann a).

Inductive subtype_pos : typ -> typ -> Prop :=
| subtype_pos_base : forall ta1 ta2,
  subtype_pos_tyann ta1 ta2 ->
  subtype_pos (tann tnum ta1) (tann tnum ta2)
| subtype_pos_fun : forall t11 t12 t21 t22,
  subtype_neg t21 t11 ->
  subtype_pos t12 t22 ->
  subtype_pos (tfun t11 t12) (tfun t21 t22)
| subtype_pos_prod : forall t11 t12 t21 t22,
  subtype_pos t11 t21 ->
  subtype_pos t12 t22 ->
  subtype_pos (tprod t11 t12) (tprod t21 t22)
with subtype_neg : typ -> typ -> Prop :=
| subtype_neg_base : forall ta1 ta2,
  subtype_neg_tyann ta1 ta2 ->
  subtype_neg (tann tnum ta1) (tann tnum ta2)
| subtype_neg_fun : forall t11 t12 t21 t22,
  subtype_pos t21 t11 ->
  subtype_neg t12 t22 ->
  subtype_neg (tfun t11 t12) (tfun t21 t22)
| subtype_neg_prod : forall t11 t12 t21 t22,
  subtype_neg t11 t21 ->
  subtype_neg t12 t22 ->
  subtype_neg (tprod t11 t12) (tprod t21 t22).

Scheme subtype_pos_mut := Induction for subtype_pos Sort Prop
with subtype_neg_mut := Induction for subtype_neg Sort Prop.

Lemma subtype_reflexive : forall t,
  subtype t t.
Proof.
  intros.
  induction t.
  destruct r. constructor. destruct t; constructor. 
  constructor; assumption.
  constructor; assumption.
Qed.


Lemma subtype_tyann_transitive : forall ta1 ta2 ta3,
  subtype_tyann ta1 ta2 ->
  subtype_tyann ta2 ta3 ->
  subtype_tyann ta1 ta3.
Proof.
  intros.
  inversion H; inversion H0; subst; assumption.
Qed.

Lemma subtype_transitive : forall t1 t2 t3,
  subtype t1 t2 -> subtype t2 t3 -> subtype t1 t3.
Proof.
  intros t1 t2 t3 Sub12 Sub23.
  generalize dependent t3. generalize dependent t1.
  induction t2; intros; inversion Sub12; inversion Sub23; subst.
  
  apply subtype_tyann_transitive with ta1 t ta3 in H1.
  constructor. assumption. assumption.

  constructor; auto.

  constructor; auto.
Qed.

Lemma subtype_pos_tyann_reflexive : forall ta,
  subtype_pos_tyann ta ta.
Proof.
  intros.
  destruct ta.
  constructor. constructor.
Qed.

Lemma subtype_neg_tyann_reflexive : forall ta,
  subtype_neg_tyann ta ta.
Proof.
  intros. destruct ta; constructor.
Qed.

Lemma subtype_pos_neg_reflexive : forall t,
  subtype_pos t t /\ subtype_neg t t.
Proof.
  intros.
  induction t.
  destruct r.
  split.
  constructor.
  apply subtype_pos_tyann_reflexive.
  constructor.
  apply subtype_neg_tyann_reflexive.
  (*fun*)
  destruct IHt1. destruct IHt2.
  split; constructor; auto.
  (*prod*)
  destruct IHt1. destruct IHt2.
  split; constructor; auto.
Qed.

Lemma subtype_pos_neg_transitive : forall t1 t2 t3,
  (subtype_pos t1 t2 -> subtype_pos t2 t3 -> subtype_pos t1 t3) /\
  (subtype_neg t1 t2 -> subtype_neg t2 t3 -> subtype_neg t1 t3).
Proof.
  intros.
  generalize dependent t1. generalize dependent t3.
  induction t2.
  (*tnum*)
  intros. 
  split; intros Sub12 Sub23; inversion Sub12; inversion Sub23; subst.

Lemma subtype_pos_tyann_transitive : forall ta1 ta2 ta3,
  subtype_pos_tyann ta1 ta2 ->
  subtype_pos_tyann ta2 ta3 ->
  subtype_pos_tyann ta1 ta3.
Proof.
  intros.
  inversion H. inversion H0. subst. rewrite H3. assumption.
  subst. assumption. subst. assumption. subst. inversion H0. assumption.
  subst. inversion H0. assumption.
Qed.

  apply subtype_pos_tyann_transitive with ta1 t ta3 in H1.
  constructor. auto. auto.

Lemma subtype_neg_tyann_transitive : forall ta1 ta2 ta3,
  subtype_neg_tyann ta1 ta2 ->
  subtype_neg_tyann ta2 ta3 ->
  subtype_neg_tyann ta1 ta3.
Proof.
  intros ta1 ta2 ta3 S12 S23.
  inversion S12; inversion S23; subst; auto. 
  constructor. constructor. inversion H1.
Qed.

  apply subtype_neg_tyann_transitive with ta1 t ta3 in H1.
  constructor. auto. auto.
  (*fun*)
  intros.
  split; intros S12 S23; inversion S12; inversion S23; subst; constructor.
  apply IHt2_1; auto.
  apply IHt2_2; auto.
  apply IHt2_1; auto.
  apply IHt2_2; auto.
  (*prod*)
  intros.
  split; intros S12 S23; inversion S12; inversion S23; subst; constructor.
  apply IHt2_1; auto.
  apply IHt2_2; auto.
  apply IHt2_1; auto.
  apply IHt2_2; auto.
Qed.  
  
Lemma subtype_pos_neg_tyann : forall ta1 ta2,
  subtype_tyann ta1 ta2 <-> subtype_pos_tyann ta1 ta2 /\ subtype_neg_tyann ta1 ta2.
Proof.
  intros.
  split; intros ST; inversion ST; subst.
  split. constructor. constructor.
  split. constructor. constructor.
  destruct ta1. destruct ta2. 
  inversion H; subst. constructor.
  inversion H0. inversion H. constructor.
Qed.

Lemma subtype_pos_neg : forall t1 t2,
  subtype t1 t2 <-> subtype_pos t1 t2 /\ subtype_neg t1 t2.
Proof.
  intros.
  split. intros ST. induction ST.
  apply subtype_pos_neg_tyann in H. inversion H.
  split; constructor; assumption.
  (*fun*)
  inversion IHST1. inversion IHST2.
  split; constructor; auto.
  (*prod*)
  inversion IHST1. inversion IHST2.
  split; constructor; auto.
  (*->*)

Lemma subtype_pos_neg_3 : forall t1 t2 t3,
  subtype_pos t1 t2 /\ subtype_pos t2 t3 /\ subtype_neg t1 t2 /\ subtype_neg t2 t3 ->
  subtype t1 t3.
Proof.
  intros t1 t2 t3. generalize dependent t1. generalize dependent t3.
  induction t2; intros t3 t1 STPPNN.
  inversion STPPNN as [STP12 [STP23 [STN12 STN23]]].
  inversion STP12. inversion STP23. subst.
  inversion STN12. inversion STN23. subst.
  constructor.
  apply subtype_pos_tyann_transitive with ta1 t ta3 in H1.
  apply subtype_neg_tyann_transitive with ta1 t ta3 in H2.
  apply subtype_pos_neg_tyann. split; assumption. assumption. assumption.

  inversion STPPNN as [STP12 [STP23 [STN12 STN23]]].
  inversion STP12; inversion STP23; inversion STN12; inversion STN23; subst.
  inversion H11; inversion H17; subst.
  constructor. 
  apply IHt2_1. auto. apply IHt2_2. auto.

  inversion STPPNN as [STP12 [STP23 [STN12 STN23]]].
  inversion STP12; inversion STP23; inversion STN12; inversion STN23; subst.
  inversion H17; inversion H11; subst.
  constructor.
  auto. auto.
Qed.

  intros [SP SN].
  apply subtype_pos_neg_3 with t1.
  split. apply subtype_pos_neg_reflexive.
  split. assumption.
  split. apply subtype_pos_neg_reflexive.
  assumption.
Qed.

Inductive all_casts : exp -> Prop :=
| ac_var : forall i,
  all_casts (evar i)
| ac_app : forall e1 e2,
  all_casts e1 ->
  all_casts e2 ->
  all_casts (eapp e1 e2)
| ac_cst : forall q va,
  all_casts (ecst q va)
| ac_lam : forall i e,
  all_casts e ->
  all_casts (elam i e)
| ac_cnd : forall e1 e2 e3,
  all_casts e1 ->
  all_casts e2 ->
  all_casts e3 ->
  all_casts (ecnd e1 e2 e3)
| ac_prm : forall o e1 e2,
  all_casts e1 ->
  all_casts e2 ->
  all_casts (eprm o e1 e2)
| ac_cast_pos : forall e t1 t2,
  subtype_pos t1 t2 ->
  all_casts e ->
  all_casts (ecast e t1 t2 pos_blame)
| ac_cast_neg : forall e t1 t2,
  subtype_neg t1 t2 ->
  all_casts e ->
  all_casts (ecast e t1 t2 neg_blame)
.

Lemma blame_invariant : forall e e',
  all_casts e ->
  smallstep e e' ->
  all_casts e'.
Proof.
  intros e e' AC Smallstep.
  induction Smallstep.
  inversion AC. subst.
  inversion H2. subst.
  (*substitution lemma*)
  induction e1. 
  unfold ssubst. destruct (beq_id i i0). assumption. assumption. 
  unfold ssubst. fold ssubst. constructor. apply IHe1_1.
  constructor. constructor. inversion H1. assumption. assumption.
  constructor. inversion H1. assumption. inversion H1. assumption.
  apply IHe1_2. constructor. constructor. inversion H1. assumption.
  assumption. constructor. inversion H1. assumption. inversion H1. assumption.
  unfold ssubst. assumption.
  unfold ssubst. fold ssubst. destruct (beq_id i i0). assumption.
  constructor. apply IHe1. constructor. constructor. inversion H1. assumption.
  assumption. constructor. inversion H1. assumption.
  inversion H1. assumption.
  unfold ssubst. fold ssubst. constructor.
  apply IHe1_1. constructor. constructor. inversion H1. assumption. assumption.
  constructor. inversion H1. assumption. inversion H1. assumption.
  apply IHe1_2. constructor. constructor. inversion H1. assumption.
  assumption. constructor. inversion H1. assumption. inversion H1. assumption.
  unfold ssubst. fold ssubst. constructor.
  inversion H1. apply IHe1_1. constructor. constructor.
  assumption.   assumption. constructor. assumption. assumption.
  inversion H1. apply IHe1_2. constructor. constructor.
  assumption. assumption. constructor. assumption. assumption.
  inversion H1. apply IHe1_3. constructor. constructor.
  assumption. assumption. constructor. assumption. assumption.
  unfold ssubst. fold ssubst. inversion H1. constructor. assumption.
  apply IHe1. constructor. constructor. assumption. assumption.
  constructor. assumption. assumption.
  constructor. assumption. apply IHe1.
  constructor. constructor. assumption. assumption.
  constructor. assumption. assumption.
  (*back to main*)
  constructor. inversion AC. assumption. inversion AC. assumption.
  inversion AC. subst. inversion H0. constructor. subst.
  constructor. constructor. constructor. constructor.
  inversion H3. assumption.
  inversion H6. assumption.
  constructor. inversion H3. assumption.
  constructor. subst.
  inversion H0. constructor.
  constructor. constructor. constructor. constructor.
  subst. inversion H3. subst. assumption. subst.
  inversion H6. assumption.
  constructor. subst. inversion H3. subst. assumption. constructor.
  constructor. apply IHSmallstep. inversion AC. assumption.
  inversion AC. assumption.
  inversion AC. subst.
  constructor. assumption. apply IHSmallstep. assumption.
  inversion AC. subst.
  constructor. apply IHSmallstep. assumption. assumption.
  inversion AC. subst.
  constructor. constructor. apply IHSmallstep. assumption.
  inversion AC. subst.
  constructor. apply IHSmallstep. assumption. assumption. assumption.
  inversion AC. subst.
  constructor. assumption. apply IHSmallstep. assumption.
  constructor. assumption. apply IHSmallstep. assumption.
Qed.

Inductive no_failing_cast : exp -> Prop :=
| nfc_base : forall n t a a',
  a <> a' ->
  no_failing_cast (ecast (ecst n (vd a)) t (tann tnum (taann a')) neg_blame)
| nfc_prm : forall o a0 a1 a2 n1 n2,
  ~ an_rel o a1 a2 a0 -> 
  no_failing_cast (eprm o (ecst n1 (vd a1)) (ecst n2 (vd a2)))
| nfc_cnd : forall n1 va1 e2 e3,
  ~ vtann_compatible anon va1 tadyn ->
  no_failing_cast (ecnd (ecst n1 va1) e2 e3)
| nfc_app_left : forall e1 e2,
  no_failing_cast e1 ->
  no_failing_cast (eapp e1 e2)
| nfc_app_right : forall e1 e2,
  value e1 ->
  no_failing_cast e2 ->
  no_failing_cast (eapp e1 e2)
| nfc_prm_left : forall o e1 e2,
  no_failing_cast e1 ->
  no_failing_cast (eprm o e1 e2)
| nfc_prm_right : forall o e1 e2,
  value e1 ->
  no_failing_cast e2 ->
  no_failing_cast (eprm o e1 e2)
| nfc_cnd_cond : forall e1 e2 e3,
  no_failing_cast e1 ->
  no_failing_cast (ecnd e1 e2 e3)
| nfc_cast : forall e t1 t2 p,
  no_failing_cast e ->
  no_failing_cast (ecast e t1 t2 p).

Lemma blame_short : forall e t,
  typing empty e t ->
  all_casts e ->
  stuckterm e ->
  no_failing_cast e.
Proof.
  intros e t Typing AC Stuck. generalize dependent t.
  induction Stuck; intros t0 Typing.
  inversion AC. subst.
  inversion Typing. subst. inversion H8. subst.
  inversion H6. subst. inversion H2. inversion H3.
  subst.
  inversion Typing; subst. inversion H8; subst.
  inversion H6; subst. inversion H2. subst. constructor. assumption.

  apply nfc_prm with a0. assumption.
  apply nfc_cnd. assumption.
  apply nfc_app_left. inversion Typing. apply IHStuck with (tfun t2 t0).
  inversion AC. assumption. assumption.
  apply nfc_app_right. assumption. inversion Typing. apply IHStuck with t2.
  inversion AC. assumption. assumption.
  apply nfc_prm_left. inversion Typing. apply IHStuck with (tann tnum ta1).
  inversion AC. assumption. assumption.
  apply nfc_prm_right. assumption. inversion Typing. apply IHStuck with (tann tnum ta2).
  inversion AC. assumption. assumption.
  apply nfc_cnd_cond. inversion Typing. apply IHStuck with (tann tnum ta).
  inversion AC. assumption. assumption. 
  apply nfc_cast. apply IHStuck with t1. inversion AC. assumption. assumption.
  inversion Typing. assumption.
Qed.

