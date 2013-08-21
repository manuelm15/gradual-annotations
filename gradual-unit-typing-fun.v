Require Export SfLib.

Variable B : Set. (*set of base-type values*)

Variable op : Set. (*there is some set of operations on base types,
this will be lifted to the annotation algebra *)

(*equality on operations is decideable*)
Hypothesis op_eq_dec : forall o1 o2 : op, {o1 = o2} + { o1 <> o2 }.

(*Operations can be applied to base-type values,
  operation application is a function*)
Variable b_rel : op -> B -> B -> B -> Prop.

Hypothesis b_rel_function :
  forall o b1 b2 b b',
    b_rel o b1 b2 b ->
    b_rel o b1 b2 b' ->
    b = b'
.

(*It is decideable wether b_rel is defined on two arguments.*)
Hypothesis decide_op : forall o b1 b2,
  (exists b, b_rel o b1 b2 b) \/ (~exists b, b_rel o b1 b2 b)
.

(* Set of annotations *)
Inductive ann : Set :=
| anon : ann
| acst : id -> ann
| aprm : op -> ann -> ann -> ann
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

(*parameter for the function*)
Inductive join_param :=
 | case (*join_case*)
 | appl (*join_appl*)
 | jop : op -> join_param
.

(*join function on annotations*)
Variable join : join_param -> ann -> ann -> ann -> Prop.

(*join is a function *)
Hypothesis join_function : forall o a1 a2 a a',
  join o a1 a2 a /\ join o a1 a2 a'
  -> a = a'.

(* it is decideable wether join is defined on arguments or not*)
Hypothesis decide_join : forall o a1 a2,
  (exists a, join o a1 a2 a) \/ (~ exists a, join o a1 a2 a).

(*Set of type annotations*)
Inductive tyann : Set :=
| taan : ann -> tyann
| tadyn : tyann (* the question mark...*)
.


(*set of value annotations*)
Inductive vann : Set := 
| vs : ann -> vann  (*static value annotation*)
| vd : ann -> vann  (*dynamic value annotation*)
.

(* join function on value annotations *)
Inductive join_v : join_param -> vann -> vann -> vann -> Prop :=
| join_v_static : forall o a1 a2 a,
                   join o a1 a2 a -> 
                   join_v o (vs a1) (vs a2) (vs a)
| join_v_dyn : forall o a1 a2 a,
                   join o a1 a2 a ->
                   join_v o (vd a1) (vd a2) (vd a)
.

(* join function on type annotations *)
Inductive join_t : join_param -> tyann -> tyann -> tyann -> Prop :=
| join_t_dyn : forall o,
                  join_t o tadyn tadyn tadyn
| join_t_static : forall o a1 a2 a,
                  join o a1 a2 a ->
                  join_t o (taan a1) (taan a2) (taan a)
.

Inductive type : Set :=
| tann : stype -> tyann -> type
with stype : Set :=
| tbase : stype
| tfun : type -> type -> stype
| tsum : type -> type  -> stype
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

Inductive eterm : Type :=
| evar : id -> eterm (* a variable*)
| eop : op -> eterm -> eterm -> eterm (*an operation applied to two terms*)
| eappl : eterm -> eterm -> eterm 
          (* application of lambda-abstraction to a term*)
| ecase : eterm -> id -> eterm -> id -> eterm -> eterm (*case*)
| ecast : eterm -> type -> type -> blame -> eterm 
          (*cast from one type to another with blame*)
| eguard : (vann -> vann -> vann -> Prop) -> vann -> eterm -> eterm
(*guard is an auxillary term to remember what join-function to use,
with which argument*)
| dbase : B ->  vann -> eterm (*value of base-type, a constant*)
| dabstr : id -> eterm -> vann -> eterm (*lambda-expression*)
| dinl : eterm -> vann -> eterm (*lnl e va*)
| dinr : eterm -> vann -> eterm (*lnr e va*)
.


Inductive value : eterm -> Prop :=
| baseval : forall b va, value (dbase b va)
| abstrval : forall i va e, value (dabstr i e va)
| inlval : forall e va, value e 
                           -> value (dinl e va)
| inrval : forall e va, value e
                           -> value (dinr e va)
.

(*compability relation of value annotations and type annotations*)
(*relates D(a) to ? and S(a) to a*)
Inductive vtann_compatible2 : vann -> tyann -> Prop :=
| vcts2 : forall ann, vtann_compatible2 (vs ann) (taan ann)
| vctd2 : forall ann, vtann_compatible2 (vd ann)  tadyn
.


(*other way of saying this is*)
Inductive vtann_compatible (a : ann) : vann -> tyann -> Prop :=
| vtcs : vtann_compatible a (vs a) (taan a)
| vtcd : vtann_compatible a (vd a) tadyn
.

(* vcast e1 t1 t2 e2 p: cast from e1 of type t1 to type t2 with blame p 
   results in e2 *)
Inductive vcast : eterm -> type -> type -> eterm -> blame -> Prop :=
| vc_base : forall b a va1 va2 ta1 ta2 p,
  vtann_compatible a va1 ta1 ->
  vtann_compatible a va2 ta2 ->
  vcast (dbase b va1) (tann tbase ta1) (tann tbase ta2) (dbase b va2) p
| vc_lam : forall a va1 va2 i e ta1 ta2 t1a t1b t2a t2b p,
  vtann_compatible a va1 ta1 ->
  vtann_compatible a va2 ta2 ->
  vcast (dabstr i e va1) (tann (tfun t1a t1b) ta1) (tann (tfun t2a t2b) ta2) 
        (dabstr i 
            (ecast (eappl (dabstr i e va1) (ecast (evar i) t2a t1a (flip p)))
            t1b t2b p) va2) p  (*RC-SG-CAST-FUN*)
| vc_inl : forall a va1 ta1 va2 ta2 e t1a t1b t2a t2b p,
  vtann_compatible a va1 ta1 ->
  vtann_compatible a va2 ta2 ->
  vcast (dinl e va1) (tann (tsum t1a t1b) ta1) (tann (tsum t2a t2b) ta2)
      (dinl (ecast e t1a t2a p) va2) p
| vc_inr : forall a va1 ta1 va2 ta2 e t1a t1b t2a t2b p,
  vtann_compatible a va1 ta1 ->
  vtann_compatible a va2 ta2 ->
  vcast (dinr e va1) (tann (tsum t1a t1b) ta1) (tann (tsum t2a t2b) ta2)
      (dinr (ecast e t1b t2b p) va2) p
.

(* substitution function *)
Fixpoint ssubst (e1 : eterm) (i : id) (e2 : eterm) :=
   match e1 with
   | evar j => if beq_id i j then e2 else evar j
   | eop o ea eb => eop o (ssubst ea i e2) (ssubst eb i e2)
   | eappl ea eb => eappl (ssubst ea i e2) (ssubst eb i e2)
   | ecase ea j eb k ec => ecase (ssubst ea i e2)
                                 j (if beq_id i j then eb
                                           else (ssubst eb i e2))
                                 k (if beq_id i k then ec
                                           else (ssubst ec i e2))
   | ecast ea t1 t2 b => ecast (ssubst ea i e2) t1 t2 b
   | eguard f va ea => eguard f va (ssubst ea i e2)
   | dbase b va => dbase b va
   | dabstr j e' va => if beq_id i j then dabstr j e' va else
                                                dabstr j (ssubst e' i e2) va
   | dinl e' va => dinl (ssubst e' i e2) va
   | dinr e' va  => dinr (ssubst e' i e2) va
   end.

Inductive smallstep : eterm -> eterm -> Prop :=
| ss_beta : forall i e1 e2 va,
  value e2 ->
  smallstep (eappl (dabstr i e1 va) e2)
            (eguard (join_v appl) va (ssubst e1 i e2))
| ss_case_inl : forall i j e e1 e2 va,
  value e ->
  smallstep (ecase (dinl e va) i e1 j e2)
            (eguard (join_v case) va (ssubst e1 i e))
| ss_case_inr : forall i j e e1 e2 va,
  value e ->
  smallstep (ecase (dinr e va) i e1 j e2)
            (eguard (join_v case) va (ssubst e2 j e))
| ss_guard_base : forall (f:vann -> vann -> vann -> Prop) b va va1 va2,
  f va1 va2 va ->
  smallstep (eguard f va1 (dbase b va2))
            (dbase b va)
| ss_guard_abstr : forall (f:vann -> vann -> vann -> Prop) i e va va1 va2,
  f va1 va2 va ->
  smallstep (eguard f va1 (dabstr i e va2))
            (dabstr i e va)
| ss_guard_dinl : forall (f: vann -> vann -> vann -> Prop) e va va1 va2,
  value e ->
  f va1 va2 va ->
  smallstep (eguard f va1 (dinl e va2))
            (dinl e va)
| ss_guard_dinr : forall (f: vann -> vann -> vann -> Prop) e va va1 va2,
  value e ->
  f va1 va2 va ->
  smallstep (eguard f va1 (dinr e va2))
            (dinr e va)
| ss_prim : forall o b1 b2 b va1 va2 va,
   join_v (jop o) va1 va2 va ->
  b_rel o b1 b2 b ->
  smallstep (eop o (dbase b1 va1) (dbase b2 va2)) (dbase b va)
| ss_cast : forall e t1 t2 v p,
  value e ->
  vcast e t1 t2 v p ->
  smallstep (ecast e t1 t2 p) v
| ss_ctx1 : forall e1 e1' e2,
  smallstep e1 e1' ->
  smallstep (eappl e1 e2) (eappl e1' e2)
| ss_ctx11 : forall i va e1 e2 e2',
  smallstep e2 e2' ->
  smallstep (eappl (dabstr i e1 va) e2) (eappl (dabstr i e1 va) e2')
| ss_ctx2 : forall o e1 e1' e2,
  smallstep e1 e1' ->
  smallstep (eop o e1 e2) (eop o e1' e2)
| ss_ctx3 : forall o n1 a1 e2 e2',
  smallstep e2 e2' ->
  smallstep (eop o (dbase n1 a1) e2) (eop o (dbase n1 a1) e2')
| ss_ctx_guard : forall f va e e',
  smallstep e e' ->
  smallstep (eguard f va e) (eguard f va e')
| ss_ctx_case : forall i j e1 e2 e e',
  smallstep e e' ->
  smallstep (ecase e i e1 j e2) (ecase e' i e1 j e2)
| ss_ctx_inl : forall va e e',
  smallstep e e' ->
  smallstep (dinl e va) (dinl e' va)
| ss_ctx_inr : forall va e e',
  smallstep e e' ->
  smallstep (dinr e va) (dinr e' va)
| ss_ctx5 : forall e e' t1 t2 p,
  smallstep e e' ->
  smallstep (ecast e t1 t2 p) (ecast e' t1 t2 p).

Lemma values_dont_reduce : forall e,
  value e -> ~ (exists e' , smallstep e e').
Proof.
  unfold not.
  intros.
  induction e; inversion H; subst; inversion H0; inversion H1.
  (* value dinl *)
  apply IHe. apply H2.
    exists e'. apply H6.
  (* value dinr *)
  apply IHe. apply H2.
    exists e'. apply H6.
Qed.

(* typing environment*)
Definition tenv := partial_map type.

(*compatibility between type annotations*)
Inductive ann_compatible : tyann -> tyann -> Prop :=
| ac_equ : forall a,
  ann_compatible (taan a) (taan a)
| ac_dyn_left : forall a,
  ann_compatible tadyn (taan a)
| ac_dyn_right : forall a,
  ann_compatible (taan a) tadyn
| ac_dyn_both :
  ann_compatible tadyn tadyn.

(*compatibility between types*)
Inductive compatible : type -> type -> Prop :=
| c_num : forall ta1 ta2,
  ann_compatible ta1 ta2 ->
  compatible (tann tbase ta1) (tann tbase ta2)
| c_fun : forall t1a t1b t2a t2b ta1 ta2,
  compatible t1b t1a ->
  compatible t2a t2b ->
  ann_compatible ta1 ta2 ->
  compatible (tann (tfun t1a t2a) ta1) (tann (tfun t1b t2b) ta2)
| c_sum : forall t1a t1b t2a t2b ta1 ta2,
  compatible t1a t1b ->
  compatible t2a t2b ->
  ann_compatible ta1 ta2 ->
  compatible (tann (tsum t1a t2a) ta1) (tann (tsum t1b t2b) ta2)
.

Inductive typing : tenv -> eterm -> type -> Prop :=
| ty_base : forall te va ta b,
  vtann_compatible2 va ta ->
  typing te (dbase b va)  (tann tbase ta) (*RC-T-B*)
| ty_var : forall te t i,
  Some t = te i ->
  typing te (evar i) t (*RC-T-VAR*)
| ty_abstr : forall va ta te i e t' t,
  vtann_compatible2 va ta ->
  typing (extend te i t') e t ->
  typing te (dabstr i e va) (tann (tfun t' t) ta) (*RC-T-ABS*)
| ty_guard : forall te e s va' ta ta' ta'' p,
  typing te e (tann s ta'') ->
  ((join_t p) ta' ta'' ta) ->
  vtann_compatible2 va' ta' ->
  typing te (eguard (join_v p) va' e) (tann s ta) (*RC-T-GUARD*)
| ty_inl : forall va ta te e t1 t2,
  vtann_compatible2 va ta ->
  typing te e t1 ->
  typing te (dinl e va) (tann (tsum t1 t2) ta) (*RC-T-INL*)
| ty_inr : forall va ta te e t1 t2,
  vtann_compatible2 va ta ->
  typing te e t2 ->
  typing te (dinr e va) (tann (tsum t1 t2) ta) (*RC-T-INR*)
| ty_op : forall te e1 e2 ta1 ta2 ta o,
  typing te e1 (tann tbase ta1) ->
  typing te e2 (tann tbase ta2) ->
  join_t (jop o) ta1 ta2 ta ->
  typing te (eop o e1 e2) (tann tbase ta) (*RC-T-OP*)
| ty_app : forall te e1 e2 s t2 ta ta1 ta2,
  typing te e1 (tann (tfun t2 (tann s ta1)) ta) ->
  typing te e2 t2 ->
  join_t appl ta ta1 ta2 ->
  typing te (eappl e1 e2) (tann s ta2) (*RC-T-APP*)
| ty_case : forall te e e1 e2 i j t1 t2 s ta ta1 ta2,
  typing te e (tann (tsum t1 t2) ta1) ->
  typing (extend te i t1) e1 (tann s ta) ->
  typing (extend te j t2) e2 (tann s ta) ->
  join_t case ta1 ta ta2 -> 
  typing te (ecase e i e1 j e2) (tann s ta2) (*RC-T-CASE*)
| ty_cast : forall te e t1 t2 p,
  typing te e t1 ->
  compatible t1 t2 ->
  typing te (ecast e t1 t2 p) t2 (*RC-T-CAST*)
.


Inductive stuckterm : eterm -> Prop := (*TODO this might work, but don't be to sure about it*)
| fc_base : forall n t a a' p,
  a' <> a ->
  stuckterm (ecast (dbase n (vd a)) t (tann tbase (taan a')) p)
| fc_abstr : forall a a' t t1 t2 i e p,
  a' <> a ->
  stuckterm (ecast (dabstr i e (vd a)) t (tann (tfun t1 t2) (taan a')) p) 
| fc_inl : forall a a' e t t1 t2 p,
  a' <> a -> 
  stuckterm (ecast (dinl e (vd a)) t (tann (tsum t1 t2) (taan a')) p)
| fc_inr : forall a a' e t t1 t2 p,
  a' <> a ->
  stuckterm (ecast (dinr e (vd a)) t (tann (tsum t1 t2) (taan a')) p)
| fc_cast : forall e t1 t2 p,
  stuckterm e ->
  stuckterm (ecast e t1 t2 p)
| fc_op1 : forall o a1 a2 b1 b2,
  (~ exists a0, join (jop o) a1 a2 a0) -> 
  stuckterm (eop o (dbase b1 (vd a1)) (dbase b2 (vd a2)))
| fc_op2 : forall  o a1 a2 b1 b2,
  (exists a0, join (jop o) a1 a2 a0) ->
  (~ exists b0, b_rel o b1 b2 b0 )->
  stuckterm (eop o (dbase b1 (vs a1)) (dbase b2 (vs a2)))
| fc_op3 : forall  o a1 a2 b1 b2,
  (exists a0, join (jop o) a1 a2 a0) ->
  (~ exists b0, b_rel o b1 b2 b0 )->
  stuckterm (eop o (dbase b1 (vd a1)) (dbase b2 (vd a2)))
| fc_guard_base : forall a1 a2 f b,
  ~(exists va, f (vd a1) (vd a2) va) ->
  stuckterm (eguard f (vd a1) (dbase b (vd a2)))
| fc_guard_abstr : forall a1 a2 f i e,
  ~(exists va, f (vd a1) (vd a2) va) ->
  stuckterm (eguard f (vd a1) (dabstr i e (vd a2)))
| fc_guard_inl : forall a1 a2 f e,
  ~(exists va, f (vd a1) (vd a2) va) ->
  stuckterm (eguard f (vd a1) (dinl e (vd a2)))
| fc_guard_inr : forall a1 a2 f e,
  ~(exists va, f (vd a1) (vd a2) va) ->
  stuckterm (eguard f (vd a1) (dinr e (vd a2)))
| fc_guard : forall e f va,
  stuckterm e ->
  stuckterm (eguard f va e)
| fc_appl_left : forall e1 e2,
  stuckterm e1 ->
  stuckterm (eappl e1 e2)
| fc_appl_right : forall e1 e2,
  stuckterm e2 ->
  value e1 ->
  stuckterm (eappl e1 e2)
| fc_op_left : forall o e1 e2,
  stuckterm e1 ->
  stuckterm (eop o e1 e2)
| fc_op_right : forall o e1 e2,
  stuckterm e2 ->
  value e1 ->
  stuckterm (eop o e1 e2)
| fc_case : forall e e1 e2 i j,
  stuckterm e ->
  stuckterm (ecase e i e1 j e2)
| fc_inl_ind : forall e va, 
  stuckterm e ->
  stuckterm (dinl e va)
| fc_inr_ind : forall e va, 
  stuckterm e ->
  stuckterm (dinr e va)
.



Lemma progress : forall e t,
  typing empty e t ->
  (value e \/ (exists e', smallstep e e') \/ stuckterm e).
Proof.
  intros e t H.
  remember (@empty type) as Gamma.
  induction H; intros; subst.
  (*dbase*)
  left. constructor.

  (*evar*)
  inversion H.
  (*dabstr*)
  left. constructor.

  (*eguard*)
  destruct IHtyping.
    reflexivity.
    destruct e; inversion H0; inversion H2; subst.
    destruct va'. destruct v.
    (*eguard ... dbase ... *)
    inversion H. inversion H5.

    inversion H1.

    destruct v.
    inversion H. inversion H5.

    right.
    pose (decide_join p a a0).
    destruct o. destruct H3.
    left. exists (dbase b (vd x)).
    constructor. constructor. apply H3.

    right. constructor.
    unfold not. unfold not in H3. intros.
    apply H3. inversion H4.
    inversion H5. exists a3.
    apply H9.

    right. destruct v.
    inversion H1. left.
    inversion H. inversion H8. subst.
    exists (dbase b (vs a)). constructor. constructor.
    inversion H0. subst. apply H9.

    inversion H. inversion H6.

    (*eguard ... dabstr ... *)
    destruct va'; destruct v.
    inversion H. inversion H6.

    inversion H1.

    inversion H. inversion H6.

    right.
    pose (decide_join p a a0).
    destruct o.  destruct H3.
    left.
    exists (dabstr i e (vd x)). constructor. constructor.
    apply H3.

    right. constructor.
    unfold not. unfold not in H3.
    intros. apply H3.
    inversion H4. inversion H5.
    subst. exists a3. apply H9.

    destruct va'; destruct v.

    right. left.
    exists (dabstr i e (vs a)).
    constructor. constructor.
    inversion H1. inversion H. inversion H9.
    subst. apply H3.

    inversion H. inversion H7.

    inversion H1.

    inversion H1.    

    (*eguard ... dinl*)
    destruct va'; destruct v.

    inversion H. inversion H1.

    inversion H1.

    inversion H. inversion H7.

    pose (decide_join p a a0).
    destruct o. destruct H3.
    right. left.
    exists (dinl e (vd x)).
    constructor. apply H8.
    constructor. apply H3.

    right. right.
    constructor.
    unfold not. unfold not in H3.
    intros. apply H3.
    inversion H4. inversion H5.
    exists a3. apply H10.

    destruct va'; destruct v.
    inversion H1.
    inversion H. inversion H11.
    inversion H0. subst.
    right. left.
    exists (dinl e (vs a)). constructor.
    apply H9. constructor. apply H20.  

    inversion H. inversion H8.

    inversion H1.

    inversion H1.
    (*eguard ... dinr *)
    destruct va'; destruct v.

    inversion H. inversion H1.

    inversion H1.

    inversion H. inversion H7.

    pose (decide_join p a a0).
    destruct o. destruct H3.
    right. left.
    exists (dinr e (vd x)).
    constructor. apply H8.
    constructor. apply H3.

    right. right.
    constructor.
    unfold not. unfold not in H3.
    intros. apply H3.
    inversion H4. inversion H5.
    exists a3. apply H10.

    destruct va'; destruct v.
    inversion H1.
    inversion H. inversion H11.
    inversion H0. subst.
    right. left.
    exists (dinr e (vs a)). constructor.
    apply H9. constructor. apply H20.  

    inversion H. inversion H8.

    inversion H1.

    inversion H1.

    destruct H2.
    (*eguard ... e and e -> e'*)
    destruct H2 as [e'].
    right. left. exists (eguard (join_v p) va' e').
    constructor. apply H2.

    (*eguard ... e and stuckterm e*)
    right. right. constructor. apply H2.
  (*dinl*)
  destruct IHtyping.
  reflexivity.
  left. constructor. apply H1.

  destruct H1.
  right. left. destruct H1.
  exists (dinl x va). constructor. apply H1.

  right. right. constructor. apply H1.

  (*dinr*)
  destruct IHtyping.
  reflexivity.
  left. constructor. apply H1.

  destruct H1.
  right. left. destruct H1.
  exists (dinr x va). constructor. apply H1.

  right. right. constructor. apply H1.

  (*eop*)
  right.
  destruct IHtyping1. reflexivity.
  destruct IHtyping2. reflexivity. 
  inversion H2. inversion H3.
    (*eop dbase dbase*)
    inversion H. rewrite <- H4 in H8. inversion H8.
    inversion H0. rewrite <- H5 in H14. inversion H14.
    inversion H1.
    inversion H9. rewrite <- H22 in H9. rewrite <- H19 in H9.
    inversion H9.

    rewrite <- H22 in H12. rewrite <- H12.
    rewrite <- H5 in H0. rewrite <- H20 in H0.
    inversion H0. inversion H26.

    pose (decide_join (jop o) ann0 ann1).
    pose (decide_op o b b0).
    destruct o1. destruct H30 as [a].
    destruct o2. destruct H31 as [b'].
    left. exists (dbase b' (vd a)).
    constructor. constructor. apply H30. apply H31.

    right. apply fc_op3. exists a. apply H30.
    apply H31.

    right. apply fc_op1. apply H30.

    subst. inversion H15. inversion H9.
    subst.
    pose (decide_op o b b0).
    destruct o0. destruct H4 as [b'].
    left. exists (dbase b' (vs a)).
    constructor. constructor. apply H16. apply H4.

    right. apply fc_op2. exists a. apply H16.
    apply H4.

    (* inconsistent cases generated by inverting assumptions of form value e*)
    rewrite <- H14 in H5. inversion H5.

    rewrite <- H16 in H5. inversion H5.

    rewrite <- H16 in H5. inversion H5.

    rewrite <- H16 in H5. inversion H5.

    rewrite <- H17 in H5. inversion H5.

    rewrite <- H15 in H5. inversion H5.

    rewrite <- H8 in H4. inversion H4.

    rewrite <- H10 in H4. inversion H4.

    rewrite <- H10 in H4. inversion H4.

    rewrite <- H10 in H4. inversion H4.

    rewrite <- H11 in H4. inversion H4.

    rewrite <- H9 in H4. inversion H4.

    rewrite <- H5 in H0. inversion H0.

    rewrite <- H6 in H0. inversion H0.

    rewrite <- H6 in H0. inversion H0.

    rewrite <- H4 in H. inversion H.

    rewrite <- H5 in H. inversion H.

    rewrite <- H5 in H. inversion H.

    destruct H3.
    (* eop o e1 e2, e2 -> e'*)
    inversion H2. left. destruct H3.
    exists (eop o (dbase b va) x).
    apply ss_ctx3. apply H3.

    rewrite <- H4 in H. inversion H.

    rewrite <- H5 in H. inversion H.

    rewrite <- H5 in H. inversion H.

    (* eop o e1 e2, stuckterm e2*)
    right. apply fc_op_right.
    apply H3. apply H2.

    destruct H2.
    (* eop o e1 e2, e1 -> e'*)
    left. destruct H2. exists (eop o x e2).
    apply ss_ctx2. apply H2.

    (* app o e1 e2, stuckterm e1 *)
    right. apply fc_op_left. apply H2.

  (* eappl e1 e2 *)
  right.

  inversion H.
  inversion H2.

  destruct IHtyping1.
  reflexivity.

  destruct IHtyping2.
  reflexivity.

  left. exists (eguard (join_v appl) va (ssubst e i e2)).
  apply ss_beta. apply H10.

  destruct H10. destruct H10. left.
  exists (eappl (dabstr i e va) x). apply ss_ctx11.
  apply H10.

  right. apply fc_appl_right. apply H10.
  constructor.

  destruct IHtyping2. reflexivity.
  destruct H9.

  left.
  exists (eguard (join_v appl) va (ssubst e i e2)).
  apply ss_beta. apply H10.

  rewrite <- H5 in H9. inversion H9.

  destruct H9. destruct H9.
  rewrite <- H5 in H9. inversion H9.

  rewrite <- H5 in H9. inversion H9.

  destruct IHtyping1.
  reflexivity.

  rewrite <- H6 in H9. inversion H9.

  destruct H9. destruct H9.

  rewrite H6. left. exists (eappl x e2).
  apply ss_ctx1. apply H9.

  right. rewrite H6. apply (fc_appl_left). apply H9.

  destruct IHtyping1. reflexivity.
  rewrite <- H6 in H9. inversion H9.

  destruct H9. destruct H9. left. rewrite H6.
  exists (eappl x e2). apply ss_ctx1. apply H9.

  right. rewrite H6. apply fc_appl_left. apply H9.

  destruct IHtyping1.
  reflexivity. rewrite <- H7 in H10. inversion H10.

  destruct H10. rewrite H7.  left. destruct H10.
  exists (eappl x e2). apply ss_ctx1. apply H10.

  right. rewrite H7. apply fc_appl_left. apply H10.

  destruct IHtyping1. reflexivity.
  rewrite <- H5 in H7. inversion H7.

  destruct H7. left. destruct H7. rewrite <- H6.
  rewrite H5. exists (eappl x e2). apply ss_ctx1.
  apply H7.

  right. rewrite <- H6. rewrite H5. apply fc_appl_left.
  apply H7. 

  (* ecase e i e1 j e2*)
  right.
  destruct IHtyping1. reflexivity.

  destruct H3.
  inversion H.

  inversion H.

  left. exists (eguard (join_v case) va (ssubst e1 i e)).
  apply ss_case_inl. apply H3.

  left. exists (eguard (join_v case) va (ssubst e2 j e)).
  apply ss_case_inr. apply H3.

  destruct H3. left. destruct H3.
  exists (ecase x i e1 j e2).
  apply ss_ctx_case. apply H3.

  right. constructor. apply H3.

  (* ecast *)
  right. destruct IHtyping.
  reflexivity. destruct H1.
    (*first: cases where (value e)*)
    (*ecast dbase *)
    destruct t1 as [t' tya1]; destruct t2 as [t'' tya2].
    destruct tya1; destruct tya2.
    destruct t'; destruct t''; destruct va; inversion H; inversion H3;
    inversion H0; inversion H10.
    left. exists (dbase b (vs a0)).
    apply ss_cast.
    constructor.
    apply vc_base with (a := a); rewrite H13; constructor. 

    inversion H0; destruct va; inversion H; inversion H8;
    try rewrite <- H1 in H; try inversion H.
    left. exists (dbase b (vd a)).
    apply ss_cast. constructor.
    apply vc_base with (a := a); constructor.

    destruct va; inversion H; inversion H3;
    inversion H0; try rewrite <- H7 in H; try inversion H.
    pose (ann_eq_dec a a0).
    destruct s. left.
    exists (dbase b (vs a)). apply ss_cast.
    constructor.
    apply vc_base with (a:=a). rewrite e. constructor. constructor.

    right. apply fc_base. apply n.

    left. destruct va. inversion H. inversion H3.
    exists (dbase b (vd a)). apply ss_cast. constructor.
    inversion H. inversion H0; try rewrite <- H7 in H; try inversion H.
    apply vc_base with (a:=a); constructor.

    (*ecast dabstr*)
    inversion H. inversion H0. rewrite <- H9 in H. inversion H.

    rewrite <- H11 in H4. inversion H4. inversion H10. 
    destruct va. subst. inversion H6.
    left. 
    exists (dabstr i (ecast (eappl (dabstr i e (vs a)) 
                         (ecast (evar i) t1b t1a (flip p))) t2a t2b p) (vs a)).
    apply ss_cast. constructor.
    apply vc_lam with (a:=a); constructor.

    rewrite <- H13 in H16. rewrite H16 in H6. inversion H6.

    destruct va. rewrite H16 in H6. rewrite <- H13 in H6. inversion H6.

    pose (ann_eq_dec a a0). destruct s.
    left. rewrite <- e1.
    exists (dabstr i (ecast (eappl (dabstr i e (vd a0))
                         (ecast (evar i) t1b t1a (flip p))) t2a t2b p) (vs a)).
    apply ss_cast; try constructor.
    rewrite <- e1. apply vc_lam with (a:=a); constructor.

    right. apply fc_abstr. apply n.

    destruct va. rewrite H16 in H6. rewrite <- H13 in H6.
    inversion H6. left.
    exists (dabstr i (ecast (eappl (dabstr i e (vs a))
                         (ecast (evar i) t1b t1a (flip p))) t2a t2b p) (vd a)).
    apply ss_cast. constructor.
    apply vc_lam with (a:=a); constructor.

    rewrite H16 in H6. rewrite <- H13 in H6. inversion H6.

    destruct va. rewrite H16 in H6. rewrite <- H13 in H6. inversion H6.

    left.
    exists (dabstr i (ecast (eappl (dabstr i e (vd a))
                         (ecast (evar i) t1b t1a (flip p))) t2a t2b p) (vd a)).
    apply ss_cast. constructor.
    apply vc_lam with (a:=a); constructor.

    rewrite <- H11 in H4. inversion H4.

    (* ecast dinl*)
    inversion H0. rewrite <- H3 in H. inversion H.

    rewrite <- H5 in H. inversion H.

    inversion H4. destruct va.
    left. rewrite <- H7 in H5. rewrite <- H5 in H. inversion H.
    inversion H13.
    exists (dinl (ecast e t1a t1b p) (vs a)).
    apply ss_cast. constructor. apply H1.
    apply vc_inl with (a:=a); constructor.

    rewrite <- H5 in H. inversion H.
    rewrite <- H7 in H13. inversion H13.

    destruct va.
    rewrite <- H5 in H. inversion H.
    rewrite <- H7 in H13. inversion H13.

    pose (ann_eq_dec a a0). destruct s.
    left. exists (dinl (ecast e t1a t1b p) (vs a)).
    apply ss_cast. constructor. apply H1. rewrite e0.
    apply vc_inl with (a:=a0); constructor.

    right. apply fc_inl. apply n.

    destruct va.
    left. exists (dinl (ecast e t1a t1b p) (vd a)).
    apply ss_cast. constructor. apply H1.
    apply vc_inl with (a:=a).
    rewrite <- H5 in H. rewrite <- H7 in H. inversion H.
    inversion H13. constructor.
    constructor.

    rewrite <- H5 in H. rewrite <- H7 in H. inversion H.
    inversion H13.

    destruct va.
    rewrite <- H5 in H. rewrite <- H7 in H. inversion H.
    inversion H13.

    left. exists (dinl (ecast e t1a t1b p) (vd a)).
    apply ss_cast. constructor. apply H1.
    apply vc_inl with (a:=a); constructor.

    (*dinr*)
    inversion H.
    rewrite <- H6 in H. inversion H.

    inversion H0; inversion H6.

    rewrite <- H17 in H6. inversion H6.

    rewrite <- H19 in H6. inversion H6.

    destruct va. inversion H12.
    rewrite <- H21 in H19. inversion H19; rewrite <- H25; rewrite <- H26.
    rewrite H27 in H18. rewrite <- H22 in H18. inversion H18.
    left.
    exists (dinr (ecast e t2a t2b p) (vs a)).
    apply ss_cast. constructor. apply H1.
    apply vc_inr with (a:=a); constructor.

    left. exists (dinr (ecast e t2a t2b p) (vd a)).
    apply ss_cast. constructor. apply H1.
    apply vc_inr with (a:=a); constructor.

    inversion H12. destruct ta2.
    pose (ann_eq_dec a0 a). destruct s.
    rewrite e2. left.
    exists (dinr (ecast e t3 t2b p) (vs a)).
    apply ss_cast. constructor. apply H1.
    apply vc_inr with (a:=a); constructor.

    right. apply fc_inr. apply n.

    left.
    exists (dinr (ecast e t3 t2b p) (vd a)).
    apply ss_cast. constructor.
    apply H1.
    apply vc_inr with (a:=a); constructor.

    (*then e -> e'*)
    destruct H1.
    left. destruct H1. 
    exists (ecast x t1 t2 p).
    apply ss_ctx5. apply H1.

    (*then stuckterm e*)
    right. apply fc_cast. apply H1.
Qed.

Inductive occurs_free (i : id) :  eterm -> Prop :=
| of_var : 
  occurs_free i (evar i)
| of_app1 : forall e1 e2,
  occurs_free i e1 ->
  occurs_free i (eappl e1 e2)
| of_app2 : forall e1 e2,
  occurs_free i e2 ->
  occurs_free i (eappl e1 e2)
| of_base1 : forall e1 e2 o,
  occurs_free i e1 ->
  occurs_free i (eop o e1 e2)
| of_base2 : forall e1 e2 o,
  occurs_free i e2 ->
  occurs_free i (eop o e1 e2)
| of_lam : forall i' e va,
  occurs_free i e ->
  i <> i' ->
  occurs_free i (dabstr i' e va)
| of_inl : forall e va,
  occurs_free i e ->
  occurs_free i (dinl e va)
| of_inr : forall e va,
  occurs_free i e ->
  occurs_free i (dinr e va)
| of_case1 : forall j k e e1 e2,
  occurs_free i e ->
  occurs_free i (ecase e j e1 k e2)
| of_case2 : forall j k e e1 e2,
  occurs_free i e1 ->
  i <> j ->
  occurs_free i (ecase e j e1 k e2)
| of_case3 : forall j k e e1 e2,
  occurs_free i e2 ->
  i <> k ->
  occurs_free i (ecase e j e1 k e2)
| of_guard : forall f va e,
  occurs_free i e ->
  occurs_free i (eguard f va e)
| of_cast : forall e t1 t2 p,
  occurs_free i e ->
  occurs_free i (ecast e t1 t2 p)
.

Hint Constructors occurs_free.

Definition closed (e:eterm) := 
  forall x, ~ occurs_free x e.

Inductive non_binding_context (e:eterm) : eterm -> Prop :=
| nb_app_left : forall e2,
  non_binding_context e (eappl e e2)
| nb_app_right : forall e1,
  non_binding_context e (eappl e1 e)
| nb_base_left : forall o e2,
  non_binding_context e (eop o e e2)
| nb_base_right : forall o e1,
  non_binding_context e (eop o e1 e)
| nb_case : forall e1 e2 j k,
  non_binding_context e (ecase e j e1 k e2)
| nb_cast : forall t1 t2 p,
  non_binding_context e (ecast e t1 t2 p)
| nb_inl : forall va,
  non_binding_context e (dinl e va)
| nb_inr : forall va,
  non_binding_context e (dinr e va)
| nb_guard : forall f va,
  non_binding_context e (eguard f va e)
.

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
  (forall x : id, occurs_free x (eop o e1 e2) -> te x = te' x)
  ->
  (forall x : id, occurs_free x e1 -> te x = te' x).
Proof.
  auto.
Qed.

Lemma weaken_free_4 : forall (te:tenv) te' o e1 e2,
  (forall x : id, occurs_free x (eop o e1 e2) -> te x = te' x)
  ->
  (forall x : id, occurs_free x e2 -> te x = te' x).
Proof.
  auto.
Qed.

Lemma weaken_free_case : forall (te:tenv) te' e i j e1 e2,
  (forall x : id, occurs_free x (ecase e i e1 j e2) -> te x = te' x)
  ->
  (forall x : id, occurs_free x e -> te x = te' x).
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
  (* dbase *)
  constructor. apply H.
  (* evar *)
  assert (occurs_free i (evar i)).
    constructor.
  apply H0 in H1.
  constructor. rewrite <- H1. apply H.
  (* dabstr *)
  constructor. apply H.
  apply IHtyping. intros.
  unfold extend.
  remember (beq_id i x) as beq_id_i_x.
  destruct (beq_id_i_x). reflexivity.
  apply H1.
  constructor. apply H2.
  apply beq_id_false_not_eq. rewrite Heqbeq_id_i_x.
  rewrite beq_id_sym. reflexivity.
  (* eguard *)
  apply ty_guard with (ta':=ta') (ta'':=ta'').
  apply IHtyping. intros.
  apply H2.
  constructor. apply H3.
  apply H.
  apply H1.
  (* dinl *)
  constructor. apply H.
  apply IHtyping. intros.
  apply H1.
  constructor. apply H2.
  (* dinr *)
  constructor. apply H.
  apply IHtyping. intros.
  apply H1.
  constructor. apply H2.
  (* eop *)
  apply ty_op with (ta1:=ta1) (ta2:=ta2).
  apply IHtyping1.
  pose (weaken_free_3 te te' o e1 e2 H0).
  apply e.
  apply IHtyping2.
  pose (weaken_free_4 te te' o e1 e2 H0).
  apply e.
  apply H.
  (* eappl *)
  apply ty_app with (t2:=t2) (ta:=ta) (ta1:=ta1).
  apply IHtyping1. intros.
  apply H0. apply of_app1. apply H1.
  apply IHtyping2. intros.
  apply H0. apply of_app2. apply H1.
  apply H.
  (* ecase *)
  apply ty_case with (t1:=t1) (t2:=t2) (ta:=ta) (ta1:=ta1).
  apply IHtyping1.
  pose (weaken_free_case te te' e i j e1 e2).
  apply e0. apply H0.
  apply IHtyping2. intros.
  unfold extend. remember (beq_id i x) as beq_id_i_x.
  destruct beq_id_i_x. reflexivity.
  apply H0.
  apply of_case2. apply H1.
  apply beq_id_false_not_eq. rewrite Heqbeq_id_i_x.
  rewrite beq_id_sym. reflexivity.
  apply IHtyping3. intros.
  unfold extend. remember (beq_id j x) as beq_id_j_x.
  destruct (beq_id_j_x). reflexivity.
  apply H0.
  apply of_case3. apply H1.
  apply beq_id_false_not_eq. rewrite Heqbeq_id_j_x.
  rewrite beq_id_sym. reflexivity.
  apply H.
  (* ecast *)
  constructor.
  apply IHtyping.
  pose (weaken_free_ctx te te' e (ecast e t1 t2 p)).
  apply e0.
  constructor. apply H1.
  apply H.
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
  apply IHFree with (t:=(tann (tfun t2 (tann s ta1)) ta)).
  apply H1.
  apply IHFree with (t:=t2).
  apply H3.
  apply IHFree with (t:=tann tbase ta1).
  apply H3.
  apply IHFree with (t:=tann tbase ta2).
  apply H5.
  apply IHFree in H6. 
  apply not_eq_beq_id_false in H. rewrite extend_neq in H6.
  apply H6. rewrite beq_id_sym. apply H.
  apply IHFree with (t:=t1). apply H4.
  apply IHFree with (t:=t2). apply H4.
  apply IHFree with (t:=(tann (tsum t1 t2) ta1)).
  apply H6.
  apply IHFree in H8.
  apply not_eq_beq_id_false in H. rewrite extend_neq in H8.
  apply H8. rewrite beq_id_sym. apply H.
  apply IHFree in H9.
  apply not_eq_beq_id_false in H. rewrite extend_neq in H9.
  apply H9. rewrite beq_id_sym. apply H.
  apply IHFree with (t:=tann s ta''). apply H3.
  apply IHFree with (t:=t1). apply H5.
Qed.

Lemma typable_empty_closed : forall e t,
  typing empty e t ->
  closed e.
Proof.
  intros.
  remember (@empty type) as E.
  unfold closed. unfold not. intros.
  induction H.
  (*dbase*)
  inversion H0.
  (*evar i*)
  rewrite HeqE in H. inversion H.
  (*dabstr i e va*)
  inversion H0. subst.
  pose (free_in_context (extend empty i t') x e t H4).
  apply e0 in H1.
  apply not_eq_beq_id_false in H6.
  rewrite extend_neq in H1. inversion H1. inversion H2.
  rewrite beq_id_sym. apply H6.
  (* eguard *)
  apply IHtyping. apply HeqE. inversion H0.
  apply H4.
  (* inl *)
  apply IHtyping. apply HeqE. inversion H0.
  apply H3.
  (* inr *)
  apply IHtyping. apply HeqE. inversion H0.
  apply H3.
  (* eop o e1 e2 *)
  inversion H0.
  apply IHtyping1. apply HeqE. apply H4.
  apply IHtyping2. apply HeqE. apply H4.
  (* eappl e1 e2 *)
  inversion H0.
  apply IHtyping1. apply HeqE. apply H4.
  apply IHtyping2. apply HeqE. apply H4.
  (* ecase e i e1 j e2 *)
  inversion H0.
  apply IHtyping1. apply HeqE. apply H5.
  subst.
  pose (free_in_context (extend empty i t1) x e1 (tann s ta) H6).
  apply e0 in H1.
  apply not_eq_beq_id_false in H10.
  rewrite extend_neq in H1. inversion H1. inversion H4.
  rewrite beq_id_sym. apply H10.
  subst.
  pose (free_in_context (extend empty j t2) x e2 (tann s ta) H6).
  apply e0 in H2.
  apply not_eq_beq_id_false in H10.
  rewrite extend_neq in H2. inversion H2. inversion H4.
  rewrite beq_id_sym. apply H10.
  (*ecast*)
  inversion H0.
  apply IHtyping. apply HeqE.
  apply H3.
Qed.


 