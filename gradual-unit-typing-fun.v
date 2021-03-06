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

(* it is decideable whether join is defined on arguments or not*)
Hypothesis decide_join : forall o a1 a2,
  (exists a, join o a1 a2 a) \/ (~ exists a, join o a1 a2 a).

(* x is neutral element regarding join appl*)
Definition neutral_join_appl (x:ann) :=
  forall a, join appl x a a.

(* there exists a neutral element regarding join appl*)
Hypothesis ex_neutral_join_appl : exists x,
  neutral_join_appl x.

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

Lemma join_t_function : forall p ta1 ta2 ta3 ta4,
  (join_t p ta1 ta2 ta3 /\ join_t p ta1 ta2 ta4) ->
  ta3 = ta4.
Proof.
  intros. destruct H.
  inversion H; subst; inversion H0; subst.
  constructor.
  (assert (a=a4)).
  apply join_function with (o:=p) (a1:=a1) (a2:=a2).
  split. apply H1. apply H5.
  subst; reflexivity.
Qed.
  

Inductive type : Set :=
| tann : stype -> tyann -> type
with stype : Set :=
| tbase : stype
| tfun : type -> type -> stype
| tsum : type -> type  -> stype
.

Definition tann_to_cons (t : type) :=
  match t with
  | tann _ (taan _) => vs
  | tann _ tadyn => vd
  end. 

Scheme type_mut := Induction for type Sort Prop
with stype_mut := Induction for stype Sort Prop.

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
| dinl : eterm -> vann -> eterm (*inl e va*)
| dinr : eterm -> vann -> eterm (*inr e va*)
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
| vc_lam : forall a va ta va' ta' n t2 x e p t1 t1' t2' (*mkAnn vtmp*), 
  (*(t2 = tadyn -> mkAnn = vd) -> 
  (t2 = taan vtmp -> mkAnn = vs) ->*) 
  vtann_compatible a va ta ->
  vtann_compatible a va' ta' ->
  neutral_join_appl n ->
  vcast (dabstr x e va)
        (tann (tfun t1 t2) ta)
        (tann (tfun t1' t2') ta')
        (dabstr x (ecast 
                    (eappl (dabstr x e (tann_to_cons t2 n)) (*(vann_to_cons va n))*)  
                           (ecast (evar x) t1' t1(flip p)))
                    t2 t2'
                    p) va')
        p
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
| c_fun : forall t1' t1 t2 t2' ta ta',
  compatible t1' t1 ->
  compatible t2 t2' ->
  ann_compatible ta ta' ->
  compatible (tann (tfun t1 t2) ta)
             (tann (tfun t1' t2') ta')
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
| ty_abstr : forall va ta te i e t' t, (*TODO for t=(s p), join p ta ex*)
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


Inductive stuckterm : eterm -> Prop :=
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
    inversion H0; subst.

    inversion H.

    inversion H3. subst.

    inversion H. inversion H7. subst. left.
    pose ex_neutral_join_appl.
    destruct e0.
    exists (dabstr i
             (ecast (eappl
                        (dabstr i e (tann_to_cons t3 x))
                        (ecast (evar i) t1' t0 (flip p)))
                     t3 t2' p) (vs a)).

    constructor. constructor. apply vc_lam with (a:=a).
    constructor. constructor. apply H4.

    subst. inversion H. subst. inversion H7. subst.

    pose (ann_eq_dec a ann0).
    destruct s. subst. left.
    pose ex_neutral_join_appl.
    destruct e0.
    exists (dabstr i
             (ecast (eappl
                        (dabstr i e (tann_to_cons t3 x))
                        (ecast (evar i) t1' t0 (flip p)))
                     t3 t2' p) (vs ann0)).

    constructor. constructor. apply vc_lam with (a:=ann0).
    constructor. constructor. apply H4.

    right. apply fc_abstr. apply n.

    subst. inversion H. subst. inversion H7. subst.

    left.
    pose ex_neutral_join_appl; destruct e0.
    exists (dabstr i
             (ecast (eappl
                        (dabstr i e (tann_to_cons t3 x))
                        (ecast (evar i) t1' t0 (flip p)))
                     t3 t2' p) (vd a)).
    constructor. constructor. apply vc_lam with (a:=a).
    constructor. constructor. apply H4.

    subst. inversion H. subst. inversion H7. subst.

    pose ex_neutral_join_appl; destruct e0.
    left. exists (dabstr i
         (ecast (eappl
                    (dabstr i e (tann_to_cons t3 x))
                    (ecast (evar i) t1' t0 (flip p)))
                t3 t2' p) (vd ann0)).
    constructor. constructor. apply vc_lam with (a:=ann0).
    constructor. constructor. apply H4.

    inversion H.
                                         
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
    apply  vc_inr with (a:=a); constructor.

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

(* if x occurs free in x and in a typing environment te x = te' x,
   then e has the same type in te and te' 
   (especially: it types at all) *)
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

(* if there are free variables in e and e types in some environment,
   then the variables are typed in that environment*)
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

(* if e types in an empty environment, then e is closed *)
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

(* if e types to t in an empty environment,
   then it types to t in every environment *)
Lemma typing_empty_typing_te : forall e t te,
  typing empty e t ->
  typing te e t.
Proof.
  intros.
  apply (context_invariance empty te e t). intros.
  apply typable_empty_closed in H.
  unfold closed in H.
  apply H in H0. inversion H0.
  apply H.
Qed.


(* extending environments commutes,
   as long as the variables added are not identical. *)
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

(* if two typing environments are similar at all places and receive the same extension,
  the extended environments are similar in all places*)
Lemma identical_extend_identical : forall te te' i (t:type),
  (forall x, te x = te' x) ->
  (forall x, (extend te i t) x = (extend te' i t) x).
Proof.
  intros.
  unfold extend.  
  remember (beq_id i x) as beq_id_i_x.
  destruct beq_id_i_x.
  reflexivity. 
  apply H.
Qed.

(*typing does not change if environment stays the same for all variables.
  this is a form of context invariance*)
Lemma exchangeable_context : forall te te' e t,
  (forall x, te x = te' x) ->
  typing te e t ->
  typing te' e t.
Proof.
  intros te te' e.
  generalize dependent te.
  generalize dependent te'.
  induction e; intros; inversion H0.
  (* evar *)
  constructor.
  rewrite H3.
  apply H.
 
 (* eop *)
  apply ty_op with (ta1:=ta1) (ta2:=ta2).
  apply IHe1 with (te:=te).
  apply H.
  apply H5.
  apply IHe2 with (te:=te).
  apply H.
  apply H7.
  apply H8.
  (* eappl *)
  apply ty_app with (t2:=t2) (ta:=ta) (ta1:=ta1). 
  apply IHe1 with (te:=te).
  apply H.
  apply H3.
  apply IHe2 with (te:=te).
  apply H.
  apply H5.
  apply H7.
  (* ecase *)
  apply ty_case with (t1:=t1) (t2:=t2) (ta:=ta) (ta1:=ta1).  apply IHe1 with (te:=te).
  apply H.
  apply H8.
  apply IHe2 with (te:= (extend te i t1)).
  apply identical_extend_identical.
  apply H.
  apply H9.
  apply IHe3 with (te:= (extend te i0 t2)).
  apply identical_extend_identical.
  apply H.
  apply H10.
  apply H11.
  (* ecast *)
  constructor.
  apply IHe with (te:=te).
  apply H.
  apply H7. apply H8.
  (* eguard *)
  apply ty_guard with (ta':=ta') (ta'':=ta'').
  apply IHe with (te:=te).
  apply H.
  apply H5.
  apply H7.
  apply H8.
  (* dbase *)
  constructor.
  apply H5.
  (* dabstr *)
  constructor.
  apply H6. 
  apply IHe with (te:=(extend te i t')).   
  apply identical_extend_identical.
  apply H.  
  apply H7.
  (* dinl *)
  constructor. 
  apply H4.  
  apply IHe with (te:=te).
  apply H.
  apply H6.
  (* dinr *)
  constructor.
  apply H4.
  apply IHe with (te:=te).
  apply H.
  apply H6.
Qed.

Lemma closed_substitution : forall te e1 e2 i t t2, 
  typing empty e2 t2 ->
  typing (extend te i t2) e1 t ->
  typing te (ssubst e1 i e2) t.
Proof.
  intros te e1 e2 i t t2 Typing_e2 Typing_e1.
  remember (@empty type) as Gamma.
  generalize dependent t. 
  generalize dependent te.
  induction e1; intros te tt Typing_e1.
  (* evar *)
  unfold ssubst.
  inversion Typing_e1; subst.
  remember (beq_id i i0) as beq_id_i_i0.
  destruct beq_id_i_i0.
  inversion H1; subst.
  apply typing_empty_typing_te. 
  pose (extend_eq type te i0 t2).
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
  (* eop *)
  unfold ssubst; fold ssubst.
  inversion Typing_e1; subst.
  econstructor.
  eapply IHe1_1.
  eapply H3.
  eapply IHe1_2.
  eapply H5.
  assumption.
  (*eapp*)
  inversion Typing_e1; subst.
  apply IHe1_1 in H1.
  apply IHe1_2 in H3.
  unfold ssubst; fold ssubst.
  apply ty_app with (t2:=t0) (ta:=ta) (ta1:=ta1).
  apply H1. apply H3.
  apply H5.
  (* ecase *)
  inversion Typing_e1; subst.
  unfold ssubst; fold ssubst.
  apply ty_case with (t1:=t1) (t2:=t0) (ta:=ta) (ta1:=ta1).
  apply IHe1_1. apply H6.
  remember (beq_id i i0) as beq_id_i_i0.
  destruct beq_id_i_i0.
  apply beq_id_eq in Heqbeq_id_i_i0.
  rewrite Heqbeq_id_i_i0 in H7.
  pose (extend_shadow type te t2 t1).
  apply exchangeable_context with (te:=(extend (extend te i0 t2) i0 t1)).
  intros. apply e.
  apply H7.
  apply IHe1_2.
  apply exchangeable_context with (te:=(extend (extend te i t2) i0 t1)).
  apply extend_swap.
  symmetry in Heqbeq_id_i_i0.
  apply beq_id_false_not_eq in Heqbeq_id_i_i0.
  apply Heqbeq_id_i_i0.
  apply H7.
  remember (beq_id i i1) as beq_id_i_i1.
  destruct beq_id_i_i1.
  apply beq_id_eq in Heqbeq_id_i_i1.
  apply exchangeable_context with (te:=(extend (extend te i t2) i1 t0)).
  rewrite Heqbeq_id_i_i1.
  pose (extend_shadow type te t2 t0).
  intros. apply e.
  apply H8.
  apply IHe1_3.
  apply exchangeable_context with (te:=(extend (extend te i t2) i1 t0)).
  apply extend_swap.
  symmetry in Heqbeq_id_i_i1.
  apply beq_id_false_not_eq.
  apply Heqbeq_id_i_i1.
  apply H8.
  apply H9.
  (*ecast*)
  unfold ssubst; fold ssubst.
  inversion Typing_e1; subst.
  constructor.
  apply IHe1.
  assumption.
  assumption.
  (*eguard*)
  unfold ssubst; fold ssubst.
  inversion Typing_e1.
  apply ty_guard with (ta':=ta') (ta'':=ta'').
  apply IHe1. apply H3.
  apply H5.
  apply H6.
  (*dbase*)
  unfold ssubst; fold ssubst.
  apply context_invariance with (te:=(extend te i t2)).
  intros.
  assert (closed (dbase b v)).
  inversion Typing_e1.
  apply typable_empty_closed with (t:=tann tbase ta).
  constructor.
  apply H4.
  unfold closed in H0. unfold not in H0.
  apply H0 in H. inversion H.
  apply Typing_e1.
  (*dabstr*)
  unfold ssubst; fold ssubst.
  remember (beq_id i i0) as beq_id_i_i0.
  destruct beq_id_i_i0.
  apply beq_id_eq in Heqbeq_id_i_i0.
  inversion Typing_e1. subst.
  constructor. apply H4.
  apply exchangeable_context with (te:=(extend (extend te i0 t2) i0 t')).
  pose (extend_shadow type te t2 t').
  intros. apply e.
  apply H5.
  inversion Typing_e1. subst.
  constructor.
  apply H4.
  apply IHe1.
  apply exchangeable_context with (te:=(extend (extend te i t2) i0 t')).
  apply extend_swap.
  apply beq_id_false_not_eq. rewrite Heqbeq_id_i_i0. reflexivity.
  apply H5.
  (*dinl*)
  inversion Typing_e1.
  unfold ssubst; fold ssubst.
  constructor.
  apply H2.
  apply IHe1.
  apply H4.
  (*dinr*)
  inversion Typing_e1.
  unfold ssubst; fold ssubst.
  constructor.
  apply H2.
  apply IHe1.
  apply H4.
Qed.

Lemma typing_preservation : forall e e' t,
  typing empty e t ->
  smallstep e e' ->
  typing empty e' t.
Proof.
  intros e e' t Htype Hss.
  generalize dependent t.
  induction Hss; intros t Htype; inversion Htype; subst.
  (* eguard (join_v appl) va (ssubst e1 i e2)) *)
  inversion H2. subst.
  apply ty_guard with (ta':=ta) (ta'':=ta1).
  apply closed_substitution with (t2:=t2).
  apply H4.
  apply H11.
  apply H6.
  apply H5.
  (* eguard (join_v case) va (ssubst e1 i e)) *)
  (* left case *)
  inversion H7. subst.
  apply ty_guard with (ta':=ta1) (ta'':=ta).
  apply closed_substitution with (t2:=t1).
  apply H11.
  apply H8.
  apply H10.
  apply H4.
  (* eguard (join_v case) va (ssubst e2 j e) *)
  (* right case *)
  inversion H7. subst.
  apply ty_guard with (ta':=ta1) (ta'':=ta).
  apply closed_substitution with (t2:=t2).
  apply H11.
  apply H9.
  apply H10.
  apply H4.
  (*dbase*)
  (* reduced from guard *)
  inversion H4. subst.
  constructor.
  inversion H; inversion H6.
  rewrite <- H5 in H2; rewrite <- H11 in H2.
  inversion H2.
  rewrite <- H3 in H7; rewrite <- H11 in H7.
  inversion H7.
  rewrite <- H5 in H2; rewrite <- H12 in H2.
  inversion H2.
  rewrite H16 in H0; rewrite H18 in H0.
  pose (join_function p a0 a3 a a4).
  assert (join p a0 a3 a /\ join p a0 a3 a4).
  split. apply H0. apply H9.
  apply e in H14.
  rewrite H14.
  constructor.
  constructor.
  rewrite <- H3 in H7; rewrite <- H11 in H7.
  inversion H7.
  (*dabstr ie va*)
  (*reduced from guard term*)
  inversion H4. subst.
  inversion H6; inversion H.
  rewrite <- H12 in H3; rewrite <- H2 in H3;
  inversion H3.
  constructor. constructor.
  apply H10.
  rewrite <- H2 in H7; rewrite <- H12 in H7;
  inversion H7;
  rewrite <- H13 in H3; rewrite <- H5 in H3;
  inversion H3.
  rewrite H17 in H9; rewrite H19 in H9.
  constructor.
  assert (a4 = a).
  apply join_function with (o:=p) (a1:=a1) (a2:=a2).
  split; [apply H9|apply H0].
  rewrite H15; constructor.
  apply H10.
  subst; inversion H7.
  (*dinl e va*)
  (*reduced from guard term*)
  inversion H5; subst.
  inversion H8; inversion H6; subst.
  inversion H7; inversion H0; subst.
  constructor.
  assert (a4 = a).
  apply join_function with (o:=p) (a1:=ann0) (a2:=ann1);
  split; [apply H14 | apply H4].
  rewrite H1; constructor.
  apply H10.
  inversion H0.
  inversion H0.
  constructor.
  inversion H7; inversion H0;
  constructor.
  apply H10.
  (*dinr e va*)
  (*reduced from guard term*)
  inversion H5; subst.
  inversion H8; inversion H6; subst.
  inversion H7; inversion H0; subst.
  constructor.
  assert (a4 = a).
  apply join_function with (o:=p) (a1:=ann0) (a2:=ann1);
  split; [apply H14 | apply H4].
  rewrite H1; constructor.
  apply H10.
  inversion H0.
  inversion H0.
  constructor.
  inversion H7; inversion H0;
  constructor.
  apply H10.
  (*dbase b va*)
  (*generated from operation application*)
  inversion H5; inversion H7; subst.
  inversion H3; inversion H11; subst.
  inversion H8; inversion H; subst.
  assert (a4 = a).
  apply join_function with (o:=(jop o)) (a1:=ann0) (a2:=ann1).
  split; [apply H14| apply H6].
  rewrite H1.
  constructor. constructor.
  inversion H.
  inversion H.
  inversion H8; inversion H; subst.
  constructor. constructor.
  (*value, generated from cast*)
  inversion H0; subst.
  constructor. inversion H2; constructor. 

  constructor. inversion H2; constructor. 

  constructor.
  destruct t2.
    destruct t. simpl.

  apply ty_app with (t2:=t0) (ta:=(taan n)) (ta1:=(taan a0)).
  constructor. 
  constructor.

  inversion H7.
  apply exchangeable_context with (te:= (extend empty x t0)).
  intros x0. symmetry.
  apply extend_shadow with (ctxt:=empty) (x1:=x0) (x2:=x). 

  apply H14.  

  constructor.
  constructor.
  SearchAbout extend.
  unfold extend.
  pose beq_id_refl.
  assert (beq_id x x = true).
  symmetry.
  apply e with (i:=x).
  rewrite H4. reflexivity.

  inversion H8.
  apply H10.

  unfold neutral_join_appl in H3.
  constructor. apply H3.

  simpl. apply ty_app with (t2:=t0) (ta:=(tadyn)) (ta1:=(tadyn)).
  constructor.
  constructor.

  inversion H7.
  apply exchangeable_context with (te:= (extend empty x t0)).
  intros x0. symmetry.
  apply extend_shadow.  

  apply H14.

  constructor.
  constructor.
  unfold extend.
  pose beq_id_refl.
  assert (beq_id x x = true).
  symmetry.
  apply e with (i:=x).
  rewrite H4. reflexivity.

  inversion H8.
  apply H10.

  (*....*)
  constructor.
 
  inversion H8. apply H13.

  (*dinl*)
  constructor. destruct H2; constructor.

  constructor; inversion H7; subst.
  
  assumption.

  inversion H8. subst. assumption.

  (*dinr*)
  constructor. destruct H2; constructor.

  constructor; inversion H7; subst.
  
  assumption.

  inversion H8. subst. assumption.
 
  (*eappl, made step on first argument*)
  apply ty_app with (t2:=t2) (ta:=ta) (ta1:=ta1).
  apply IHHss. apply H1. apply H3. apply H5.

  (*eappl, made step on second argument*)
  apply ty_app with (t2:=t2) (ta:=ta) (ta1:=ta1).
  apply H1. apply IHHss. apply H3. apply H5.

  (*eop, made step on first argument*)
  apply ty_op with (ta1:=ta1) (ta2:=ta2).
  apply IHHss. apply H3. apply H5. apply H6.

  (*eop, made step on second argument*)
  apply ty_op with (ta1:=ta1) (ta2:=ta2).
  apply H3. apply IHHss. apply H5. apply H6.

  (*eguard, made step on guarded term*)
  apply ty_guard with (ta':=ta') (ta'':=ta'').
  apply IHHss. apply H3. apply H5. apply H6.

  (*ecase... *)
  apply ty_case with (t1:=t1) (t2:=t2) (ta:=ta) (ta1:=ta1).
  apply IHHss. apply H6. apply H7. apply H8. apply H9.

  (*dinl... *)
  constructor. apply H2. apply IHHss. apply H4.

  (*dinr... *)
  constructor. apply H2. apply IHHss. apply H4.

  (*ecast*)
  constructor. apply IHHss. apply H5. apply H6.
Qed.
 
(* type preservation carries over multiple steps*)
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

Definition stuck (e:eterm) :=
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

(*cast related subtyping on annotations, neutral*)
Inductive subtype_tyann : tyann -> tyann -> Prop :=
| subtype_tyann_static : forall a,
  subtype_tyann (taan a) (taan a)
| subtype_tyann_dynamic : 
  subtype_tyann tadyn tadyn.

(*cast related subtyping on types, neutral*)
Inductive subtype : type -> type -> Prop :=
| subtype_base : forall ta1 ta2,
  subtype_tyann ta1 ta2 ->
  subtype (tann tbase ta1) (tann tbase ta2)
| subtype_fun : forall t1 t1' t2 t2' ta1 ta2,
  subtype_tyann ta1 ta2 ->
  subtype t2' t1' ->
  subtype t1 t2 ->
  subtype (tann (tfun t1' t1) ta1) (tann (tfun t2' t2) ta2)
| subtype_sum : forall t1 t2 ta1 t1' t2' ta2,
  subtype_tyann ta1 ta2 ->
  subtype t1 t1' ->
  subtype t2 t2' ->
  subtype (tann (tsum t1 t2) ta1) (tann (tsum t1' t2') ta2)
.

(*cast related subtyping on annotations, positive*)
Inductive subtype_pos_tyann : tyann -> tyann -> Prop :=
| subtype_pos_tyann_static : forall a,
  subtype_pos_tyann (taan a) (taan a)
| subtype_pos_tyann_dynamic : 
  subtype_pos_tyann tadyn tadyn
| subtype_pos_tyann_mixed : forall a,
  subtype_pos_tyann (taan a) tadyn.

(*cast related subtyping on annotations, negative*)
Inductive subtype_neg_tyann : tyann -> tyann -> Prop :=
| subtype_neg_tyann_static : forall a,
  subtype_neg_tyann (taan a) (taan a)
| subtype_neg_tyann_dynamic :
  subtype_neg_tyann tadyn tadyn
| subtype_neg_tyann_mixed : forall a,
  subtype_neg_tyann tadyn (taan a).

(*cast related subtyping on types, positive*)
Inductive subtype_pos : type -> type -> Prop :=
| subtype_pos_base : forall ta1 ta2,
  subtype_pos_tyann ta1 ta2 ->
  subtype_pos (tann tbase ta1) (tann tbase ta2)
| subtype_pos_fun : forall t1 t1' t2 t2' ta1 ta2,
  subtype_pos_tyann ta1 ta2 ->
  subtype_pos t1 t2 ->
  subtype_neg t2' t1' ->
  subtype_pos (tann (tfun t1' t1) ta1) (tann (tfun t2' t2) ta2)
| subtype_pos_sum : forall t1 t2 ta1 t1' t2' ta2,
  subtype_pos_tyann ta1 ta2 ->
  subtype_pos t1 t1' ->
  subtype_pos t2 t2' ->
  subtype_pos (tann (tsum t1 t2) ta1) (tann (tsum t1' t2') ta2)
with subtype_neg : type -> type -> Prop :=
| subtype_neg_base : forall ta1 ta2,
  subtype_neg_tyann ta1 ta2 ->
  subtype_neg (tann tbase ta1) (tann tbase ta2)
| subtype_neg_fun : forall t1 t1' t2 t2' ta1 ta2,
  subtype_neg_tyann ta1 ta2 ->
  subtype_neg t1 t2 ->
  subtype_pos t2' t1' ->
  subtype_neg (tann (tfun t1' t1) ta1) (tann (tfun t2' t2) ta2)
| subtype_neg_sum : forall t1 t2 ta1 t1' t2' ta2,
  subtype_neg_tyann ta1 ta2 ->
  subtype_neg t1 t1' ->
  subtype_neg t2 t2' ->
  subtype_neg (tann (tsum t1 t2) ta1) (tann (tsum t1' t2') ta2).

Scheme subtype_pos_mut := Induction for subtype_pos Sort Prop
with subtype_neg_mut := Induction for subtype_neg Sort Prop.

Lemma subtype_tyann_refl : forall ta, subtype_tyann ta ta.
Proof.
 intros ta.
 destruct ta. 
 apply subtype_tyann_static.
 apply subtype_tyann_dynamic.
Qed.

Lemma subtype_refl : forall t, subtype t t.
Proof.
 intros.
 apply type_mut with (P := fun t => subtype t t) (P0 := fun s => forall a, subtype (tann s a) (tann s a)).
 intros. 
 apply H.
 constructor. apply subtype_tyann_refl.
 intros.
 constructor. apply subtype_tyann_refl.
 assumption. assumption.
 intros.
 constructor. apply subtype_tyann_refl.
 assumption. assumption.
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
  subtype t1 t2 ->
  subtype t2 t3 ->
  subtype t1 t3.
Proof.
  intros.
  generalize dependent t1.
  generalize dependent t3.
  apply type_mut with (P := fun t2 => forall t3, subtype t2 t3 -> forall t1, subtype t1 t2 -> subtype t1 t3) 
                      (P0 := fun s => forall a t3, subtype (tann s a) t3 -> 
                                      forall t1, subtype t1 (tann s a) -> 
                                      subtype t1 t3).
  intros. 
  apply H with (a:=t).  apply H0. apply H1.
  
  intros.
  inversion H; inversion H0; subst. constructor. apply subtype_tyann_transitive with (ta2:=a).
  apply H6. apply H2.

  intros.
  inversion H1; inversion H2; subst.
  constructor. apply subtype_tyann_transitive with (ta2:=a).
  apply H14. apply H6.
  apply H. apply H15. apply H8.
  apply H0. apply H9. apply H16.

  intros.
  inversion H1; inversion H2; subst.
  constructor. apply subtype_tyann_transitive with (ta2:=a).
  apply H14. apply H6.
  apply H. apply H8. apply H15.
  apply H0. apply H9. apply H16.
Qed.

Lemma subtype_pos_tyann_reflexive : forall ta,
  subtype_pos_tyann ta ta.
Proof.
  intros. destruct ta; constructor.
Qed.

Lemma subtype_neg_tyann_reflexive : forall ta,
  subtype_neg_tyann ta ta.
Proof.
  intros. destruct ta; constructor.
Qed.

Lemma subtype_pos_tyann_transitive : forall ta1 ta2 ta3,
  subtype_pos_tyann ta1 ta2 ->
  subtype_pos_tyann ta2 ta3 ->
  subtype_pos_tyann ta1 ta3.
Proof.
  intros.
  inversion H; inversion H0; subst; try assumption.
  inversion H0.
Qed.

Lemma subtype_neg_tyann_transitive : forall ta1 ta2 ta3,
  subtype_neg_tyann ta1 ta2 ->
  subtype_neg_tyann ta2 ta3 ->
  subtype_neg_tyann ta1 ta3.
Proof.
  intros.
  inversion H0; inversion H; subst; try assumption.
  inversion H.
Qed.

Lemma subtype_pos_neg_reflexive : forall t,
  subtype_pos t t /\ subtype_neg t t.
Proof.
  intros.
  apply type_mut with (P:= fun t => subtype_pos t t /\ subtype_neg t t)
                      (P0:= fun s => forall ta, subtype_pos (tann s ta) (tann s ta) 
                                             /\ subtype_neg (tann s ta) (tann s ta)); intros.
  apply H.

  split; constructor.
    apply subtype_pos_tyann_reflexive.
    apply subtype_neg_tyann_reflexive.

  split; constructor.
    apply subtype_pos_tyann_reflexive.
    destruct H0. apply H0.
    destruct H. apply H1.

    apply subtype_neg_tyann_reflexive.
    destruct H0. apply H1.
    destruct H. apply H.

  split; constructor.

    apply subtype_pos_tyann_reflexive.
    destruct H. apply H.
    destruct H0. apply H0.

    apply subtype_neg_tyann_reflexive.
    destruct H. apply H1.
    destruct H0. apply H1.
Qed.


Lemma subtype_pos_neg_transitive : forall t1 t2 t3,
  (subtype_pos t1 t2 -> subtype_pos t2 t3 -> subtype_pos t1 t3) /\
  (subtype_neg t1 t2 -> subtype_neg t2 t3 -> subtype_neg t1 t3).
Proof.
  intros.
  generalize dependent t1.
  generalize dependent t3.
  apply type_mut with (P:= fun t2 => forall t3 t1,
                                   (subtype_pos t1 t2 ->
                                    subtype_pos t2 t3 ->
                                    subtype_pos t1 t3) /\
                                   (subtype_neg t1 t2 ->
                                    subtype_neg t2 t3 ->
                                    subtype_neg t1 t3))
                      (P0 := fun s => forall ta t3 t1,
                                   (subtype_pos t1 (tann s ta) ->
                                    subtype_pos (tann s ta) t3 ->
                                    subtype_pos t1 t3) /\
                                   (subtype_neg t1 (tann s ta) ->
                                    subtype_neg (tann s ta) t3 ->
                                    subtype_neg t1 t3)); intros.
  apply H.

  split; intros.
    
     inversion H; inversion H0; subst; constructor.
     apply subtype_pos_tyann_transitive with (ta2 := ta); assumption.

     intros.
     inversion H; inversion H0; subst; constructor.
     apply subtype_neg_tyann_transitive with (ta2 := ta); assumption.

  split; intros.

     inversion H1; inversion H2; subst; constructor.
     apply subtype_pos_tyann_transitive with (ta2:=ta); assumption.
     destruct H0 with (t3:=t7) (t1:=t4).
     apply H3; assumption.
     destruct H with (t3:=t1') (t1:=t2'0).
     apply H4; assumption.
     
     inversion H1; inversion H2; subst; constructor.
     apply subtype_neg_tyann_transitive with (ta2:=ta); assumption.
     destruct H0 with (t3:=t7) (t1:=t4);
     apply H4; assumption.
     destruct H with (t3:=t1') (t1:=t2'0);
     apply H3; assumption.

  split; intros.

     inversion H1; inversion H2; subst; constructor.
     apply subtype_pos_tyann_transitive with (ta2:=ta); assumption.
     destruct H with (t3:=t1'0) (t1:=t4).
     apply H3; assumption.
     destruct H0 with (t3:= t2'0) (t1:=t5).
     apply H3; assumption.


     inversion H1; inversion H2; subst; constructor.
     apply subtype_neg_tyann_transitive with (ta2:=ta); assumption.
     destruct H with (t3:=t1'0) (t1:=t4); apply H4; assumption.
     destruct H0 with (t3:=t2'0) (t1:=t5); apply H4; assumption.
Qed.

Lemma subtype_pos_neg_tyann : forall ta1 ta2,
  subtype_tyann ta1 ta2 <-> subtype_pos_tyann ta1 ta2 /\ subtype_neg_tyann ta1 ta2.
Proof.
  split; intros.

  split; inversion H; constructor; assumption.

  inversion H; 
  inversion H0; subst; 
  inversion H1; subst;
  constructor;
  assumption.
Qed.

Lemma subtype_pos_neg3 : forall t1 t2 t3,
 subtype_pos t1 t2 /\ subtype_pos t2 t3 /\ subtype_neg t1 t2 /\ subtype_neg t2 t3 ->
 subtype t1 t3.
Proof.
 intros.
 generalize dependent t1.
 generalize dependent t3.
 apply type_mut with (P := fun t2 => forall t3 t1 : type,
                                   subtype_pos t1 t2 /\
                                   subtype_pos t2 t3 /\ 
                                   subtype_neg t1 t2 /\
                                   subtype_neg t2 t3 ->
                                   subtype t1 t3)
                     (P0 := fun s => forall ta t3 t1,
                                   subtype_pos t1 (tann s ta) /\
                                   subtype_pos (tann s ta) t3 /\
                                   subtype_neg t1 (tann s ta) /\
                                   subtype_neg (tann s ta) t3 ->
                                   subtype t1 t3); intros.

 (* base case*)
 apply subtype_transitive with (t2 := (tann s t)).
 destruct H0. destruct H1. destruct H2.
 destruct t1.
 inversion H0; subst; inversion H1; subst;
 inversion H2; subst; inversion H3; subst.
 constructor.
 apply subtype_tyann_transitive with (ta2:=t).
 apply subtype_pos_neg_tyann; split; assumption.
 apply subtype_tyann_refl.

 (* function *)
 apply H with (ta:=t).

 split. assumption.

 split.  pose subtype_pos_neg_reflexive.
 destruct a with (t:=(tann (tfun t2' t4) t)).
 apply H4.

 split. assumption.

 pose (subtype_pos_neg_reflexive (tann (tfun t2' t4) t)). 
 destruct a. apply H5.

 (* sum type *)
 apply H with (ta:=t). 

 split. assumption.

 split. pose (subtype_pos_neg_reflexive (tann (tsum t1' t2') t)).
 destruct a. assumption.

 split.  assumption.

 pose (subtype_pos_neg_reflexive (tann (tsum t1' t2') t)).
 destruct a. assumption.

 (* (tann s t) t3 *)
 apply H with (ta:=t).
 
 pose (subtype_pos_neg_reflexive (tann s t)).
 destruct a.
 destruct H0. destruct H3. destruct H4.

 split. assumption.

 split. assumption.
 
 split; assumption.

 (* t tbase *)
 destruct H. inversion H. subst.
 destruct H0. inversion H0. subst. 
 constructor. apply subtype_pos_neg_tyann.
 split.
  apply subtype_pos_tyann_transitive with (ta2:=ta); assumption.

  destruct H1. inversion H1. inversion H2. subst.
  apply subtype_neg_tyann_transitive with (ta2:=ta); assumption.

 (* tfun t *)
 destruct H1. inversion H1. subst. 
 destruct H2. inversion H2. subst.
 destruct H3. inversion H3. subst. inversion H4. subst.

 constructor.
 apply subtype_pos_neg_tyann.
 split.
   apply subtype_pos_tyann_transitive with (ta2:=ta); assumption.
 
   apply subtype_neg_tyann_transitive with (ta2:=ta); assumption.
 
 apply H.
 split. assumption.
 split. assumption.
 split; assumption.
 
 apply H0.
 split. assumption.
 split. assumption.
 split; assumption.

 (* t tsum*)
 destruct H1. inversion H1. subst.
 destruct H2. inversion H2. subst.
 destruct H3. inversion H3. subst. inversion H4. subst.

 constructor.
 apply subtype_pos_neg_tyann.
 split.
   apply subtype_pos_tyann_transitive with (ta2:=ta); assumption.

   apply subtype_neg_tyann_transitive with (ta2:=ta); assumption.

 apply H.
 split. assumption.
 split. assumption.
 split; assumption.

 apply H0.
 split. assumption.
 split. assumption.
 split; assumption.
Qed.

Lemma subtype_pos_neg : forall t1 t2,
 subtype t1 t2 <-> subtype_pos t1 t2 /\ subtype_neg t1 t2.
Proof.
 intros.
 split.
 (* -> *)
 intros ST. induction ST.
 
   (* tbase *)
   split.

   constructor.
   inversion H; constructor.

   constructor.  
   inversion H; constructor.

   (* tfun *)
   destruct IHST1. destruct IHST2. split.

   constructor.
   inversion H; constructor. assumption.
   assumption.  

   constructor.
   inversion H; constructor. assumption.
   assumption.

   (* tsum *)
   destruct IHST1. destruct IHST2. split.

   constructor.
   inversion H; constructor. assumption.
   assumption.

   constructor.
   inversion H; constructor. assumption.
   assumption.

 (* <- *)
 intros.
 apply subtype_pos_neg3 with (t2 := t2).
 destruct H.
 
 pose (subtype_pos_neg_reflexive t2). destruct a.
 
 split. assumption.
 split. assumption.
 split; assumption.
Qed.

Inductive all_casts : eterm -> Prop :=
| ac_var : forall i,
  all_casts (evar i)
| ac_appl : forall e1 e2,
  all_casts e1 ->
  all_casts e2 ->
  all_casts (eappl e1 e2)
| ac_base : forall b va,
  all_casts (dbase b va)
| ac_abstr: forall i e va,
  all_casts e ->
  all_casts (dabstr i e va)
| ac_op : forall o e1 e2,
  all_casts e1 ->
  all_casts e2 ->
  all_casts (eop o e1 e2)
| ac_cast_pos : forall e t1 t2,
  subtype_pos t1 t2 ->
  all_casts e ->
  all_casts (ecast e t1 t2 pos_blame)
| ac_cast_neg : forall e t1 t2,
  subtype_neg t1 t2 ->
  all_casts e ->
  all_casts (ecast e t1 t2 neg_blame)
| ac_dinl : forall e va,
  all_casts e ->
  all_casts (dinl e va)
| ac_dinr : forall e va,
  all_casts e ->
  all_casts (dinr e va)
| ac_guard : forall e va join_f,
  all_casts e ->
  all_casts (eguard join_f va e)
| ac_case : forall e1 e2 e3 x y,
  all_casts e1 ->
  all_casts e2 ->
  all_casts e3 ->
  all_casts (ecase e1 x e2 y e3)
.

Lemma blame_invariant : forall e e',
  all_casts e ->
  smallstep e e' ->
  all_casts e'.
Proof.
  intros e e' AC Smallstep.
  induction Smallstep.
  (* eappl -> eguard *)
  inversion AC. subst. inversion H2. subst.

  induction e1.
  constructor. unfold ssubst. destruct (beq_id i i0).
  apply H3. apply H1.

  inversion H1. subst.
  simpl.
  constructor.
  constructor.
  assert (all_casts (eguard (join_v appl) va (ssubst e1_1 i e2))).
    apply IHe1_1.
    constructor. constructor. apply H5. apply H3.
    constructor. apply H5. apply H5.
  inversion H0. subst. apply H6.
  assert (all_casts (eguard (join_v appl) va (ssubst e1_2 i e2))).
    apply IHe1_2.
    constructor. constructor. apply H7. apply H3.
    constructor. apply H7. apply H7.
  inversion H0. subst. apply H6.

  inversion H1. subst.
  simpl.
  constructor. constructor.
  assert (all_casts (eguard (join_v appl) va (ssubst e1_1 i e2))).
    apply IHe1_1.
    constructor. constructor. apply H5. apply H3.
    constructor. apply H5. apply H5.
  inversion H0. subst.
  apply H7.
  assert (all_casts (eguard (join_v appl) va (ssubst e1_2 i e2))).
    apply IHe1_2.
    constructor. constructor. apply H6. apply H3.
    constructor. apply H6. apply H6.
  inversion H0. subst.
  apply H7.

  inversion H1. subst.
  simpl.
  assert (all_casts (eguard (join_v appl) va (ssubst e1_1 i e2))).
    apply IHe1_1.
    constructor. constructor. apply H6. apply H3.
    constructor. apply H6. apply H6.
  inversion H0; subst.
  assert (all_casts (eguard (join_v appl) va (ssubst e1_2 i e2))).  
    apply IHe1_2.
    constructor. constructor. apply H9. apply H3.
    constructor. apply H9. apply H9.
  inversion H4; subst.
  assert (all_casts (eguard (join_v appl) va (ssubst e1_3 i e2))).
    apply IHe1_3.
    constructor. constructor. apply H10. apply H3.
    constructor. apply H10. apply H10.
  inversion H7; subst.
  destruct (beq_id i i0); destruct (beq_id i i1);
  constructor;
  constructor; assumption.
  
  simpl.
  inversion H2; subst.
  assert (all_casts (eguard (join_v appl) va (ssubst e1 i e2))).
    apply IHe1.
    constructor. constructor. inversion H1; subst. apply H9. apply H9.
    apply H3.
    constructor. inversion H1; subst. apply H9. apply H9.
    inversion H1; subst. apply H9. apply H9.
  constructor.
  inversion H0; subst.
  inversion H1; subst; constructor.
  apply H8. apply H6.
  apply H8. apply H6.
  
  simpl.
  inversion AC; subst.
  inversion H2; subst.
  inversion H4; subst.
  assert (all_casts (eguard (join_v appl) va (ssubst e1 i e2))).
    apply IHe1.
    constructor. constructor. apply H7. apply H6.
    constructor. apply H7.
    apply H7.
  constructor. constructor.
  inversion H0; subst. apply H9.

  simpl. constructor.  apply H1.

  simpl.
  inversion H2; subst. 
  inversion H4; subst.
  assert (all_casts (eguard (join_v appl) va (ssubst e1 i e2))).
    apply IHe1.
    constructor. constructor. apply H5. apply H3.
    constructor. apply H5.
    apply H5.
  inversion H0; subst.
  destruct (beq_id i i0); constructor; constructor; assumption.
  
  simpl.
  inversion H2; subst.
  inversion H1; subst.
  assert (all_casts (eguard (join_v appl) va (ssubst e1 i e2))).
    apply IHe1.
    constructor. constructor. apply H5. apply H3.
    constructor. apply H5.
    apply H5.
  inversion H0; subst.
  constructor. constructor. apply H7.

  simpl.
  inversion H2; subst.
  inversion H1; subst.
  assert (all_casts (eguard (join_v appl) va (ssubst e1 i e2))).
    apply IHe1.
    constructor. constructor. apply H5. apply H3.
    constructor. apply H5.
    apply H5.
  inversion H0; subst.
  constructor. constructor. apply H7.

  (* case -> guard *)
  inversion AC; subst.

  induction e1.

  simpl.
  destruct (beq_id i i0). inversion H3; subst.
  constructor. apply H1.
  constructor. apply H6.

  simpl.
  inversion H6; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e1_1 i e))).
    apply IHe1_1.
    constructor. apply H3.
    apply H2.
    apply H7.
    apply H2.
  inversion H0. subst.
  assert (all_casts (eguard (join_v case) va (ssubst e1_2 i e))).
    apply IHe1_2.
    constructor. apply H3.
    apply H5.
    apply H7.
    apply H5.
  inversion H1. subst.
  constructor. constructor. assumption. assumption.

  simpl.
  inversion H6; subst.
  inversion H3; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e1_1 i e))).
    apply IHe1_1.
    constructor. constructor. apply H1. apply H2.
    apply H7.
    apply H2.
  inversion H0; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e1_2 i e))).
    apply IHe1_2.
    constructor. constructor. apply H1. apply H4. 
    apply H7.
    apply H4.
  inversion H5; subst.
  constructor. constructor. apply H8. apply H10.

  simpl.
  inversion H3; subst.
  inversion H6; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e1_1 i e))).
     apply IHe1_1.
     constructor; assumption.
     apply H5.
  inversion H0; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e1_2 i e))).
     apply IHe1_2.
     constructor; assumption.
     apply H10.
  inversion H2; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e1_3 i e))).
     apply IHe1_3.
     constructor; assumption.
     apply H11.
  inversion H8; subst.
  destruct (beq_id i i0); destruct (beq_id i i1); constructor; constructor;
  assumption.

  simpl.
  inversion AC; subst.
  assert (all_casts e1).
    inversion H9; subst; assumption.
  assert (all_casts (eguard (join_v case) va (ssubst e1 i e))).
    apply IHe1. constructor. apply H4.
    apply H0. apply H10.
    apply H0.
  inversion H1; subst.
  constructor. inversion H9; subst; constructor; assumption.

  simpl.
  inversion H6; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e1 i e))).
    apply IHe1.
    constructor; assumption.
    apply H1.
  inversion H0; subst.
  constructor. constructor; assumption.

  simpl.
  constructor. constructor.

  simpl.
  inversion H6; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e1 i e))).
    apply IHe1.
    constructor; assumption.
    apply H1.
  inversion H0; subst.
  destruct(beq_id i i0); constructor.
  assumption.
  constructor. assumption.

  simpl.
  inversion H3; subst.
  inversion H6; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e1 i e))).
    apply IHe1.
    constructor; assumption.
    apply H2.
  inversion H0; subst.
  constructor. constructor. apply H5.

  simpl.
  inversion H3; subst.
  inversion H6; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e1 i e))).
    apply IHe1.
    constructor; assumption.
    apply H2.
  inversion H0; subst.
  constructor. constructor. apply H5.

  inversion AC; subst.

  induction e2.

  simpl.
  destruct (beq_id j i0). inversion H3; subst.
  constructor. apply H1.
  constructor. apply H7.

  simpl.
  inversion H7; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e2_1 j e))).
    apply IHe2_1.
    constructor. apply H3.
    apply H6.
    apply H2.
    apply H2.
  inversion H0. subst.
  assert (all_casts (eguard (join_v case) va (ssubst e2_2 j e))).
    apply IHe2_2.
    constructor. apply H3.
    apply H6.
    apply H5.
    apply H5.
  inversion H1. subst.
  constructor. constructor. assumption. assumption.

  simpl.
  inversion H7; subst.
  inversion H3; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e2_1 j e))).
    apply IHe2_1.
    constructor. constructor. apply H1. apply H6.
    apply H2.
    apply H2.
  inversion H0; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e2_2 j e))).
    apply IHe2_2.
    constructor. constructor. apply H1. apply H6. 
    apply H4.
    apply H4.
  inversion H5; subst.
  constructor. constructor. apply H8. apply H10.

  simpl.
  inversion H3; subst.
  inversion H7; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e2_1 j e))).
     apply IHe2_1.
     constructor; assumption.
     apply H5.
  inversion H0; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e2_2 j e))).
     apply IHe2_2.
     constructor; assumption.
     apply H10.
  inversion H2; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e2_3 j e))).
     apply IHe2_3.
     constructor; assumption.
     apply H11.
  inversion H8; subst.
  destruct (beq_id j i0); destruct (beq_id j i1); constructor; constructor;
  assumption.

  simpl.
  inversion AC; subst.
  assert (all_casts e2).
    inversion H7; subst; assumption.
  assert (all_casts (eguard (join_v case) va (ssubst e2 j e))).
    apply IHe2. constructor. apply H4.
    apply H9. apply H0.
    apply H0.
  inversion H1; subst.
  constructor. inversion H10; subst; constructor; assumption.

  simpl.
  inversion H7; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e2 j e))).
    apply IHe2.
    constructor; assumption.
    apply H1.
  inversion H0; subst.
  constructor. constructor; assumption.

  simpl.
  constructor. constructor.

  simpl.
  inversion H7; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e2 j e))).
    apply IHe2.
    constructor; assumption.
    apply H1.
  inversion H0; subst.
  destruct(beq_id j i0); constructor.
  assumption.
  constructor. assumption.

  simpl.
  inversion H3; subst.
  inversion H7; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e2 j e))).
    apply IHe2.
    constructor; assumption.
    apply H2.
  inversion H0; subst.
  constructor. constructor. apply H5.

  simpl.
  inversion H3; subst.
  inversion H7; subst.
  assert (all_casts (eguard (join_v case) va (ssubst e2 j e))).
    apply IHe2.
    constructor; assumption.
    apply H2.
  inversion H0; subst.
  constructor. constructor. apply H5.

  (* guard ... *)
  constructor.

  inversion AC; subst.
  inversion H1; subst.
  constructor; assumption. 

  inversion AC; subst.
  inversion H2; subst.
  constructor. assumption.

  inversion AC; subst.
  inversion H2; subst.
  constructor; assumption.

  (* eop -> dbase *)
  constructor.

  (* cast to value *)
  inversion H0; subst.

  constructor.

  (* cast function application *)
  constructor. 
  inversion AC; subst.
  constructor.
  inversion H6; subst.

  inversion H0. subst.

  apply H13.

  constructor. constructor.
  inversion H9. assumption.

  constructor. inversion H6. assumption.
  constructor.

  constructor. inversion H6. assumption.

  constructor. constructor. inversion H9. assumption.

  constructor. inversion H6. assumption.

  constructor.

  (* cast dinl*)

  constructor. inversion AC.  
  constructor. inversion H5. assumption.
  
  inversion H8. assumption.

  constructor. subst. inversion H5. assumption.

  inversion H8. assumption.

  (* cast dinr*)  

  constructor. inversion AC.  
  constructor. inversion H5. assumption.
  
  inversion H8. assumption.

  constructor. subst. inversion H5. assumption.

  inversion H8. assumption.

  (* function application *)
  
  inversion AC; constructor; subst.
  apply IHSmallstep. apply H1.
  apply H2.

  inversion AC; subst; constructor.
  constructor. inversion H1. subst. apply H0.
  apply IHSmallstep. apply H2. 

  (* operation application *)
  constructor. apply IHSmallstep. inversion AC; subst. assumption.
  inversion AC; subst. assumption.

  constructor. inversion AC. subst. apply H1.
  apply IHSmallstep. inversion AC. assumption.

  (* guard term *)
  inversion AC; constructor. subst. apply IHSmallstep. assumption.

  (* case *)
  inversion AC; constructor. subst. apply IHSmallstep. assumption.
  assumption. assumption.

  (* dinl *)
  inversion AC; constructor. apply IHSmallstep. assumption.

  (* dinr *)
  inversion AC; constructor; apply IHSmallstep; assumption.

  (* ecast*)
  inversion AC; subst; constructor; try assumption;
  try apply IHSmallstep; try assumption.
Qed.


Inductive no_failing_cast : eterm -> Prop :=
| nfc_base : forall b t a a',
  a' <> a ->
  no_failing_cast (ecast (dbase b (vd a)) t (tann tbase (taan a')) neg_blame)
| nfc_abstr : forall a a' t t1 t2 i e,
  a' <> a ->
  no_failing_cast (ecast (dabstr i e (vd a)) t (tann (tfun t1 t2) (taan a'))  neg_blame)
| nfc_inl : forall a a' t t1 t2 e,
  a' <> a ->
  no_failing_cast (ecast (dinl e (vd a)) t (tann (tsum t1 t2) (taan a')) neg_blame)
| nfc_inr : forall a a' t t1 t2 e,
  a' <> a ->
  no_failing_cast (ecast (dinr e (vd a)) t (tann (tsum t1 t2) (taan a')) neg_blame)
| nfc_cast : forall e t1 t2 p,
  no_failing_cast e ->
  no_failing_cast (ecast e t1 t2 p)
| nfc_op1 : forall o a1 a2 n1 n2,
  (~ exists a0, join (jop o) a1 a2 a0) -> 
  no_failing_cast (eop o (dbase n1 (vd a1)) (dbase n2 (vd a2)))
| nfc_op2 : forall o a1 a2 b1 b2,
  (exists a0, join (jop o) a1 a2 a0) ->
  (~ exists b0, b_rel o b1 b2 b0) ->
  no_failing_cast (eop o (dbase b1 (vs a1)) (dbase b2 (vs a2)))
| nfc_op3 : forall o a1 a2 b1 b2,
  (exists a0, join (jop o) a1 a2 a0) ->
  (~ exists b0, b_rel o b1 b2 b0) ->
  no_failing_cast (eop o (dbase b1 (vd a1)) (dbase b2 (vd a2)))
| nfc_guard_base : forall a1 a2 f b,
  ~ (exists va, f (vd a1) (vd a2) va) ->
  no_failing_cast (eguard f (vd a1) (dbase b (vd a2)))
| nfc_guard_abstr : forall a1 a2 f i e,
  ~ (exists va, f (vd a1) (vd a2) va) ->
  no_failing_cast (eguard f (vd a1) (dabstr i e (vd a2)))
| nfc_guard_inl : forall a1 a2 f e,
  ~ (exists va, f (vd a1) (vd a2) va) ->
  no_failing_cast (eguard f (vd a1) (dinl e (vd a2)))
| nfc_guard_inr : forall a1 a2 f e,
  ~ (exists va, f (vd a1) (vd a2) va) ->
  no_failing_cast (eguard f (vd a1) (dinr e (vd a2)))
| nfc_guard : forall e f va,
  no_failing_cast e ->
  no_failing_cast (eguard f va e)
| nfc_appl_left : forall e1 e2,
  no_failing_cast e1 ->
  no_failing_cast (eappl e1 e2)
| nfc_appl_right : forall e1 e2,
  value e1 ->
  no_failing_cast e2 ->
  no_failing_cast (eappl e1 e2)
| nfc_op_left : forall o e1 e2,
  no_failing_cast e1 ->
  no_failing_cast (eop o e1 e2)
| nfc_op_right : forall o e1 e2,
  value e1 ->
  no_failing_cast e2 ->
  no_failing_cast (eop o e1 e2)
| nfc_case : forall e e1 e2 i j,
  no_failing_cast e ->
  no_failing_cast (ecase e i e1 j e2) 
| nfc_inl_ind : forall e va,
  no_failing_cast e ->
  no_failing_cast (dinl e va)
| nfc_inr_ind : forall e va,
  no_failing_cast e ->
  no_failing_cast (dinr e va).

Lemma blame_short : forall e t,
  typing empty e t ->
  all_casts e ->
  stuckterm e ->
  no_failing_cast e.
Proof.
  intros e t Typing AC Stuck. generalize dependent t.
  induction Stuck; intros t0 Typing.
  (* cast base value *)
  inversion AC. subst.
  inversion Typing. subst.
  inversion H8. subst. inversion H6. subst.
  inversion H2. inversion H3. 
 
  subst. apply nfc_base. assumption.
  (* cast function *)

  inversion AC. subst.
  inversion Typing. subst.
  inversion H8. subst. inversion H7. subst.
  inversion H2. subst. inversion H6.

  subst. apply nfc_abstr. assumption.
  (* cast dinl*)

  inversion AC. subst.
  inversion Typing. subst.
  inversion H8. subst. inversion H4. subst.
  inversion H2. subst. inversion H10.

  apply nfc_inl. assumption.

  (* cast dinr *)
  inversion AC. subst.
  inversion Typing. subst.
  inversion H8. subst. inversion H4. subst.
  inversion H2. subst. inversion H10.

  apply nfc_inr. assumption.

  (* cast *)
  apply nfc_cast.
  inversion Typing. subst.
  apply IHStuck with (t:=t1).

  inversion AC. subst. assumption. assumption.
  assumption.

  (* operation, both dynamic, no join of annotations possible *)
  apply nfc_op1. apply H.

  (* operation, both static, operation not defined on values *)
  apply nfc_op2. assumption. assumption.

  (* operation, both dynamic, operation not defined on values *)
  apply nfc_op3. assumption. assumption.

  (* guard term, dynamic annotations, base-value*)
  apply nfc_guard_base.  assumption.

  (* guard term, dynamic annotations, abstrafction*)
  apply nfc_guard_abstr. assumption.

  (* guard term, dynamic annotations, inl *)
  apply nfc_guard_inl. assumption.

  (* guard term, dynamic annotations, inr *)
  apply nfc_guard_inr. assumption.

  (* guard term, inductive case *)
  apply nfc_guard. inversion Typing. subst.
  apply IHStuck with (t:=(tann s ta'')).
  inversion AC; assumption. assumption.

  (* application, stuck on function *)
  apply nfc_appl_left. inversion Typing. subst.
  apply IHStuck with (t:=(tann (tfun t2 (tann s ta1)) ta)).

  inversion AC. assumption. assumption.

  (* application, stuck on argument *)
  inversion Typing; subst.
  apply nfc_appl_right. assumption.
  
  apply IHStuck with (t:=t2).
  inversion AC. assumption.

  assumption.

  (* operation, stuck on first expression *)
  inversion Typing; subst.

  apply nfc_op_left.
  apply IHStuck with (t:=(tann tbase ta1)).
  inversion AC. assumption.
  assumption.

  (* operation, stuck on second expression *)
  inversion Typing; subst.

  apply nfc_op_right. assumption.
  apply IHStuck with (t:=(tann tbase ta2)).

  inversion AC; assumption.
  assumption.

  (* case *)
  apply nfc_case.
  inversion Typing; subst.
  apply IHStuck with (t:= (tann (tsum t1 t2) ta1)).

  inversion AC; assumption.
  assumption.

  (* inl, inductive case *)
  apply nfc_inl_ind.
  inversion Typing; subst.
  apply IHStuck with t1.
  
  inversion AC; assumption.
  assumption.

  (*inr, inductive case *)
  apply nfc_inr_ind.
  inversion Typing; subst.
  apply IHStuck with t2.

  inversion AC; assumption.
  assumption.
Qed.