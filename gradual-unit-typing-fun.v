Require Export SfLib.

Variable B : Set. (*set of base-type values*)

Variable op : Set. (*there is some set of operations on base types,
this will be lifted to the annotation algebra *)

(*Operations can be applied to base-type values,
  operation application is a function*)
Variable b_rel : op -> B -> B -> B -> Prop.

Hypothesis b_rel_function :
  forall o b1 b2 b b',
    b_rel o b1 b2 b ->
    b_rel o b1 b2 b' ->
    b = b'
.
(* TODO n-ary operations *)

Inductive ann : Set :=
| anon : ann
| acst : id -> ann
| aprm : op -> ann -> ann -> ann
. 

(* a relation describing how annotations behave under operations*)
(* for example, for an annotation a, a + a = a *)
Variable an_rel : op -> ann -> ann -> ann -> Prop.

(* an_rel should be a function
 (only one resulting annotation if a opperation is applied to two annoatations)
*)
Hypothesis an_rel_function : 
 forall o a1 a2 a a', an_rel o a1 a2 a ->
                      an_rel o a1 a2 a' ->
                      a = a'.
(* Note that an_rel in general might be a partial function*)

(*join function for function application, somewhat
 similar to join function on operations...*)
Variable join_app_stat : ann -> ann -> ann -> Prop.

Hypothesis join_app_stat_function :
   forall a1 a2 a a',
         join_app_stat a1 a2 a ->
         join_app_stat a1 a2 a' ->
         a = a'.

(*join function for case application*)
Variable join_case_stat : ann -> ann -> ann -> Prop.

Hypothesis join_case_stat_function :
   forall a1 a2 a a',
         join_case_stat a1 a2 a ->
         join_case_stat a1 a2 a' ->
         a = a'.

(*Set of type annotations*)
Inductive tyann : Set :=
| taan : ann -> tyann
| tadyn : tyann (* the question mark...*)
.

(*generator for join functions on type annotations*)
Inductive ho_join_t : (ann -> ann -> ann -> Prop)
   -> tyann -> tyann -> tyann -> Prop :=
   | ho_join_t_static : 
       forall (f: (ann -> ann -> ann -> Prop)) a1 a2 a, 
       f a1 a2 a -> ho_join_t f (taan a1) (taan a2) (taan a)
   | ho_join_t_dynamic : forall f, ho_join_t f tadyn tadyn tadyn.

(*if ho_join is applied to a function, the result is a function*)
Lemma ho_join_t_keep_fun : forall (f: ann -> ann -> ann -> Prop) 
    ta1 ta2 ta ta',
   (forall a1 a2 a a', f a1 a2 a -> f a1 a2 a' -> a = a') ->
   (((ho_join_t f) ta1 ta2 ta) -> ((ho_join_t f) ta1 ta2 ta')
    -> ta = ta').
Proof.
  intros f ta1 ta2 ta ta' f_fun.
  intros H0 H1.
  inversion H0.
    inversion H1.
      assert (a1 = a0).
        rewrite <- H8 in H3.
        inversion H3. reflexivity.
      assert (a3 = a2).
        rewrite <- H9 in H4.
        inversion H4. reflexivity.
      assert (a = a4).
        rewrite <- H11 in H6.
        rewrite H12 in H6.
        apply f_fun with (a:=a) (a':=a4) (a1:=a1) (a2:=a2).
        apply H.
        apply H6.
      rewrite H13. reflexivity.
      rewrite <- H3 in H7. inversion H7.
    inversion H1.
      rewrite <- H7 in H2. inversion H2.
      reflexivity.
Qed.

Definition join_app_t := ho_join_t join_app_stat.

Theorem join_app_t_function : forall ta1 ta2 ta ta',
          join_app_t ta1 ta2 ta ->
          join_app_t ta1 ta2 ta' ->
          ta = ta'.
Proof.
  intros ta1 ta2 ta ta'.
  apply ho_join_t_keep_fun.
  apply join_app_stat_function.
Qed.

Definition join_case_t := ho_join_t join_case_stat.

Theorem join_case_t_function : forall ta1 ta2 ta ta',
          join_case_t ta1 ta2 ta ->
          join_case_t ta1 ta2 ta' ->
          ta = ta'.
Proof.
  intros ta1 ta2 ta ta'.
  apply ho_join_t_keep_fun.
  apply join_case_stat_function.
Qed.

Definition join_op_t (o:op) : tyann -> tyann -> tyann -> Prop :=
   ho_join_t (an_rel o).

     
Theorem join_op_t_function : forall o ta1 ta2 ta ta',
          join_op_t o ta1 ta2 ta ->
          join_op_t o ta1 ta2 ta' ->
          ta = ta'.
Proof.
  intros.
  apply ho_join_t_keep_fun with (f:=(an_rel o)) (ta1:=ta1) (ta2:=ta2).
  apply an_rel_function.
  apply H.
  apply H0.
Qed.

(*set of value annotations*)
Inductive vann : Set := 
| vs : ann -> vann  (*static value annotation*)
| vd : ann -> vann  (*dynamic value annotation*)
.

(*generator for join functions on value annotations*)
Inductive ho_join_v : (ann -> ann -> ann -> Prop)
                     -> (vann -> vann -> vann -> Prop) :=
| ho_join_v_static : forall (f: ann -> ann -> ann -> Prop) a1 a2 a3,
      f a1 a2 a3 -> ho_join_v f (vs a1) (vs a2) (vs a3)
| ho_join_v_dyn : forall (f: ann -> ann -> ann -> Prop) a1 a2 a3,
      f a1 a2 a3 -> ho_join_v f (vd a1) (vd a2) (vd a3)
.

(*everything generated from a function with ho_join_v is a function*)
Lemma ho_join_v_keep_fun : forall (f : ann -> ann -> ann -> Prop)
          va1 va2 va va',
          (forall a1 a2 a a', f a1 a2 a -> f a1 a2 a' -> a = a')
       -> (ho_join_v f) va1 va2 va
       -> (ho_join_v f) va1 va2 va'
       -> (va = va').
Proof.
  intros f va1 va2 va va' f_fun.
  intros.
  inversion H.
    inversion H0.
      assert (a1 = a0) as EQ10.
        rewrite <- H3 in H8. inversion H8. reflexivity.
      assert (a4 = a2) as EQ42.
        rewrite <- H4 in H9. inversion H9. reflexivity.
      assert (a3 = a5) as EQ35.
        apply f_fun with (a1:=a1) (a2:=a2).
        apply H1. rewrite EQ10. rewrite <- EQ42. apply H6.
      rewrite EQ35. reflexivity.
      rewrite <- H3 in H8. inversion H8.
    inversion H0.
      rewrite <- H3 in H8. inversion H8.
      assert (a1 = a0) as EQ10.
        rewrite <- H3 in H8. inversion H8. reflexivity.
      assert (a4 = a2) as EQ42.
        rewrite <- H4 in H9. inversion H9. reflexivity.
      assert (a3 = a5) as EQ35.
       apply f_fun with (a1:=a1) (a2:=a2).
       apply H1. rewrite EQ10. rewrite <- EQ42. apply H6.
       rewrite EQ35. reflexivity.
Qed.

Axiom excluded_middle : forall (P : Prop),
  P \/ ~ P.

Lemma ex_ho_join_v_or_not : forall f va1 va2,
   (exists va3, (ho_join_v f) va1 va2 va3)
   \/ (~ exists va3, (ho_join_v f) va1 va2 va3).
Proof.
  intros.
  apply excluded_middle.
Qed.

(*join functions on value annotations*)
Definition join_app_v := ho_join_v join_app_stat.

Theorem join_app_v_function : forall va1 va2 va va',
     join_app_v va1 va2 va ->
     join_app_v va1 va2 va' ->
     va = va'.
Proof.
  intros. 
  apply ho_join_v_keep_fun with (f:= join_app_stat)
                                (va1 := va1)
                                (va2 := va2).
  apply join_app_stat_function.
  apply H.
  apply H0.
Qed.

Definition join_case_v := ho_join_v join_case_stat.

Theorem join_case_v_function : forall va1 va2 va va', 
     join_case_v va1 va2 va ->
     join_case_v va1 va2 va' ->
     va = va'.
Proof.
  intros.
  apply ho_join_v_keep_fun with (f:= join_case_stat)
                                (va1 := va1)
                                (va2 := va2).
  apply join_case_stat_function.
  apply H.
  apply H0.
Qed.

Definition join_op_v (o:op) : vann -> vann -> vann -> Prop :=
     ho_join_v (an_rel o).

Theorem join_op_v_function : forall o va1 va2 va va',
     join_op_v o va1 va2 va ->
     join_op_v o va1 va2 va' ->
     va = va'.
Proof.
  intros.
  apply ho_join_v_keep_fun with (f := (an_rel o))
                                (va1 := va1)
                                (va2 := va2).
  apply an_rel_function.
  apply H.
  apply H0.
Qed.


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
| dlnl : eterm -> vann -> eterm (*lnl e va*)
| dlnr : eterm -> vann -> eterm (*lnr e va*)
.


Inductive value : eterm -> Prop :=
| baseval : forall b va, value (dbase b va)
| abstrval : forall i va e, value (dabstr i e va)
| lnlval : forall e va, value e 
                           -> value (dlnl e va)
| lnrval : forall e va, value e
                           -> value (dlnr e va)
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
| vc_lnl : forall a va1 ta1 va2 ta2 e t1a t1b t2a t2b p,
  vtann_compatible a va1 ta1 ->
  vtann_compatible a va2 ta2 ->
  vcast (dlnl e va1) (tann (tsum t1a t1b) ta1) (tann (tsum t2a t2b) ta2)
      (dlnl (ecast e t1a t2a p) va2) p
| vc_lnr : forall a va1 ta1 va2 ta2 e t1a t1b t2a t2b p,
  vtann_compatible a va1 ta1 ->
  vtann_compatible a va2 ta2 ->
  vcast (dlnr e va1) (tann (tsum t1a t1b) ta1) (tann (tsum t2a t2b) ta2)
      (dlnr (ecast e t1b t2b p) va2) p
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
   | dlnl e' va => dlnl (ssubst e' i e2) va
   | dlnr e' va  => dlnr (ssubst e' i e2) va
   end.

Inductive smallstep : eterm -> eterm -> Prop :=
| ss_beta : forall i e1 e2 va,
  value e2 ->
  smallstep (eappl (dabstr i e1 va) e2)
            (eguard join_app_v va (ssubst e1 i e2))
| ss_case_lnl : forall i j e e1 e2 va,
  value e ->
  smallstep (ecase (dlnl e va) i e1 j e2)
            (eguard join_case_v va (ssubst e1 i e))
| ss_case_lnr : forall i j e e1 e2 va,
  value e ->
  smallstep (ecase (dlnr e va) i e1 j e2)
            (eguard join_case_v va (ssubst e2 j e))
| ss_guard_base : forall (f:vann -> vann -> vann -> Prop) b va va1 va2,
  f va1 va2 va ->
  smallstep (eguard f va1 (dbase b va2))
            (dbase b va)
| ss_guard_abstr : forall (f:vann -> vann -> vann -> Prop) i e va va1 va2,
  f va1 va2 va ->
  smallstep (eguard f va1 (dabstr i e va2))
            (dabstr i e va)
| ss_guard_dlnl : forall (f: vann -> vann -> vann -> Prop) e va va1 va2,
  value e ->
  f va1 va2 va ->
  smallstep (eguard f va1 (dlnl e va2))
            (dlnl e va)
| ss_guard_dlnr : forall (f: vann -> vann -> vann -> Prop) e va va1 va2,
  value e ->
  f va1 va2 va ->
  smallstep (eguard f va1 (dlnr e va2))
            (dlnr e va)
| ss_prim : forall o b1 b2 b va1 va2 va,
  join_op_v o va1 va2 va ->
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
| ss_ctx_lnl : forall va e e',
  smallstep e e' ->
  smallstep (dlnl e va) (dlnl e' va)
| ss_ctx_lnr : forall va e e',
  smallstep e e' ->
  smallstep (dlnr e va) (dlnr e' va)
| ss_ctx5 : forall e e' t1 t2 p,
  smallstep e e' ->
  smallstep (ecast e t1 t2 p) (ecast e' t1 t2 p).

Lemma values_dont_reduce : forall e,
  value e -> ~ (exists e' , smallstep e e').
Proof.
  unfold not.
  intros.
  induction e; inversion H; subst; inversion H0; inversion H1.
  (* value dlnl *)
  apply IHe. apply H2.
    exists e'. apply H6.
  (* value dlnr *)
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
| ty_guard : forall te e s va' ta ta' ta'' f,
  typing te e (tann s ta'') ->
  ((ho_join_t f) ta' ta'' ta) ->
  vtann_compatible2 va' ta' -> (*TODO really?*)
  typing te (eguard (ho_join_v f) va' e) (tann s ta) (*RC-T-GUARD*)
| ty_inl : forall va ta te e t1 t2,
  vtann_compatible2 va ta ->
  typing te e t1 ->
  typing te (dlnl e va) (tann (tsum t1 t2) ta) (*RC-T-INL*)
| ty_inr : forall va ta te e t1 t2,
  vtann_compatible2 va ta ->
  typing te e t2 ->
  typing te (dlnr e va) (tann (tsum t1 t2) ta) (*RC-T-INR*)
| ty_op : forall te e1 e2 ta1 ta2 ta o,
  typing te e1 (tann tbase ta1) ->
  typing te e2 (tann tbase ta2) ->
  join_op_t o ta1 ta2 ta ->
  typing te (eop o e1 e2) (tann tbase ta) (*RC-T-OP*)
| ty_app : forall te e1 e2 s t2 ta ta1 ta2,
  typing te e1 (tann (tfun t2 (tann s ta1)) ta) ->
  typing te e2 t2 ->
  join_app_t ta ta1 ta2 ->
  typing te (eappl e1 e2) (tann s ta2) (*RC-T-APP*)
| ty_case : forall te e e1 e2 i j t1 t2 s ta ta1 ta2,
  typing te e (tann (tsum t1 t2) ta1) ->
  typing (extend te i t1) e1 (tann s ta) ->
  typing (extend te j t2) e2 (tann s ta) ->
  join_case_t ta1 ta ta2 -> (*TODO argument order*)
  typing te (ecase e i e1 j e2) (tann s ta2) (*RC-T-CASE*)
| ty_cast : forall te e t1 t2 p,
  typing te e t1 ->
  compatible t1 t2 ->
  typing te (ecast e t1 t2 p) t2 (*RC-T-CAST*)
.


Inductive stuckterm : eterm -> Prop := (*TODO this might work, but don't be to sure about it*)
| fc_base : forall n t a a' p,
  a <> a' ->
  stuckterm (ecast (dbase n (vd a)) t (tann tbase (taan a')) p)
| fc_op1 : forall o a1 a2 b1 b2,
  (~ exists a0, an_rel o a1 a2 a0) -> 
  stuckterm (eop o (dbase b1 (vd a1)) (dbase b2 (vd a2)))
| fc_op2 : forall  o a1 a2 b1 b2,
  (exists a0, an_rel o a1 a2 a0) ->
  (~ exists b0, b_rel o b1 b2 b0 )->
  stuckterm (eop o (dbase b1 (vs a1)) (dbase b2 (vs a2)))
| fc_op3 : forall  o a1 a2 b1 b2,
  (exists a0, an_rel o a1 a2 a0) ->
  (~ exists b0, b_rel o b1 b2 b0 )->
  stuckterm (eop o (dbase b1 (vd a1)) (dbase b2 (vd a2)))
| fc_guard_base : forall a1 a2 f b,
  ~(exists va, f (vd a1) (vd a2) va) ->
  stuckterm (eguard f (vd a1) (dbase b (vd a2)))
| fc_guard_abstr : forall a1 a2 f i e,
  ~(exists va, f (vd a1) (vd a2) va) ->
  stuckterm (eguard f (vd a1) (dabstr i e (vd a2)))
| fc_guard_lnl : forall a1 a2 f e,
  ~(exists va, f (vd a1) (vd a2) va) ->
  stuckterm (eguard f (vd a1) (dlnl e (vd a2)))
| fc_guard_lnr : forall a1 a2 f e,
  ~(exists va, f (vd a1) (vd a2) va) ->
  stuckterm (eguard f (vd a1) (dlnr e (vd a2)))
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
| fc_lnl : forall e va, 
  stuckterm e ->
  stuckterm (dlnl e va)
| fc_lnr : forall e va, 
  stuckterm e ->
  stuckterm (dlnr e va)
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
    assert (a0 = a1).
      inversion H1. reflexivity.
    assert (a2 = a3).
      inversion H. inversion H7. reflexivity.
    subst.
    right. left.
    exists (dbase b (vs a)). apply ss_guard_base.
    apply ho_join_v_static. apply H3.

    inversion H. inversion H6.
    destruct v.
    inversion H.  
    inversion H1.

    inversion H1.

    destruct v.
    inversion H. inversion H5.
    destruct va'.
    destruct H0.
    inversion H. inversion H5.

    inversion H1.

    (* seems to need excluded middle from here...*)
    assert ((exists va, (ho_join_v f) (vd a0) (vd a) va) 
            \/ (~ exists va, (ho_join_v f) (vd a0) (vd a) va)).
      apply ex_ho_join_v_or_not.
    destruct H3. destruct H3.
    right. left.
    exists (dbase b x).
    apply ss_guard_base. apply H3.
    unfold not in H3.
    right. right. 
    apply fc_guard_base with (a1:=a0) (a2:=a). unfold not. apply H3.
    (* .... to here*)

    (*eguard ... dabstr ... *)
    destruct va'; destruct v.
    right. left. 
    exists (dabstr i e (vs a)).
    apply ss_guard_abstr. apply ho_join_v_static.
    assert (a1 = a0).
      inversion H1. reflexivity.
    assert (a2 = a3).
      inversion H. inversion H8. reflexivity.
    subst. apply H3.

    inversion H. inversion H7.
    inversion H1.

    inversion H1.
    destruct va'; destruct v.
    inversion H. inversion H6.

    inversion H1.

    inversion H. inversion H6.

    (* needs excluded middle from here...*)
    assert ((exists va, (ho_join_v f) (vd a) (vd a0) va)
             \/ (~exists va, (ho_join_v f) (vd a) (vd a0) va)).
      apply ex_ho_join_v_or_not.
    destruct H3.
    right. left. destruct H3.
    exists (dabstr i e x).
    apply ss_guard_abstr. apply H3.

    right. right.
    apply fc_guard_abstr. apply H3.
    (*... to here *)

    (*eguard ... dlnl*)
    destruct va'; destruct v.
    assert (a0 = a1).
      inversion H1. reflexivity.
    assert (a3 = a2).
      inversion H. inversion H10. reflexivity.
    subst.
    right. left.
    inversion H0. subst.
    exists (dlnl e (vs a)).
    apply ss_guard_dlnl. apply H9.

    apply ho_join_v_static. apply H8.
    inversion H. inversion H8.

    inversion H1.

    inversion H. inversion H8.

    destruct va'; destruct v.
    inversion H. inversion H7.

    inversion H1.

    inversion H. inversion H7.

    (* needs excluded middle from here...*)
    assert ((exists va, (ho_join_v f) (vd a) (vd a0) va)
             \/ ( ~ exists va, (ho_join_v f) (vd a) (vd a0) va)).
      apply ex_ho_join_v_or_not.
    destruct H3.
    right. left. destruct H3.
    exists (dlnl e x).
    apply ss_guard_dlnl.
    apply H8.

    apply H3.

    right. right.
    apply fc_guard_lnl. apply H3.

    (*... to here *)
    (*eguard ... dlnr *)
    destruct va'; destruct v.
    assert (a0 = a1).
      inversion H1. reflexivity.
    assert (a3 = a2).
      inversion H. inversion H10. reflexivity.
    subst.
    right. left.
    inversion H0. subst.
    exists (dlnr e (vs a)).
    apply ss_guard_dlnr. apply H9.

    apply ho_join_v_static. apply H8.

    inversion H. inversion H8.

    inversion H1.

    inversion H. inversion H8.

    destruct va'; destruct v.
    inversion H1.

    inversion H. inversion H7.
    inversion H1.

    inversion H. inversion H7.

    (* needs excluded middle from here...*)
    assert ((exists va, (ho_join_v f) (vd a) (vd a0) va)
            \/ (~ exists va, (ho_join_v f) (vd a) (vd a0) va)).
      apply ex_ho_join_v_or_not.
    destruct H3.
    right. left. destruct H3.
    exists (dlnr e x).
    apply ss_guard_dlnr.
    apply H8.
    apply H3.

    right. right.
    apply fc_guard_lnr. apply H3.
    (*... to here*)

    (* eguard join va' e*)
    right. destruct H2.
    left. destruct H2.
    exists (eguard (ho_join_v f) va' x).
    apply ss_ctx_guard. apply H2.

    right. apply fc_guard. apply H2.
  (*dlnl*)
  destruct IHtyping.
  reflexivity.
  left. constructor. apply H1.

  destruct H1.
  right. left. destruct H1.
  exists (dlnl x va). constructor. apply H1.

  right. right. constructor. apply H1.

  (*dlnr*)
  destruct IHtyping.
  reflexivity.
  left. constructor. apply H1.

  destruct H1.
  right. left. destruct H1.
  exists (dlnr x va). constructor. apply H1.

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
    inversion H9. rewrite <- H24 in H20. inversion H20.
                                         rewrite <- H12. rewrite <- H23.
                                         rewrite <- H26.
    inversion H15.
    (*case needs excluded middle from here..*)
    rewrite <- H27 in H21. inversion H21. rewrite <- H18. rewrite <- H25.
                                          rewrite <- H29. 
    assert ((exists b1, b_rel o b b0 b1) \/ ~(exists b1, b_rel o b b0 b1)).
      apply excluded_middle.
    destruct H28. destruct H28.
    left. exists (dbase x (vs a)). constructor.
    constructor. apply H16.
    apply H28.

    right. apply fc_op2.
    exists a. apply H16.
    apply H28.
    (*to here*)

    rewrite <- H22 in H1. rewrite <- H24 in H1. rewrite <- H27 in H1.
    inversion H1.

    rewrite <- H24 in H20. inversion H20.

    inversion H9.
    rewrite <- H23 in H19. inversion H19.

    inversion H15.
    rewrite <- H25 in H20. inversion H20.

    rewrite <- H12. rewrite <- H18.
    rewrite <- H22. rewrite <- H24.

    (*case needs excluded middle from here...*)
    assert ((exists a, join_op_v o (vd ann0) (vd ann1) a) \/
             (~exists a, join_op_v o (vd ann0) (vd ann1) a)).
       apply excluded_middle.
    assert ((exists b1, b_rel o b b0 b1) \/
            (~exists b1, b_rel o b b0 b1)).
       apply excluded_middle.
    destruct H26. destruct H26.
    destruct H27. destruct H27.
    left.
    exists (dbase x0 x). constructor.
    apply H26. apply H27.

    right. apply fc_op3. inversion H26. exists a3. apply H31.
    apply H27.

    right. apply fc_op1 with (a1:=ann0) (a2:=ann1).
    unfold not. intros. unfold not in H26.
    apply H26. destruct H28.
    exists (vd x). constructor. apply H28.
    (*... to here*)
    
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

  left. exists (eguard (join_app_v 

   

    

    
