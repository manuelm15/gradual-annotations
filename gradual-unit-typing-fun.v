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

(* lift join functions to gradual annotations*)
Inductive ho_join : (ann -> ann -> ann -> Prop)
   -> tyann -> tyann -> tyann -> Prop :=
   | ho_join_static : 
       forall (f: (ann -> ann -> ann -> Prop)) a1 a2 a, 
       f a1 a2 a -> ho_join f (taan a1) (taan a2) (taan a)
   | ho_join_dynamic : forall f, ho_join f tadyn tadyn tadyn.

(*if ho_join is applied to a function, the result is a function*)
Lemma ho_join_keep_fun : forall (f: ann -> ann -> ann -> Prop) 
    ta1 ta2 ta ta',
   (forall a1 a2 a a', f a1 a2 a -> f a1 a2 a' -> a = a') ->
   (((ho_join f) ta1 ta2 ta) -> ((ho_join f) ta1 ta2 ta')
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

Definition join_app := ho_join join_app_stat.

Theorem join_app_function : forall ta1 ta2 ta ta',
          join_app ta1 ta2 ta ->
          join_app ta1 ta2 ta' ->
          ta = ta'.
Proof.
  intros ta1 ta2 ta ta'.
  apply ho_join_keep_fun.
  apply join_app_stat_function.
Qed.

Definition join_case := ho_join join_case_stat.

Theorem join_case_function : forall ta1 ta2 ta ta',
          join_case ta1 ta2 ta ->
          join_case ta1 ta2 ta' ->
          ta = ta'.
Proof.
  intros ta1 ta2 ta ta'.
  apply ho_join_keep_fun.
  apply join_case_stat_function.
Qed.

Definition join_op (o:op) : tyann -> tyann -> tyann -> Prop :=
   ho_join (an_rel o).

     
Theorem join_op_function : forall o ta1 ta2 ta ta',
          join_op o ta1 ta2 ta ->
          join_op o ta1 ta2 ta' ->
          ta = ta'.
Proof.
  intros.
  apply ho_join_keep_fun with (f:=(an_rel o)) (ta1:=ta1) (ta2:=ta2).
  apply an_rel_function.
  apply H.
  apply H0.
Qed.

Inductive type : Set :=
| tann : stype -> tyann -> type
with stype : Set :=
| tnum : stype
| tfun : type -> type -> stype
| tadd : type -> type -> stype
.

(*set of value annotations*)
Inductive vann : Set := 
| vs : ann -> vann 
| vd : ann -> vann
.

(*compability relation of value annotations and type annotations*)
(*relates D(a) to ? and S(a) to a*)
Inductive vannCompatTann : vann -> tyann -> Prop :=
| vcstat : forall ann, vannCompatTann (vs ann) (taan ann)
| vcdyn : forall ann, vannCompatTann (vd ann)  tadyn
.

Inductive eterm : Set :=
| etermd : dterm -> vann -> eterm
| evar : id -> eterm
| eop : op -> eterm -> eterm -> eterm
| eappl : eterm -> eterm -> eterm
| ecase : eterm -> id -> eterm -> id -> eterm -> eterm
with dterm : Set :=
| dbase : B -> dterm
| dabstr : id -> eterm -> dterm
| dlnl : eterm -> dterm
| dlnr : eterm -> dterm
.
(*TODO cast still missing*)
(*TODO guard*)

Inductive value : Set :=
| valuew : wvalue -> vann -> value
with wvalue : Set :=
| wbase : B -> wvalue 
| wabstr : id -> eterm -> wvalue
| wlnl : value -> wvalue
| wlnr : value -> wvalue
.
(*make this a proposition ?*)

(*would look like this*)
Inductive value' : eterm -> Prop :=
| baseval : forall b va, value' (etermd (dbase b) va)
| abstrval : forall i va e, value' (etermd (dabstr i e) va)
| lnlval : forall e va, value' e 
                           -> value' (etermd (dlnl e) va)
| lnrval : forall e va, value' e
                           -> value' (etermd (dlnr e) va)
.

(* use evaluation context? kind of problematic, because 
distinct "case"...*)
Inductive evc : Set :=
| evcempty : evc
| evcappl : evc -> eterm -> evc
| evcvalappl : value -> evc -> evc
| evccase : evc -> id -> eterm -> id -> eterm -> evc
| evclnl : evc -> evc
| evclnr : evc -> evc
.

(* substitution function *)
Fixpoint ssubst (e1 : eterm) (i : id) (e2 : eterm) :=
   match e1 with
   | etermd d va => etermd (ssubstd d i e2) va
   | evar j => if beq_id i j then e2 else evar j
   | eop o ea eb => eop o (ssubst ea i e2) (ssubst eb i e2)
   | eappl ea eb => eappl (ssubst ea i e2) (ssubst eb i e2)
   | ecase ea j eb k ec => ecase (ssubst ea i e2)
                                 j (if beq_id i j then eb
                                           else (ssubst eb i e2))
                                 k (if beq_id i k then ec
                                           else (ssubst ec i e2))
   end
   with ssubstd (d : dterm) (i : id) (e : eterm) :=
   match d with
   | dbase b => dbase b
   | dabstr j e' => if beq_id i j then dabstr j e' else
                                                dabstr j (ssubst e' i e)
   | dlnl e' => dlnl (ssubst e' i e)
   | dlnr e' => dlnr (ssubst e' i e)
   end. 
   
(*TODO cast*)

