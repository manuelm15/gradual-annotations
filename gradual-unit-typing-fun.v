Require Export SfLib.
Require Export QArith_base.

(*
Inductive op : Set := 
| add : op
| sub : op
| mul : op
| div : op
.*)

Variable op : Set. (*there is some set off operations on base types,
this will be lifted to the annotation algebra *)

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

Inductive tyann : Set :=
| taan : ann -> tyann
| tadyn : tyann (* the question mark...*)
.

(*join function for type annotations and operations, lifted from an_rel*)
Inductive join_op : op -> tyann -> tyann -> tyann -> Prop:=
| join_op_static : forall o a1 a2 a3,
                  an_rel o a1 a2 a3 ->
                  join_op o (taan a1) (taan a2) (taan a3)
| join_op_dynamic : forall o, join_op o tadyn tadyn tadyn.

Theorem join_op_function : forall o ta1 ta2 ta ta',
          join_op o ta1 ta2 ta ->
          join_op o ta1 ta2 ta' ->
          ta = ta'.
Proof.
  intros o ta1 ta2 ta ta' H1 H2.
  inversion H1.
    inversion H2.
      assert (a0 = a1).
        rewrite <- H8 in H3.
        inversion H3. reflexivity.
      rewrite H11 in H6.
      assert (a4 = a2).

(*join function for function application, somewhat
 similar to join function on operations...*)
Variable join_app_stat : tyann -> tyann -> tyann -> Prop.


Inductive type : Set :=
| tann : stype -> tyann -> type
with stype : Set :=
| tnum : stype
| tfun : type -> type -> stype
| tadd : type -> type -> stype
.

Inductive vann : Set := 
| vs : ann -> vann
| vd : ann -> vann
.

Inductive eterm : Set :=
| etermd : dterm -> vann -> eterm
| evar : id -> eterm
| eop : op -> eterm -> eterm -> eterm
| eappl : eterm -> eterm -> eterm
| ecase : eterm -> id -> eterm -> id -> eterm -> eterm
with dterm : Set :=
| dbase : Q -> dterm (*should this really be Q? Probably not necessary *)
| dabstr : id -> eterm -> dterm
| dlnl : eterm -> dterm
| dlnr : eterm -> dterm
.

Inductive value : Set :=
| valuew : wvalue -> vann -> value
with wvalue : Set :=
| wbase : Q -> wvalue 
| wabstr : id -> eterm -> wvalue
| wlnl : value -> wvalue
| wlnr : value -> wvalue
.
(*make this a proposition ?*)

Inductive evc : Set :=
| evcempty : evc
| evcappl : evc -> eterm -> evc
| evcvalappl : value -> evc -> evc
| evccase : evc -> id -> eterm -> id -> eterm -> evc
| evcinl : evc -> evc
| evcinr : evc -> evc
. (* make this a proposition?*)


(*compability relation of value annotations and type annotations*)
(*relates D(a) to ? and S(a) to a*)
Inductive vannCompatTann : vann -> tyann -> Prop :=
| vcstat : forall ann, vannCompatTann (vs ann) (taan ann)
| vcdyn : forall ann, vannCompatTann (vd ann)  tadyn
.


