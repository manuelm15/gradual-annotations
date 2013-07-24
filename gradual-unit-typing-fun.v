Require Export SfLib.
Require Export QArith_base.

(*
Inductive op : Set := 
| add : op
| sub : op
| mul : op
| div : op
.*)

Inductive ann : Set :=
| anon : ann
| acst : id -> ann
| aprm : op -> ann -> ann -> ann

. 
(*TODO is this really enough? 
shouldn't function annotations be handled somehow like
| apfun : ann -> ann -> ann?*)

Inductive tyann : Set :=
| taan : ann -> tyann
| tadyn : tyann (* the question mark...*)
.

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
(*make this a proposition*)

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




