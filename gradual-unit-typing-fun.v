Require Export SfLib.
Require Export QArith_base.

Inductive op : Set := 
| add : op
| sub : op
| mul : op
| div : op
.

Inductive ann : Set :=
| anon : ann
| acst : id -> ann
| aprm : op -> ann -> ann -> ann
. 
(*TODO is this really enough? shouldn't abstraction be handled somehow?*)

Inductive tyann : Set :=
| taan : ann -> tyann
| tadyn : tyann
.

Inductive type : Set :=
| tann : stype -> tyann -> type
with stype : Set :=
| tnum : stype
| tfun : type -> type -> stype
| tadd : type -> type -> stype
.

Inductive eterm : Set :=
| etermd : dterm -> vann -> dterm
| evar : id -> eterm
| eop : op -> eterm -> eterm -> eterm
| eappl : eterm -> eterm -> eterm
| ecase : eterm -> id -> eterm -> id -> eterm -> eterm
with dterm
| dbase : Q -> dterm (*TODO should this really be Q?*)
| dabstr : id -> eterm -> dterm
| dlnl : eterm -> dterm
| dlnr : eterm -> dterm
.

Inductive value : Set :=
| valuew -> wvalue -> vann -> value
with wvalue
| wbase : Q (*TODO: again, should this really be Q?*)
| wabstr : id -> eterm -> wvalue
| wlnl : value -> wvalue
| wlnr : value -> wvalue
.

Inductive evc : Set :=
| evcempty : evc
| evcappl : evc -> eterm -> evc
| evcvalappl : value -> evc -> evc
| evccase : evc -> id -> eterm -> id -> eterm -> evc
| evcinl : evc -> evc
| evcinr : evc -> evc
.