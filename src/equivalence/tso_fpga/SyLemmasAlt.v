
Require Import SyEvents.
Require Import SyExecution.
Require Import SyLabels.
Require Import TSOFPGA.
Require Import Lia.
Require Import Arith.
Require Import IndefiniteDescription.
Require Import PropExtensionality.
Require Import List.
Require Import AuxProp.
Require Import AuxRel.
From hahn Require Import Hahn.

Section SyLemmasAlt.


Lemma match_evE x y :
  match_ev x y <-> is_external y /\ x = proj_ev y.
Proof using.
  split; ins; desf.
  destruct H; desf.
  destruct y; vauto. destruct e; vauto. 
Qed.

Definition myco t x y :=
  (⟪ INITx : is_init x ⟫ /\
   exists yl,
     ⟪ My : match_ev y yl ⟫ /\
     ⟪ ELy : trace_elems t yl ⟫ /\
     ⟪ Wy : is_w y ⟫ /\
     ⟪ LOC : loc x = loc y ⟫) \/
  (exists xl,
     ⟪ Mx : match_ev x xl ⟫ /\
     ⟪ ELx : trace_elems t xl ⟫ /\
     ⟪ Wx : is_w x ⟫ /\
     exists yl,
       ⟪ My : match_ev y yl ⟫ /\
       ⟪ ELy : trace_elems t yl ⟫ /\
       ⟪ Wy : is_w y ⟫ /\
       ⟪ LOC : loc x = loc y ⟫ /\
       ⟪ TS : write_ts xl < write_ts yl ⟫).

End SyLemmasAlt.