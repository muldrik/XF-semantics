Require Import SyLabels.
From hahn Require Import Hahn. 
Require Import Lia.
Section SyEvents.

(* req + resp объединить *)

Inductive FPGAEvent :=
  | Fpga_write_req (c:Chan) (x:Loc) (v:Val)
  | Fpga_read_req (c:Chan) (x:Loc)
  | Fpga_fence_req_one (c: Chan)
  | Fpga_fence_req_all
  | Fpga_write_resp (c:Chan) (x:Loc) (v:Val)
  | Fpga_read_resp (c:Chan) (x:Loc) (v:Val)
  | Fpga_fence_resp_one (c: Chan)
  | Fpga_fence_resp_all.

Inductive CPUEvent := 
(*   | Askip  *)
  | Cpu_load  (x:Loc) (v:Val)
  | Cpu_store (x:Loc) (v:Val)
  | Cpu_fence.

Inductive Event :=
  | ThreadEvent (thread: nat) (index: nat) (e: CPUEvent)
  | FpgaEvent (e: FPGAEvent) (index: nat) (m: Mdata)
  | InitEvent (x : SyLabels.Loc).

Definition fpga_chan_opt (e: FPGAEvent) :=
  match e with
  | Fpga_write_req c _ _ => Some c
  | Fpga_read_req c _ => Some c
  | Fpga_fence_req_one c => Some c
  | Fpga_write_resp c _ _ => Some c
  | Fpga_read_resp c _ _ => Some c
  | Fpga_fence_resp_one c => Some c
  | Fpga_fence_req_all => None
  | Fpga_fence_resp_all => None
  end.

Definition chan_opt (e: Event) :=
  match e with
  | ThreadEvent _ _ _ => None
  | FpgaEvent e _ _ => fpga_chan_opt e
  | InitEvent _ => None
end.

Definition tid (e: Event) : Tid :=
  match e with
  | ThreadEvent t _ _ => CpuTid t
  | FpgaEvent _ _ _ => FpgaTid
  | InitEvent _ => InitTid
  end. 

Definition loc (e: Event) := match e with
  | ThreadEvent _ _ (Cpu_load x _) => x
  | ThreadEvent _ _ (Cpu_store x _) => x
  | ThreadEvent _ _ Cpu_fence => 0
  | FpgaEvent (Fpga_write_req _ x _) _ _ => x
  | FpgaEvent (Fpga_read_req _ x) _ _ => x
  | FpgaEvent (Fpga_write_resp _ x _) _ _ => x
  | FpgaEvent (Fpga_read_resp _ x _) _ _ => x
  | FpgaEvent (Fpga_fence_req_one _) _ _ => 0
  | FpgaEvent (Fpga_fence_req_all) _ _ => 0
  | FpgaEvent (Fpga_fence_resp_one _) _ _ => 0
  | FpgaEvent (Fpga_fence_resp_all) _ _ => 0
  | InitEvent l => l
  end.

Definition valr (e: Event) := match e with
  | ThreadEvent _ _ (Cpu_load _ v) => v
  | ThreadEvent _ _ (Cpu_store _ _) => 0
  | ThreadEvent _ _ Cpu_fence => 0
  | FpgaEvent (Fpga_write_req _ _ v) _ _ => 0
  | FpgaEvent (Fpga_read_req _ _) _ _ => 0
  | FpgaEvent (Fpga_write_resp _ _ _) _ _ => 0
  | FpgaEvent (Fpga_read_resp _ _ v) _ _ => v
  | FpgaEvent (Fpga_fence_req_one _) _ _ => 0
  | FpgaEvent (Fpga_fence_req_all) _ _ => 0
  | FpgaEvent (Fpga_fence_resp_one _) _ _ => 0
  | FpgaEvent (Fpga_fence_resp_all) _ _ => 0
  | InitEvent _ => 0
  end.

Definition valw (e: Event) := match e with
  | ThreadEvent _ _ (Cpu_load _ _) => 0
  | ThreadEvent _ _ (Cpu_store _ v) => v
  | ThreadEvent _ _ Cpu_fence => 0
  | FpgaEvent (Fpga_write_req _ _ v) _ _ => v
  | FpgaEvent (Fpga_read_req _ _) _ _ => 0
  | FpgaEvent (Fpga_write_resp _ _ v) _ _ => v
  | FpgaEvent (Fpga_read_resp _ _ _) _ _ => 0
  | FpgaEvent (Fpga_fence_req_one _) _ _ => 0
  | FpgaEvent (Fpga_fence_req_all) _ _ => 0
  | FpgaEvent (Fpga_fence_resp_one _) _ _ => 0
  | FpgaEvent (Fpga_fence_resp_all) _ _ => 0
  | InitEvent _ => 0
  end.

Definition index(e: Event) := match e with
  | ThreadEvent _ i _ => i
  | FpgaEvent _ i _ => i
  | InitEvent _ => 0
end.

Definition meta (e: Event) := match e with
  | ThreadEvent _ _ _ => 0
  | FpgaEvent _ _ m => m
  | InitEvent _ => 0
  end.


Definition is_wr_req (e: Event) :=
  match e with
  | FpgaEvent (Fpga_write_req _ _ _) _ _ => True
  | _ => False
end.

Definition is_wr_resp (e: Event) :=
  match e with
  | FpgaEvent (Fpga_write_resp _ _ _) _ _ => True
  | _ => False
end.

Definition is_rd_req (e: Event) :=
  match e with
  | FpgaEvent (Fpga_read_req _ _) _ _ => True
  | _ => False
end.

Definition is_rd_resp (e: Event) := 
  match e with
  | FpgaEvent (Fpga_read_resp _ _ _) _ _ => True
  | _ => False
end.

Definition is_fence_req_one (e: Event) :=
  match e with
  | FpgaEvent (Fpga_fence_req_one _) _ _ => True
  | _ => False
end.

Definition is_fence_resp_one (e: Event) :=
  match e with
  | FpgaEvent (Fpga_fence_resp_one _) _ _ => True
  | _ => False
end.

Definition is_fence_req_all (e: Event) := 
  match e with
  | FpgaEvent (Fpga_fence_req_all) _ _ => True
  | _ => False
end.

Definition is_fence_resp_all (e: Event) :=
  match e with
  | FpgaEvent (Fpga_fence_resp_all) _ _ => True
  | _ => False
end.

Definition is_cpu_wr (e: Event) :=
  match e with
  | ThreadEvent _ _ (Cpu_store _ _) => True
  | _ => False
end.

Definition is_cpu_rd (e: Event) :=
  match e with
  | ThreadEvent _ _ (Cpu_load _ _) => True
  | _ => False
end.

Definition is_cpu_fence (e: Event) :=
  match e with
  | ThreadEvent _ _ (Cpu_fence) => True
  | _ => False
end.

Definition is_init e := 
  match e with
    | InitEvent _ => True
    | _ => False
  end.

Definition is_cpu e := 
  match e with
    | ThreadEvent _ _ _ => True
    | _ => False
  end.

Definition is_fpga e : Prop := 
  match e with
    | FpgaEvent _ _ _ => True
    | _ => False
end.

Definition is_w e : Prop :=
  match e with
  | ThreadEvent _ _ (Cpu_store _ _) => True
  | FpgaEvent (Fpga_write_resp _ _ _) _ _ => True
  | InitEvent _ => True
  | _ => False
end.

Definition is_r e : Prop :=
  match e with
  | ThreadEvent _ _ (Cpu_load _ _) => True
  | FpgaEvent (Fpga_read_resp _ _ _) _ _ => True
  | _ => False
end.

Definition is_req (e1 : Event) :=
  match e1 with
  | FpgaEvent (Fpga_write_req _ _ _) _ _ => True
  | FpgaEvent (Fpga_read_req _ _) _ _ => True
  | FpgaEvent (Fpga_fence_req_one _) _ _ => True
  | FpgaEvent (Fpga_fence_req_all) _ _ => True
  | _ => False
end.

Definition is_resp (e1 : Event) :=
  match e1 with
  | FpgaEvent (Fpga_write_resp _ _ _) _ _ => True
  | FpgaEvent (Fpga_read_resp _ _ _) _ _ => True
  | FpgaEvent (Fpga_fence_resp_one _) _ _ => True
  | FpgaEvent (Fpga_fence_resp_all) _ _ => True
  | _ => False
end.



Definition req_resp_pair (e1 e2: Event) :=
  match e1, e2 with
  | FpgaEvent (Fpga_write_req chan1 l1 v1) _ meta1, FpgaEvent (Fpga_write_resp chan2 l2 v2) _ meta2 => chan1 = chan2 /\ meta1 = meta2 /\ l1 = l2 /\ v1 = v2
  | FpgaEvent (Fpga_read_req chan1 _) _ meta1, FpgaEvent (Fpga_read_resp chan2 _ _) _ meta2 => chan1 = chan2 /\ meta1 = meta2
  | FpgaEvent (Fpga_fence_req_one chan1) _ meta1, FpgaEvent (Fpga_fence_resp_one chan2) _ meta2 => chan1 = chan2 /\ meta1 = meta2
  | FpgaEvent (Fpga_fence_req_all) _ meta1, FpgaEvent (Fpga_fence_resp_all) _ meta2 => meta1 = meta2
  | _, _ => False
  end.

(* Definition req_resp_pair (e1 e2 : Event) :=
  match e1, e2 with
  | EventLab (FpgaEvent (Fpga_read_req _ _) _ _), EventLab (FpgaEvent (Fpga_read_resp _ _ _) _ _) => True
  | EventLab (FpgaEvent (Fpga_write_req _ _ _) _ _), EventLab (FpgaEvent (Fpga_write_resp _) _ _) => True
  | EventLab (FpgaEvent (Fpga_fence_req_one _) _ _), EventLab (FpgaEvent (Fpga_fence_resp_one _) _ _) => True
  | EventLab (FpgaEvent (Fpga_fence_req_all) _ _), EventLab (FpgaEvent (Fpga_fence_resp_all) _ _) => True
  | _, _ => False
  end.

Definition is_req e := match e with
  | EventLab (FpgaEvent (Fpga_read_req _ _) _ _) => True
  | EventLab (FpgaEvent (Fpga_write_req _ _ _) _ _) => True
  | EventLab (FpgaEvent (Fpga_fence_req_one _) _ _) => True
  | EventLab (FpgaEvent (Fpga_fence_req_all) _ _) => True
  | _ => False
  end.

Definition meta_pair_unique :=
  same_meta_l ⊆ (is_pair)^?.


(* Для каждого запроса существует пара *)
Definition req_exists_resp :=
  forall e1, is_req e1 -> exists e2, is_pair e1 e2. *)


(* Lemma r_or_w a : is_r a \/ is_w a.
Proof using.
  unfold is_r, is_w. destruct (lab a); ins; auto.
Qed. *)

(******************************************************************************)
(** ** is_init properties *)
(******************************************************************************)
Lemma is_init_InitEvent x :
  is_init (InitEvent x).
Proof using.
  unfold is_init; auto.
Qed.

(******************************************************************************)
(* ** Same tid restriction *)
(******************************************************************************)

Definition is_tid i a : Prop := tid a = i.

Definition same_tid := (fun a b => tid a = tid b).

Definition ext_sb a b := 
  match a, b with
  | (ThreadEvent t i _), (ThreadEvent t' j _) => t = t' /\ i < j
  | (FpgaEvent _ i _), (FpgaEvent _ j _) => i < j
  | (InitEvent _), (ThreadEvent _ _ _) => True
  | (InitEvent _), (FpgaEvent _ _ _) => True
  | _, _ => False
end.


Lemma restr_eq_rel_same_tid r :  restr_eq_rel tid r  ≡ r ∩ same_tid.
Proof using. unfold same_tid.  basic_solver. Qed.

Lemma funeq_same_tid (r: relation Event) (H: funeq tid r):
 r ⊆ r ∩ same_tid.
Proof using.
unfold same_tid; basic_solver.
Qed.

Lemma same_tid_funeq (r: relation Event) (H: r ⊆ r ∩ same_tid):
 funeq tid r.
Proof using.
unfold same_tid; unfolder; firstorder.
Qed.

(******************************************************************************)
(** ** Same location restriction *)
(******************************************************************************)

Definition is_loc x a : Prop := loc a = x.

Definition same_loc := (fun x y => loc x = loc y).

Lemma restr_eq_rel_same_loc r :  restr_eq_rel loc r  ≡ r ∩ same_loc.
Proof using. unfold same_loc; basic_solver. Qed.

Lemma funeq_same_loc (r: relation Event) (H: funeq loc r):
 r ⊆ r ∩ same_loc.
Proof using.
unfold same_loc; basic_solver.
Qed.

Lemma same_loc_funeq (r: relation Event) (H: r ⊆ r ∩ same_loc):
 funeq loc r.
Proof using.
unfold same_loc; unfolder; firstorder.
Qed.

Lemma same_loc_trans : transitive same_loc.
Proof using. unfold same_loc; red; ins. by rewrite H. Qed.

Lemma same_loc_sym : symmetric same_loc.
Proof using. unfold same_loc; red; ins.
Qed.

(******************************************************************************)
(** ** Values and locations getters  *)
(******************************************************************************)

(* Lemma exists_valw a : exists vw, valw a = vw.
Proof using. unfold valw; desc; eexists; eauto. Qed.

Lemma exists_valr a : exists vw, valr a = vw.
Proof using. unfold valr; desc; eexists; eauto. Qed.

Lemma exists_loc a : exists x, loc a = x.
Proof using. unfold loc; desc; eexists; eauto. Qed. *)


(******************************************************************************)
(** ** Sequenced-Before *)
(******************************************************************************)

Definition same_index := (fun x y => index x = index y).

(* Definition ext_sb a b := 
  match a, b with
  | (ThreadEvent t i _), (ThreadEvent t' j _) => t = t' /\ i < j
  | (FpgaEvent _ i _), (FpgaEvent _ j _) => i < j
  | (InitEvent _), (ThreadEvent _ _ _) => True
  | (InitEvent _), (FpgaEvent _ _ _) => True
  | _, _ => False
end. *)

(* Definition same_index := (fun x y => index x = index y). *)


Lemma ext_sb_trans : transitive ext_sb.
Proof using.
unfold ext_sb; red; ins.
destruct x,y,z; ins; desf; splits; eauto; lia.
Qed.

Lemma ext_sb_irr : irreflexive ext_sb.
Proof using.
unfold ext_sb; red; ins.
destruct x; firstorder; lia.
Qed.

Lemma ext_sb_to_non_init : ext_sb ⊆ ext_sb ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
unfold is_init, ext_sb; basic_solver.
Qed.

Lemma ext_sb_semi_total_l x y z 
  (N: ~ is_init x) (NEQ: index y <> index z) (XY: ext_sb x y) (XZ: ext_sb x z): 
  ext_sb y z \/ ext_sb z y.
Proof using.
unfold ext_sb in *.
destruct x,y,z; ins; desf.
cut(index1 < index2 \/ index2 < index1).
tauto.
lia.
lia.
Qed.

Lemma ext_sb_semi_total_r x y z 
  (NEQ: index y <> index z) (XY: ext_sb y x) (XZ: ext_sb z x): 
  ext_sb y z \/ ext_sb z y.
Proof using.
unfold ext_sb in *.
destruct x,y,z; ins; desf; eauto.
cut(index1 < index2 \/ index2 < index1).
tauto.
lia. lia.
Qed.

Lemma ext_sb_tid_init x y (SB : ext_sb x y): tid x = tid y \/ is_init x.
Proof using.
unfold ext_sb in *; desf; ins; desf; eauto.
Qed.

Lemma ext_sb_tid_init': ext_sb ⊆ ext_sb ∩ same_tid ∪ ⦗is_init⦘ ⨾ ext_sb.
Proof using.
generalize ext_sb_tid_init; firstorder.
Qed.

Lemma tid_ext_sb: same_tid ⊆ same_tid ∩ same_index ∪ ext_sb ∪ ext_sb⁻¹ ∪ (is_init × is_init).
Proof using.
  unfold ext_sb, same_tid, same_index, tid, is_init, cross_rel; unfolder.
  ins; destruct x, y; desf; eauto.
  cut (index0 < index1 \/ index1 < index0 \/ index0 = index1).
  ins; desf; eauto 10.
  lia.
  cut (index0 < index1 \/ index1 < index0 \/ index0 = index1).
  ins; desf; eauto 10. lia.
Qed.

Lemma tid_n_init_ext_sb: same_tid ⨾ ⦗set_compl is_init⦘ ⊆ same_index ∪ ext_sb ∪ ext_sb⁻¹.
Proof using.
  rewrite tid_ext_sb at 1.
  unfold cross_rel.
  basic_solver 12.
Qed.

Lemma ext_sb_index x y (SB: ext_sb x y) (N: ~ is_init x): index x < index y.
Proof.
  unfold ext_sb in *; desf; ins; desf; eauto.
Qed.

(******************************************************************************)
(** ** Tactics *)
(******************************************************************************)



End SyEvents. 


#[global]
Hint Unfold set_union set_inter is_cpu_rd is_cpu_wr is_cpu_fence is_wr_req is_wr_resp is_fence_req_one is_fence_resp_one is_fence_req_all is_fence_resp_all is_rd_req is_rd_resp : type_unfolderDb.
(* #[global]
Hint Unfold is_r_l is_w_l is_rmw_l : type_unfolderDb.
Tactic Notation "type_unfolder" :=  repeat autounfold with type_unfolderDb in *.

Tactic Notation "type_solver" int_or_var(index) := 
  type_unfolder; basic_solver index.

Tactic Notation "type_solver" :=  type_solver 4. *)
