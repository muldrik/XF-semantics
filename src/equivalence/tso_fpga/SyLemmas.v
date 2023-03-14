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

Section SyLemmas.

Variable tr: trace SyLabel.
Variable states: nat -> SyState. 

Definition LTS_trace_param {Label State}
           (lts : LTS State Label)
           (s : nat -> State) (t : trace Label)  :=
  match t with
  | trace_fin l =>
    LTS_init lts (s 0) /\
    forall i (LLEN : i < length l) d,
      LTS_step lts (s i) (nth i l d) (s (S i))
  | trace_inf fl =>
    LTS_init lts (s 0) /\
    forall i, LTS_step lts (s i) (fl i) (s (S i))
  end.

Hypothesis (TR: LTS_trace_param TSOFPGA_lts states tr). 
Hypothesis (WF: TSOFPGA_trace_wf tr). 
(* Hypothesis (FAIR: TSOFPGA_fair tr states). *)
Hypothesis (TSO_FAIR: TSO_fair tr states).

Definition Ecpu := fun e => trace_elems tr (EventLab e) /\ is_cpu e.
Definition Efpga := fun e => trace_elems tr (EventLab e) /\ is_fpga e.
Definition Eninit := fun e => trace_elems tr (EventLab e).
(* Hypothesis BOUNDED_THREADS: exists n, forall e, Eninit e -> tid e < n.
Hypothesis NO_TID1: forall e, is_cpu e -> tid e <> 1. *)
Hypothesis NO_TID0: forall e, is_cpu e -> tid e <> CpuTid 0. 

Definition EG := is_init ∪₁ Eninit.

Definition trace_labels := fun n => trace_nth n tr def_lbl. 

Definition trace_index : Event -> nat.
  intros e.
  destruct (excluded_middle_informative (Eninit e)).
  2: { exact 0. }
  red in e0. pose proof (@trace_in_nth _ tr (EventLab e) e0 def_lbl).
  apply constructive_indefinite_description in H. destruct H. exact x. 
Defined. 

Lemma not_same_tid_cpu_fpga e1 e2 (E1: is_cpu e1) (E2: is_fpga e2) (EQ: tid e1 = tid e2): False.
Proof.
  unfolder'.
  desf.
Qed.


Lemma ti_inj e1 e2 (E'1: Eninit e1) (E'2: Eninit e2) (EQ: trace_index e1 = trace_index e2):
  e1 = e2.
Proof.
  unfold trace_index in EQ.
  do 2 (destruct (excluded_middle_informative _); [| done]).
  do 2 (destruct (constructive_indefinite_description _ _); desc).
  subst x0. congruence. 
Qed. 

Lemma trace_index_simpl e (ENINIT: Eninit e):
  forall d, trace_nth (trace_index e) tr d = EventLab e.
Proof.
  ins. unfold trace_index. destruct (excluded_middle_informative _); [| done].
  destruct (constructive_indefinite_description _ _). desc.
  rewrite <- a0. by apply trace_nth_indep. 
Qed. 

Lemma nth_not_default_found x (l: list SyLabel) d (NOT_DEF: (nth x l d) <> d):
  x < length l.
Proof.
  generalize dependent x.
  induction l; ins.
  { unfold nth in NOT_DEF; desf. }
  simpl in NOT_DEF.
  destruct x.
  { simpl; lia. }
  remember (IHl x NOT_DEF); lia.
Qed.

Lemma not_default_found x (NOT_DEF: (trace_labels x) <> def_lbl): 
  NOmega.lt_nat_l x (trace_length tr).
Proof.
  unfold trace_labels in *.
  unfold trace_nth in *.
  destruct tr.
  2: vauto.
  unfold NOmega.lt_nat_l.
  unfold trace_length.
  apply nth_not_default_found in NOT_DEF; auto.
Qed.

Lemma trace_index_simpl' e (ENINIT: Eninit e):
  trace_labels (trace_index e) = EventLab e.
Proof.
  unfold trace_labels. apply trace_index_simpl; auto. 
Qed. 

Lemma TS0: LTS_init TSOFPGA_lts (states 0).
Proof. by apply LTS_trace_param' in TR as [H _]. Qed.

Lemma TSi i (DOM: NOmega.lt_nat_l i (trace_length tr)) d:
  LTS_step TSOFPGA_lts (states i) (trace_nth i tr d) (states (S i)).
Proof. apply LTS_trace_param' in TR as [_ H]. by apply H. Qed.

Lemma Eninit_non_init: is_init ∩₁ Eninit ≡₁ ∅.
Proof.
  split; [| basic_solver].
  red. intros e [INIT NINIT].
  destruct e; vauto. red in NINIT.
  apply trace_in_nth with (d := def_lbl) in NINIT. desc.
  pose proof (TSi n NINIT def_lbl). rewrite NINIT0 in H. inversion H.
Qed. 

Lemma write_cases x (W: is_w x) (ENINIT: Eninit x):
  is_cpu_wr x <-> ~is_wr_resp x.
Proof.
  split; ins.
  { destruct x; vauto. }
  { destruct x; vauto. by destruct (proj1 Eninit_non_init (InitEvent x)). }
Qed.

Lemma write_cases' x (W: is_w x) (ENINIT: Eninit x):
  ~is_cpu_wr x <-> is_wr_resp x.
Proof.
  split; ins.
  { destruct x; vauto. by destruct (proj1 Eninit_non_init (InitEvent x)). }
  { destruct x; vauto. }
Qed.

Definition trace_before := fun x y => trace_index x < trace_index y.
Lemma tb_respects_sb: ⦗Eninit⦘ ⨾ ext_sb ⨾ ⦗Eninit⦘ ≡ ⦗Eninit⦘ ⨾ (trace_before ∩ same_tid) ⨾ ⦗Eninit⦘. 
Proof.
  split.
  { rewrite seq_eqv_lr. red. ins. desc.
    apply seq_eqv_lr. splits; auto. 
    destruct x, y; vauto.
    3:  by destruct (proj1 Eninit_non_init (InitEvent x)).
    3:  by destruct (proj1 Eninit_non_init (InitEvent x)).

    { 
      simpl in H0. desc. split; auto. subst thread0.
      red. unfold trace_index.
      do 2 (destruct (excluded_middle_informative _); [| done]).
      do 2 (destruct (constructive_indefinite_description _ _); desc).
      pose proof (NPeano.Nat.lt_trichotomy x x0). des; auto.
      { subst. rewrite a2 in a0. inversion a0. lia. }
      destruct WF as [WF_cpu WF_fpga].
      forward eapply (@WF_cpu x0 x def_lbl thread index0 index e0 e); auto.
      lia.
      unfolder'. vauto.
    }
    {
      simpl in H0. desc. split; auto.
      red. unfold trace_index.
      do 2 (destruct (excluded_middle_informative _); [| done]).
      do 2 (destruct (constructive_indefinite_description _ _); desc).
      pose proof (NPeano.Nat.lt_trichotomy x x0). des; auto.
      { subst. rewrite a2 in a0. inversion a0. lia. }
      destruct WF as [WF_cpu WF_fpga].
      forward eapply (@WF_fpga x0 x def_lbl index0 index e0 e m0 m); auto.
      lia.
      red. unfold tid. auto.
    }
    }
  { red. ins. apply seq_eqv_lr in H. desc.
    apply seq_eqv_lr. splits; auto.
    destruct x. 
    3:{ by destruct (proj1 Eninit_non_init (InitEvent x)). }
    destruct y. 
    3:{ by destruct (proj1 Eninit_non_init (InitEvent x)). }
    {
    simpl. red in H0. desc. red in H2. simpl in H2.
    splits; vauto.
    red in H0. unfold trace_index in H0. 
    do 2 (destruct (excluded_middle_informative _); [| done]).
    do 2 (destruct (constructive_indefinite_description _ _); desc).
    destruct WF.
    eapply TSO_TR_WF; eauto.
    }
    red in H0. unfold trace_before in H0. unfold trace_index in H0.
    do 2 (destruct (excluded_middle_informative _); [| done]).
    do 2 (destruct (constructive_indefinite_description _ _); desc).
    unfold same_tid in H2.
    assert (is_cpu (ThreadEvent thread index e)). {
      by unfold is_cpu.
    }
    assert (is_fpga (FpgaEvent e0 index0 m)). {
      by unfold is_fpga.
     }
     {
     exfalso.
     eapply not_same_tid_cpu_fpga; eauto.
     }
     red in H0. desc. red in H2. simpl in H2.
     assert (is_fpga (FpgaEvent e index m)). {
        unfold is_fpga. auto.
     }
     destruct y.
     assert (is_cpu (ThreadEvent thread index0 e0)). {
        unfold is_cpu. auto.
     }
     eapply not_same_tid_cpu_fpga; eauto.
     unfold ext_sb.
     red in H0.
     unfold trace_index in H0.
    do 2 (destruct (excluded_middle_informative _); [| done]).
    do 2 (destruct (constructive_indefinite_description _ _); desc).
    destruct WF as [WF_cpu WF_fpga].
    eapply WF_fpga; eauto.
    unfold tid in H2.
    discriminate.
  }
Qed. 


Lemma tb_SPO: strict_total_order Eninit trace_before.
Proof.
  red. split.
  { unfold trace_before. split.
    all: red; ins; lia. }
  red. ins. unfold trace_before.
  pose proof (Nat.lt_trichotomy (trace_index a) (trace_index b)). des; auto.
  by apply ti_inj in H.
Qed.


Definition is_init' e :=
  match e with
  | InitEvent _ => true
  | ThreadEvent _ _ _ => false
  | FpgaEvent _ _ _ => false
  end.

(* Definition is_regular_write e := is_w e && negb (is_rmw e || is_init' e).  *)
(* (* Definition regular_write lbl := (is_w \₁ (is_rmw ∪₁ is_init)) (proj_ev lbl). *) *)
(* Definition regular_write (lbl: TSO_label) := *)
(*   match lbl with *)
(*   | inl e => is_regular_write e *)
(*   | _ => false *)
(*   end. *)
Definition count_upto S bound :=
  length (filterP S (map (fun i : nat => trace_nth i tr def_lbl) (List.seq 0 bound))).


Definition state_before_event e := states (trace_index e). 


Definition check {A: Type } S (elt: A) := length (ifP S elt then elt :: nil else nil).

Lemma check0 {A: Type } S (elt: A) (NS: ~ S elt): check S elt = 0.
Proof. unfold check. destruct (excluded_middle_informative (S elt)); vauto. Qed.  

Lemma check1 {A: Type } (S: A -> Prop) (elt: A) (SSS: S elt): check S elt = 1.
Proof. unfold check. destruct (excluded_middle_informative (S elt)); vauto. Qed.  

(* Definition G :=
  {| acts := EG;
     co := ⦗EG ∩₁ is_w⦘ ⨾ restr_eq_rel Events.loc vis_lt ⨾ ⦗EG ∩₁ is_w⦘;     
     rf := ⦗EG ∩₁ is_w⦘ ⨾ rf' ⨾ ⦗EG ∩₁ is_r⦘ |}. *)


Lemma buffer_same_transition st1 st2 lbl thread (STEP: TSOFPGA_step st1 lbl st2)
      (OTHER: lbl_thread lbl <> CpuTid thread):
  cpu_bufs (st1) thread = cpu_bufs (st2) thread. 
Proof.
  destruct st1 as [mem1 buf1]. destruct st2 as [mem2 buf2]. simpl.
  inversion STEP; vauto; simpl in OTHER. 
  all: rewrite updo; auto. 
Qed. 

Lemma upstream_same_transition st1 st2 lbl chan (STEP: TSOFPGA_step st1 lbl st2)
      (OTHER: lbl_chan_opt lbl <> Some chan):
  up_bufs (st1) chan = up_bufs (st2) chan.
Proof.
  destruct st1. destruct st2. simpl.
  inversion STEP; vauto; simpl in OTHER. 
  all: rewrite updo; auto.
Qed. 

Lemma downstream_same_transition st1 st2 lbl chan (STEP: TSOFPGA_step st1 lbl st2)
      (OTHER: lbl_chan_opt lbl <> Some chan):
  down_bufs (st1) chan = down_bufs (st2) chan.
Proof.
  destruct st1. destruct st2. simpl.
  inversion STEP; vauto; simpl in OTHER. 
  all: rewrite updo; auto.
Qed. 

Lemma ge_default i:
  trace_labels i = def_lbl <-> ~ (NOmega.lt_nat_l i (trace_length tr)).
Proof. 
  split.
  { red. intros DEF LT.
    pose proof TR as TR'. apply LTS_trace_param' in TR'. desc.
    specialize (TR'0 i LT def_lbl).
    unfold trace_labels in DEF.
    rewrite DEF in TR'0.
    inversion TR'0. }
  intros.
  unfold trace_labels, trace_nth.
  remember (trace_length tr) as tr_len.
  destruct tr.
  2: { simpl in Heqtr_len.
       exfalso. apply H. vauto. }
  unfold NOmega.lt_nat_l in H. rewrite Heqtr_len in H. simpl in H.
  rewrite nth_overflow; auto. lia.
Qed.

Lemma sim_subtraces_conv (C1 C2: SyLabel -> Prop)
           (LEN: trace_length (trace_filter C1 tr) = trace_length (trace_filter C2 tr)):
  forall i (C1i: C1 (trace_labels i))
    (DOMi: NOmega.lt_nat_l i (trace_length tr)),
  exists j, C2 (trace_labels j) /\
       NOmega.lt_nat_l j (trace_length tr) /\
       count_upto C1 i = count_upto C2 j.
Proof.
  ins.
  remember (trace_filter C1 tr) as tr1. remember (trace_filter C2 tr) as tr2.
  pose proof (trace_lt_length_filter i tr DOMi C1 def_lbl C1i).
  fold (count_upto C1 i) in H. remember (count_upto C1 i) as k.
  rewrite <- Heqtr1, LEN in H. pose proof H as DOM_TR2k. 
  rewrite Heqtr2 in H. apply trace_nth_filter with (d := def_lbl) in H.
  destruct H as [j [DOMj [FILTER_MATCH COUNT]]].
  exists j. splits; auto.
  unfold trace_labels. rewrite <- FILTER_MATCH.
  apply trace_nth_in with (d := def_lbl) in DOM_TR2k.
  rewrite Heqtr2 in DOM_TR2k. apply trace_in_filter in DOM_TR2k.
  by desc. 
Qed.

Lemma lt_nondefault i:
  trace_labels i <> def_lbl <-> NOmega.lt_nat_l i (trace_length tr).
Proof. 
  pose proof (ge_default i). apply not_iff_compat in H.
  eapply iff_trans; eauto. split; auto. apply NNPP.
Qed. 


Lemma NOmega_lt_trichotomy (x y: nat_omega): (NOmega.lt x y) \/ (NOmega.lt y x) \/ (x = y).
Proof.
  destruct x, y; vauto. simpl.
  pose proof (Nat.lt_trichotomy n n0). des; vauto.
Qed.

Ltac contra name :=
  match goal with
  | |- ?gl => destruct (classic gl) as [|name]; [auto|exfalso]
  end.

Lemma filter_ends {A: Type} (t: trace A) (S: A -> Prop) d
      (FIN: trace_length (trace_filter S t) <> NOinfinity):
  exists i, (NOmega.le (NOnum i) (trace_length t)) /\
       forall j (GE: j >= i) (DOM: NOmega.lt_nat_l j (trace_length t)),
         ~ S (trace_nth j t d).
Proof.
  unfold trace_filter in FIN. 
  destruct t.
  { simpl. exists (length l). split; [lia| ]. ins. lia. }
  destruct (excluded_middle_informative (set_finite (fl ↓₁ S))).
  2: { vauto. }
  pose proof s as s'. apply set_finite_nat_bounded in s'. desc.
  exists bound. split.
  { vauto. }
  ins. red. ins.
  specialize (s' j). specialize_full s'; [vauto| ]. 
  lia.
Qed. 

Lemma trace_split {A: Type} (t: trace A) k d
      (LE_LENGTH: NOmega.le (NOnum k) (trace_length t)):
  exists l t'', l = map (fun i => trace_nth i t d) (List.seq 0 k) /\
           t = trace_app (trace_fin l) t''. 
Proof.
  destruct t.
  { simpl in *. exists (firstn k l). exists (trace_fin (skipn k l)).
    splits.
    2: { by rewrite firstn_skipn. }
    replace k with (length (firstn k l)) at 2.
    2: { apply firstn_length_le. lia. }
    rewrite map_nth_seq with (d := d); auto.
    intros. rewrite Nat.add_0_l.
    rewrite <- (firstn_skipn k) at 1. rewrite app_nth1; auto. }
  simpl trace_nth. exists (map (fun i => fl i) (List.seq 0 k)).
  exists (trace_inf (fun n => fl (k + n))). splits; auto. simpl.
  unfold trace_prepend. rewrite map_length, seq_length.
  f_equal.

  exten.

  ins. destruct (Nat.ltb x k) eqn:LTB.
  { rewrite map_nth. rewrite seq_nth; vauto. by apply Nat.ltb_lt. }
  f_equal. rewrite <- le_plus_minus; auto. by apply Nat.ltb_ge in LTB.   
Qed. 

Lemma NOmega_add_le x y: NOmega.le (NOnum x) (NOmega.add (NOnum x) y).
Proof. destruct y; vauto. simpl. lia. Qed.
  
Lemma count_le_filter {A: Type} (t: trace A) (S: A -> Prop) bound d
  (LE_LENGTH: NOmega.le (NOnum bound) (trace_length t)):
  NOmega.le
    (NOnum (length (filterP S (map (fun i => trace_nth i t d) (List.seq 0 bound)))))
    (trace_length (trace_filter S t)).
Proof.
  pose proof (trace_split t bound d LE_LENGTH) as [l [t'' [MAP APP]]].
  rewrite <- MAP, APP.  
  rewrite trace_filter_app; [| vauto]. 
  rewrite trace_length_app. simpl trace_length. 
  apply NOmega_add_le.
Qed. 

Lemma count_upto_next i F:
  count_upto F (S i) = count_upto F i + check F (trace_labels i).
Proof.
  unfold count_upto. rewrite seqS, plus_O_n.
  by rewrite !map_app, !filterP_app, !length_app. 
Qed. 


Lemma count_upto_more i j F (LE: i <= j):
  count_upto F i <= count_upto F j. 
Proof.
  apply le_lt_eq_dec in LE. destruct LE as [LT | EQ]; [| subst; lia]. 
  apply lt_diff in LT. desc. subst. 
  unfold count_upto. rewrite seq_add.
  rewrite !map_app, !filterP_app, !length_app.
  lia. 
Qed. 

(* TODO: generalize, move to hahn? *)

Ltac liaW no := (destruct no; [done|simpl in *; lia]).

Lemma buffer_size_inv st1 st2 lbl thread (STEP: TSOFPGA_step st1 lbl st2):
length (cpu_bufs st1 thread) +
check (cpu_write' ∩₁ in_cpu_thread thread) lbl =
check (is_cpu_prop ∩₁ in_cpu_thread thread) lbl +
length (cpu_bufs st2 thread).
Proof.
destruct st1 as [mem1 buf1]. destruct st2 as [mem2 buf2]. simpl.
destruct (classic (lbl_thread lbl = CpuTid thread)) as [EQ | NEQ] .
2: { forward eapply buffer_same_transition as SAME_BUF; eauto. simpl in SAME_BUF.
      rewrite SAME_BUF. 
      repeat rewrite check0; [lia| |].
      all: apply set_compl_inter; right; vauto. }
inversion STEP; subst; simpl in EQ; inv EQ.
 all: try (repeat rewrite check0; [lia| |]; apply set_compl_inter; left; vauto).
{ rewrite check1.
  2: { unfolder'. simpl. intuition. }
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite upds. rewrite length_app. by simpl. }
{ rewrite upds. rewrite CPU_BUF. simpl.
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite check1; [| unfolder'; simpl; intuition].
  lia. }
Qed. 



Definition is_store_ups (upsE: (UpstreamEntry * Mdata)) :=
  match upsE with
  | ((store_up _ _), _) => true
  | _ => false
end.

Definition is_read_ups (upsE: (UpstreamEntry * Mdata)) :=
  match upsE with
  | ((read_up _), _) => true
  | _ => false
end.

Lemma upstream_size_inv_store st1 st2 lbl chan (STEP: TSOFPGA_step st1 lbl st2):
length (filter is_store_ups (up_bufs st1 chan)) +
check (fpga_write' ∩₁ in_chan chan) lbl =
check (is_fpga_prop ∩₁ in_chan chan) lbl +
length (filter is_store_ups (up_bufs st2 chan)).
Proof.
destruct st1 as [wp1 rp1 up_buf1 db1 shm1 cpu_b1]. destruct st2 as [wp2 rp2 up_buf2 db2 shm2 cpu_b2]. simpl.
destruct (classic (lbl_chan_opt lbl = Some chan)) as [EQ | NEQ] .
2: { forward eapply upstream_same_transition as SAME_BUF; eauto. simpl in SAME_BUF.
      rewrite SAME_BUF. 
      repeat rewrite check0; [lia| |].
      all: apply set_compl_inter; right; vauto. }
inversion STEP; subst; simpl in EQ; inv EQ.
 all: try (repeat rewrite check0; [lia| |]; apply set_compl_inter; left; vauto).
{ rewrite check1.
  2: { unfolder'. simpl. intuition. }
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite upds. rewrite filter_app. rewrite length_app. by simpl. }
{ rewrite upds. rewrite UPSTREAM. simpl.
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite check1; [| unfolder'; simpl; intuition].
  lia. }
{ rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite upds. rewrite filter_app. rewrite length_app. simpl.
  rewrite check0; [| unfolder'; simpl; intuition].
  lia.
}
{
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite UPSTREAM.
  rewrite upds. 
  simpl.
  lia.
}
Qed.


(* TODO: Delete *)
Lemma upstream_size_inv_read st1 st2 lbl chan (STEP: TSOFPGA_step st1 lbl st2):
length (down_bufs st1 chan) +
check (fpga_mem_read' ∩₁ in_chan chan) lbl =
check (fpga_read_resp' ∩₁ in_chan chan) lbl +
length (down_bufs st2 chan).
Proof.
destruct st1 as [wp1 rp1 up_buf1 db1 shm1 cpu_b1]. destruct st2 as [wp2 rp2 up_buf2 db2 shm2 cpu_b2]. simpl.
destruct (classic (lbl_chan_opt lbl = Some chan)) as [EQ | NEQ] .
2: { forward eapply downstream_same_transition as SAME_BUF; eauto. simpl in SAME_BUF.
      rewrite SAME_BUF. 
      repeat rewrite check0; [lia| |].
      all: apply set_compl_inter; right; vauto. }
inversion STEP; subst; simpl in EQ; inv EQ.
 all: try (repeat rewrite check0; [lia| |]; apply set_compl_inter; left; vauto).
{ rewrite check1.
  2: { unfolder'. simpl. intuition. }
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite upds. rewrite length_app. by simpl. }
{ rewrite upds. rewrite DOWNSTREAM. simpl.
  rewrite check0; [| unfolder'; simpl; intuition].
  rewrite check1; [| unfolder'; simpl; intuition].
  lia. }
Qed.

Lemma buffer_size_cpu thread i (DOM: NOmega.le (NOnum i) (trace_length tr)):
  count_upto (cpu_write' ∩₁ in_cpu_thread thread) i = count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) i + length (cpu_bufs (states i) thread).
Proof.
  induction i.
  { simpl. unfold count_upto. rewrite seq0. simpl.
    pose proof TS0 as TS0. simpl in TS0. by rewrite <- TS0. }
  remember (states (S i)) as s. simpl.
  unfold count_upto. rewrite !seqS, !Nat.add_0_l, !map_app, !filterP_app, !length_app. simpl.
  fold (count_upto (cpu_write' ∩₁ in_cpu_thread thread) i).
  fold (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) i).
  specialize_full IHi.
  { apply NOmega.le_trans with (m := NOnum (S i)); vauto. } 
  fold (check (cpu_write' ∩₁ in_cpu_thread thread) (trace_nth i tr def_lbl)). 
  fold (check (is_cpu_prop ∩₁ in_cpu_thread thread) (trace_nth i tr def_lbl)). 
  remember (states i) as st_prev.
  rewrite IHi.
  rewrite <- !Nat.add_assoc.
  f_equal. 

  simpl in IHi. 
  apply buffer_size_inv.
  forward eapply (TSi i) with (d := def_lbl) as TSi; vauto.
Qed. 


Lemma buffer_size_upstream_write chan i (DOM: NOmega.le (NOnum i) (trace_length tr)):
  count_upto (fpga_write' ∩₁ in_chan chan) i = 
  count_upto (is_fpga_prop ∩₁ in_chan chan) i + length (filter is_store_ups (up_bufs (states i) chan)).
Proof.
  induction i.
  { simpl. unfold count_upto. rewrite seq0. simpl.
    pose proof TS0 as TS0. simpl in TS0. by rewrite <- TS0. }
  remember (states (S i)) as s. simpl.
  unfold count_upto. rewrite !seqS, !Nat.add_0_l, !map_app, !filterP_app, !length_app. simpl.
  fold (count_upto (fpga_write' ∩₁ in_chan chan) i).
  fold (count_upto (is_fpga_prop ∩₁ in_chan chan) i).
  specialize_full IHi.
  { apply NOmega.le_trans with (m := NOnum (S i)); vauto. } 
  fold (check (fpga_write' ∩₁ in_chan chan) (trace_nth i tr def_lbl)). 
  fold (check (is_fpga_prop ∩₁ in_chan chan) (trace_nth i tr def_lbl)). 
  remember (states i) as st_prev.
  rewrite IHi.
  rewrite <- !Nat.add_assoc.
  f_equal. 

  simpl in IHi. 
  apply upstream_size_inv_store.
  forward eapply (TSi i) with (d := def_lbl) as TSi; vauto.
Qed.

Lemma buffer_size_downstream chan i (DOM: NOmega.le (NOnum i) (trace_length tr)):
  count_upto (fpga_read_resp' ∩₁ in_chan chan) i + length (down_bufs (states i) chan)= 
  count_upto (fpga_mem_read' ∩₁ in_chan chan) i .
Proof.
  induction i.
  { simpl. unfold count_upto. rewrite seq0. simpl.
    pose proof TS0 as TS0. simpl in TS0. by rewrite <- TS0. }
  remember (states (S i)) as s. simpl.
  unfold count_upto. rewrite !seqS, !Nat.add_0_l, !map_app, !filterP_app, !length_app. simpl.
  fold (count_upto (fpga_read_resp' ∩₁ in_chan chan) i).
  fold (count_upto (fpga_mem_read' ∩₁ in_chan chan) i).
  specialize_full IHi.
  { apply NOmega.le_trans with (m := NOnum (S i)); vauto. } 
  fold (check (fpga_read_resp' ∩₁ in_chan chan) (trace_nth i tr def_lbl)). 
  fold (check (fpga_mem_read' ∩₁ in_chan chan) (trace_nth i tr def_lbl)). 
  remember (states i) as st_prev.
  rewrite <- IHi.
  rewrite <- !Nat.add_assoc.
  f_equal. 

  simpl in IHi. 
  forward eapply upstream_size_inv_read; eauto.
  forward eapply (TSi i) with (d := def_lbl) as TSi; vauto.
Qed.


Lemma EXACT_CHAN_PROPS chan:
  trace_length (trace_filter (fpga_write' ∩₁ in_chan chan) tr) =
  trace_length (trace_filter (is_fpga_prop ∩₁ in_chan chan) tr).
Proof.
remember (trace_length (trace_filter (fpga_write' ∩₁ in_chan chan) tr)) as len_writes.
remember (trace_length (trace_filter (is_prop ∩₁ in_chan chan) tr)) as len_props. 
pose proof (NOmega_lt_trichotomy len_writes len_props). des; auto.
{ exfalso. destruct len_writes as [|n_writes]; auto.
  forward eapply (trace_nth_filter (is_prop ∩₁ in_chan chan) tr n_writes def_lbl) as [extra_prop_pos [DOM_EP [MATCH_PROP COUNT_PROPS]]].
  { vauto. }
  fold (count_upto (is_fpga_prop ∩₁ in_chan chan) extra_prop_pos) in COUNT_PROPS.
  forward eapply (filter_ends tr (write' ∩₁ in_chan chan) def_lbl) as [w_bound [DOM_WB WRITES_BOUND]]. 
  Admitted.
  (* { by rewrite <- Heqlen_writes. }
  set (bound := max (extra_prop_pos + 1) w_bound).     
  forward eapply (buffer_size thread bound) as BUF_SIZE.
  { destruct tr; auto. simpl in *. subst bound.
    apply NPeano.Nat.max_lub_iff. split; lia. }
  simpl in BUF_SIZE. remember (states bound) as st.
  cut (count_upto (write' ∩₁ in_thread thread) bound <= n_writes /\
        count_upto (is_prop ∩₁ in_thread thread) bound > n_writes).
    
  { ins. desc. lia. }
  split.
  { cut (NOmega.le (NOnum (count_upto (regular_write' ∩₁ in_thread thread) bound)) (NOnum n_writes)).
    { ins. }
    rewrite Heqlen_writes. unfold count_upto. apply count_le_filter.
    simpl. destruct (trace_length tr); vauto.
    subst bound. apply Nat.max_lub_iff. simpl in *. split; lia. }
  unfold gt. apply Nat.lt_le_trans with (m := count_upto (is_prop ∩₁ in_thread thread) (extra_prop_pos + 1)).
  { rewrite COUNT_PROPS.
    rewrite Nat.add_1_r, count_upto_next.
    rewrite check1; [lia| ].
    unfold trace_labels. rewrite <- MATCH_PROP.
    forward eapply (trace_nth_in (trace_filter (is_prop ∩₁ in_thread thread) tr) n_writes) with (d := def_lbl) as IN_FILTER. 
    { rewrite <- Heqlen_props. vauto. }
    vauto. 
    apply trace_in_filter in IN_FILTER. by desc. }
  apply count_upto_more. subst bound. apply Nat.le_max_l. }
exfalso. 
destruct len_props as [|n_props]; auto.

forward eapply (trace_nth_filter (regular_write' ∩₁ in_thread thread) tr n_props def_lbl) as [extra_write_pos [DOM_EW [MATCH_WRITE COUNT_WRITES]]].
{ vauto. }
fold (count_upto (regular_write' ∩₁ in_thread thread) extra_write_pos) in COUNT_WRITES.
set (enabled st := exists st', TSO_step st (inr thread) st').
assert (forall i (GE: i >= (extra_write_pos + 1))
          (LE: NOmega.le (NOnum i) (trace_length tr)),
            enabled (states i)) as ENABLED_AFTER_WRITES.
{ intros. pose proof (buffer_size thread i) as BUF_SIZE. specialize_full BUF_SIZE.
  { destruct tr; vauto. }
  cut (length (snd (states i) thread) > 0).
  { ins. destruct (states i) as [mem bufs]. simpl in *. red.
    destruct (bufs thread) as [| (loc, val) buf'] eqn:BUFS; [simpl in H0; lia| ].
    exists (upd mem loc val, upd bufs thread buf'). by eapply tso_prop. }
  simpl in BUF_SIZE. cut (count_upto (regular_write' ∩₁ in_thread thread) i > count_upto (is_prop ∩₁ in_thread thread) i); [ins; lia| ].
  unfold gt.
  apply Nat.le_lt_trans with (m := n_props).
  { forward eapply (count_le_filter tr (is_prop ∩₁ in_thread thread) i def_lbl) as COUNT_LE_FILTER; auto.
    rewrite <- Heqlen_props in COUNT_LE_FILTER. simpl in COUNT_LE_FILTER.
    by unfold count_upto. }
  apply Nat.lt_le_trans with (m := count_upto (regular_write' ∩₁ in_thread thread) (extra_write_pos + 1)).
  2: { apply count_upto_more. lia. }
  rewrite Nat.add_1_r, count_upto_next. rewrite <- COUNT_WRITES.
  rewrite check1; [lia| ].
  unfold trace_labels. rewrite <- MATCH_WRITE.
  remember (regular_write' ∩₁ in_thread thread) as F.
  remember (trace_nth n_props (trace_filter F tr) def_lbl) as elem. 
  forward eapply (proj1 (trace_in_filter elem F tr)); [| intuition]. 
  subst elem. apply trace_nth_in. vauto. }  

forward eapply (filter_ends tr (is_prop ∩₁ in_thread thread) def_lbl) as [props_end [DOM NOMORE_PROPS]]. 
{ by rewrite <- Heqlen_props. }
set (after_last_prop := max (extra_write_pos + 1) props_end).


assert (NOmega.le (NOnum after_last_prop) (trace_length tr)) as ALP_LE. 
{ destruct tr; vauto. simpl in *. unfold after_last_prop. apply NPeano.Nat.max_lub_iff. split; lia. }

pose proof FAIR as FAIR_. 
specialize (@FAIR_ after_last_prop thread). specialize_full FAIR_; auto. 
{ apply ENABLED_AFTER_WRITES; auto. 
  pose proof (Nat.le_max_l (extra_write_pos + 1) props_end). lia. }

destruct FAIR_ as (j & ALPj & DOMj & TRj). 
specialize (NOMORE_PROPS j). specialize_full NOMORE_PROPS.
{ pose proof (Nat.le_max_r (extra_write_pos + 1) props_end). lia. }
{ apply lt_nondefault. unfold trace_labels. by rewrite TRj. }
rewrite TRj in NOMORE_PROPS. unfolder'. intuition. 
Qed. *)

Lemma EXACT_CHAN_READS chan:
  trace_length (trace_filter (fpga_read_resp' ∩₁ in_chan chan) tr) =
  trace_length (trace_filter (fpga_mem_read' ∩₁ in_chan chan) tr).
Proof.
  Admitted.

Definition same_chan x y :=
  let chan := lbl_chan_opt x in
  chan = lbl_chan_opt y /\ chan <> None. 

Definition same_thread x y := lbl_thread x = lbl_thread y.

Lemma write2prop_fpga_lem w
    (* (DOM: NOmega.lt_nat_l w (trace_length tr)) *)
    (W: fpga_write' (trace_labels w)):
exists p,
  ⟪THREAD_PROP: (is_fpga_prop ∩₁ same_chan (trace_labels w)) (trace_labels p)⟫ /\
  (* ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫ /\ *)
  ⟪W_P_CORR: count_upto (fpga_write' ∩₁ same_chan (trace_labels w)) w =
              count_upto (is_fpga_prop ∩₁ same_chan (trace_labels w)) p⟫.
Proof.
simpl.
assert (DOM: NOmega.lt_nat_l w (trace_length tr)).
{ destruct (classic (NOmega.lt_nat_l w (trace_length tr))); auto.
  exfalso. apply ge_default in H. rewrite H in W.
  unfolder'. intuition. }
pose proof (fpga_write_structure _ W). 
desc.
assert (same_chan (trace_labels w) ≡₁ in_chan chan).
{ rewrite H. simpl. unfold same_chan. simpl.
  unfold in_chan.
  red. split; red; ins; desc; vauto. }
apply set_extensionality in H0. rewrite H0 in *. 
pose proof sim_subtraces_conv as TMP. specialize_full TMP.
{ eapply (EXACT_CHAN_PROPS chan). }
{ red. splits; eauto.
  rewrite H. vauto. }
{ auto. }
desc. exists j. splits; vauto.
Qed.

Lemma filter_eq_pred (l: list SyLabel) (f g: SyLabel -> Prop): (forall x, (f x <-> g x)) -> filterP f l = filterP g l.
Proof. 
  induction l; vauto.
  ins.
  erewrite IHl; vauto.
  destruct (excluded_middle_informative (f a)) as [FA | NFA].
  { destruct (H a) as [LR RL].
    desf.
    exfalso; apply (n (LR FA)).
  }
  { destruct (H a) as [LR RL].
    desf.
    exfalso; apply (NFA (RL g0)).
  }
Qed.

Lemma count_same_chan_in_chan (c: Chan) (l: SyLabel) (InChan: in_chan c l) pred i
  : count_upto (pred ∩₁ same_chan l) i = count_upto (pred ∩₁ in_chan c) i.
Proof.
  unfold count_upto.
  remember ((map
  (fun i0 : nat =>
   trace_nth i0 tr def_lbl)
  (List.seq 0 i))) as lst.
  remember (pred ∩₁ same_chan l) as p1.
  remember (pred ∩₁ in_chan c) as p2.
  assert (forall x, p1 x <-> p2 x).
  { ins.
    assert (same_chan l x <-> in_chan c x). {
      unfold same_chan in *.
      unfold in_chan in *.
      rewrite InChan.
      split; ins; desf.
    }
    vauto.
    unfold set_inter in *.
    intuition.
  }
  by erewrite (filter_eq_pred lst p1 p2 H).
Qed.


Lemma EXACT_CPU_PROPS thread:
  trace_length (trace_filter (cpu_write' ∩₁ in_cpu_thread thread) tr) =
  trace_length (trace_filter (is_cpu_prop ∩₁ in_cpu_thread thread) tr).
Proof.
remember (trace_length (trace_filter (cpu_write' ∩₁ in_cpu_thread thread) tr)) as len_writes.
remember (trace_length (trace_filter (is_cpu_prop ∩₁ in_cpu_thread thread) tr)) as len_props. 
pose proof (NOmega_lt_trichotomy len_writes len_props). des; auto.
{ exfalso. destruct len_writes as [|n_writes]; auto.
  forward eapply (trace_nth_filter (is_cpu_prop ∩₁ in_cpu_thread thread) tr n_writes def_lbl) as [extra_prop_pos [DOM_EP [MATCH_PROP COUNT_PROPS]]].
  { vauto. }
  fold (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) extra_prop_pos) in COUNT_PROPS.
  forward eapply (filter_ends tr (cpu_write' ∩₁ in_cpu_thread thread) def_lbl) as [w_bound [DOM_WB WRITES_BOUND]]. 
  { by rewrite <- Heqlen_writes. }
  set (bound := max (extra_prop_pos + 1) w_bound).     
  forward eapply (buffer_size_cpu thread bound) as BUF_SIZE.
  { destruct tr; auto. simpl in *. subst bound.
    apply NPeano.Nat.max_lub_iff. split; lia. }
  simpl in BUF_SIZE. remember (states bound) as st.
  cut (count_upto (cpu_write' ∩₁ in_cpu_thread thread) bound <= n_writes /\
        count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) bound > n_writes).
    
  { ins. desc. lia. }
  split.
  { cut (NOmega.le (NOnum (count_upto (cpu_write' ∩₁ in_cpu_thread thread) bound)) (NOnum n_writes)).
    { ins. }
    rewrite Heqlen_writes. unfold count_upto. apply count_le_filter.
    simpl. destruct (trace_length tr); vauto.
    subst bound. apply Nat.max_lub_iff. simpl in *. split; lia. }
  unfold gt. apply Nat.lt_le_trans with (m := count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) (extra_prop_pos + 1)).
  { rewrite COUNT_PROPS.
    rewrite Nat.add_1_r, count_upto_next.
    rewrite check1; [lia| ].
    unfold trace_labels. rewrite <- MATCH_PROP.
    forward eapply (trace_nth_in (trace_filter (is_cpu_prop ∩₁ in_cpu_thread thread) tr) n_writes) with (d := def_lbl) as IN_FILTER. 
    { rewrite <- Heqlen_props. vauto. }
    vauto. 
    apply trace_in_filter in IN_FILTER. by desc. }
  apply count_upto_more. subst bound. apply Nat.le_max_l. }
exfalso. 
destruct len_props as [|n_props]; auto.

forward eapply (trace_nth_filter (cpu_write' ∩₁ in_cpu_thread thread) tr n_props def_lbl) as [extra_write_pos [DOM_EW [MATCH_WRITE COUNT_WRITES]]].
{ vauto. }
fold (count_upto (cpu_write' ∩₁ in_cpu_thread thread) extra_write_pos) in COUNT_WRITES.
set (enabled st := exists st', TSOFPGA_step st (CpuFlush thread) st').
assert (forall i (GE: i >= (extra_write_pos + 1))
          (LE: NOmega.le (NOnum i) (trace_length tr)),
            enabled (states i)) as ENABLED_AFTER_WRITES.
{ intros. pose proof (buffer_size_cpu thread i) as BUF_SIZE. specialize_full BUF_SIZE.
  { destruct tr; vauto. }
  cut (length (cpu_bufs (states i) thread) > 0).
  { ins. destruct (states i) as [wp rp ups downs mem bufs]. simpl in *. red.
    destruct (bufs thread) as [| (loc, val) buf'] eqn:BUFS; [simpl in H0; lia| ].
    exists (mkState wp rp ups downs (upd mem loc val) (upd bufs thread buf')). by eapply cpu_propagate. }
  simpl in BUF_SIZE. cut (count_upto (cpu_write' ∩₁ in_cpu_thread thread) i > count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) i); [ins; lia| ].
  unfold gt.
  apply Nat.le_lt_trans with (m := n_props).
  { forward eapply (count_le_filter tr (is_cpu_prop ∩₁ in_cpu_thread thread) i def_lbl) as COUNT_LE_FILTER; auto.
    rewrite <- Heqlen_props in COUNT_LE_FILTER. simpl in COUNT_LE_FILTER.
    by unfold count_upto. }
  apply Nat.lt_le_trans with (m := count_upto (cpu_write' ∩₁ in_cpu_thread thread) (extra_write_pos + 1)).
  2: { apply count_upto_more. lia. }
  rewrite Nat.add_1_r, count_upto_next. rewrite <- COUNT_WRITES.
  rewrite check1; [lia| ].
  unfold trace_labels. rewrite <- MATCH_WRITE.
  remember (cpu_write' ∩₁ in_cpu_thread thread) as F.
  remember (trace_nth n_props (trace_filter F tr) def_lbl) as elem. 
  forward eapply (proj1 (trace_in_filter elem F tr)); [| intuition]. 
  subst elem. apply trace_nth_in. vauto. }  

forward eapply (filter_ends tr (is_cpu_prop ∩₁ in_cpu_thread thread) def_lbl) as [props_end [DOM NOMORE_PROPS]]. 
{ by rewrite <- Heqlen_props. }
set (after_last_prop := max (extra_write_pos + 1) props_end).


assert (NOmega.le (NOnum after_last_prop) (trace_length tr)) as ALP_LE. 
{ destruct tr; vauto. simpl in *. unfold after_last_prop. apply NPeano.Nat.max_lub_iff. split; lia. }

pose proof TSO_FAIR as FAIR_. 
specialize (@FAIR_ after_last_prop thread). specialize_full FAIR_; auto. 
{ apply ENABLED_AFTER_WRITES; auto. 
  pose proof (Nat.le_max_l (extra_write_pos + 1) props_end). lia. }

destruct FAIR_ as (j & ALPj & DOMj & TRj). 
specialize (NOMORE_PROPS j). specialize_full NOMORE_PROPS.
{ pose proof (Nat.le_max_r (extra_write_pos + 1) props_end). lia. }
{ apply lt_nondefault. unfold trace_labels. by rewrite TRj. }
rewrite TRj in NOMORE_PROPS. unfolder'. intuition. 
Qed.


Lemma set_extensionality A (r r' : A -> Prop) :
  r ≡₁ r' -> r = r'.
Proof.
  ins. extensionality x. 
  apply propositional_extensionality; split; apply H.
Qed.  

(* Lemma init_non_rw: forall l, ~ cpu_write' (inl (InitEvent l)). *)
(* Proof. *)
(*   apply init_non_rw'.  *)
(* Qed. *)



Lemma write2prop_cpu_lem w
      (* (DOM: NOmega.lt_nat_l w (trace_length tr)) *)
      (W: cpu_write' (trace_labels w)):
  exists p,
    ⟪THREAD_PROP: (is_cpu_prop ∩₁ same_thread (trace_labels w)) (trace_labels p)⟫ /\
    (* ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫ /\ *)
    ⟪W_P_CORR: count_upto (cpu_write' ∩₁ same_thread (trace_labels w)) w =
               count_upto (is_cpu_prop∩₁ same_thread (trace_labels w)) p⟫.
Proof.
  simpl.
  assert (DOM: NOmega.lt_nat_l w (trace_length tr)).
  { destruct (classic (NOmega.lt_nat_l w (trace_length tr))); auto.
    exfalso. apply ge_default in H. rewrite H in W.
    unfolder'. intuition. }
  pose proof (reg_write_structure _ W). 
  desc.
  assert (same_thread (trace_labels w) ≡₁ in_cpu_thread thread).
  { rewrite H. simpl. unfold same_thread. simpl.
    unfold in_cpu_thread.
    red. split; red; ins; desc; vauto. }
  apply set_extensionality in H0. rewrite H0 in *. 
  pose proof sim_subtraces_conv as TMP. specialize_full TMP.
  { eapply (EXACT_CPU_PROPS thread). }
  { red. splits; eauto.
    rewrite H. vauto. }
  { auto. }
  desc. exists j. splits; vauto.
Qed.

(* Lemma write2prop_general w
      (* (DOM: NOmega.lt_nat_l w (trace_length tr)) *)
      (W: write' (trace_labels w)):
  exists p,
    ⟪THREAD_PROP: (is_cpuprop ∩₁ same_thread (trace_labels w)) (trace_labels p)⟫ /\
    (* ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫ /\ *)
    ⟪W_P_CORR: count_upto (cpu_write' ∩₁ same_thread (trace_labels w)) w =
               count_upto (is_cpu_prop∩₁ same_thread (trace_labels w)) p⟫. *)

                   
Definition write2prop (w: nat) :=
  match (excluded_middle_informative (cpu_write' (trace_labels w))) with
  | left W => (proj1_sig ((constructive_indefinite_description _ (write2prop_cpu_lem w W))))
  | right _ => match (excluded_middle_informative (fpga_write' (trace_labels w))) with
    | left W => (proj1_sig ((constructive_indefinite_description _ (write2prop_fpga_lem w W))))
    | right _ => 0
    end
  end.


Lemma w2p_later_cpu w (W: cpu_write' (trace_labels w)):
  w < write2prop w.
Proof.
  remember (trace_labels w) as tlab.
  unfold write2prop.
  destruct (excluded_middle_informative (cpu_write' (trace_labels w))); [clear W| by vauto].  
  destruct (constructive_indefinite_description _ _) as [p [PROP CORR]]. simpl.
  pose proof (Nat.lt_trichotomy w p). des; auto.
  { subst. red in PROP. exfalso. 
    apply reg_write_structure in c. destruct c as [thread [index [loc [val H]]]].
    rewrite H in PROP. red in PROP. by desc. }
  exfalso. rename H into LT. 
  apply reg_write_structure in c. destruct c as [thread [index [loc [val TLAB]]]].
  forward eapply (buffer_size_cpu thread (p + 1)) as BUF_SIZE.
  { contra GE. forward eapply (proj2 (ge_default p)) as P_DEF. 
    { red. intros. apply GE. simpl. red in H. destruct tr; vauto.
      simpl in *. lia. }
    red in PROP. rewrite P_DEF in PROP.
    generalize PROP. unfolder'. intuition. }
  red in CORR.
  assert (same_thread (trace_labels w) = in_cpu_thread thread) as RESTR_EQUIV. 
  { apply set_extensionality. rewrite TLAB. simpl.
    unfold same_thread, in_cpu_thread. simpl. red. splits; red; ins; desc; vauto. }
  rewrite RESTR_EQUIV in CORR.
  replace (count_upto (is_cpu_prop∩₁ in_cpu_thread thread) (p + 1)) with ((count_upto (is_cpu_prop∩₁ in_cpu_thread thread) p) + 1) in BUF_SIZE.
  2: { unfold count_upto.
       rewrite Nat.add_1_r with (n := p), seqS, Nat.add_0_l.
       rewrite map_app, filterP_app, length_app. simpl.
       rewrite RESTR_EQUIV in PROP.
       destruct (excluded_middle_informative ((is_cpu_prop∩₁ in_cpu_thread thread) (trace_nth p tr def_lbl))); vauto. }
  rewrite <- CORR in BUF_SIZE.
  cut (count_upto (cpu_write' ∩₁ in_cpu_thread thread) (p + 1) <= count_upto (cpu_write' ∩₁ in_cpu_thread thread) w).
  { ins. lia. }
  apply count_upto_more. lia. 
Qed.

Lemma w2p_later_fpga w (W: fpga_write' (trace_labels w)):
  w < write2prop w.
Proof.
  remember (trace_labels w) as tlab.
  unfold write2prop.
  destruct (excluded_middle_informative (cpu_write' (trace_labels w))).
  {
    exfalso.
    vauto.
    unfold fpga_write', cpu_write' in *.
    desf.
  }
  destruct (excluded_middle_informative (fpga_write' (trace_labels w))).
  destruct (constructive_indefinite_description _ _) as [p [PROP CORR]]. simpl.
  pose proof (Nat.lt_trichotomy w p). des; auto.
  { subst. red in PROP. exfalso. 
    apply fpga_write_structure in f. destruct f as [chan [loc [val [index [meta H0]]]]].
    rewrite H0 in PROP. red in PROP. desc. vauto. }
  exfalso. rename H into LT. 
  apply fpga_write_structure in f. destruct f as [chan [loc [val [index [meta TLAB]]]]].
  forward eapply (buffer_size_upstream_write chan (p + 1)) as BUF_SIZE.
  { contra GE. forward eapply (proj2 (ge_default p)) as P_DEF. 
    { red. intros. apply GE. simpl. red in H. destruct tr; vauto.
      simpl in *. lia. }
    red in PROP. rewrite P_DEF in PROP.
    generalize PROP. unfolder'. intuition. }
  red in CORR.
  assert (same_chan (trace_labels w) = in_chan chan) as RESTR_EQUIV. 
  { apply set_extensionality. rewrite TLAB. simpl.
    unfold same_chan, in_cpu_thread. simpl. red. splits; red; ins; desc; vauto. }
  rewrite RESTR_EQUIV in CORR.
  replace (count_upto (is_fpga_prop∩₁ in_chan chan) (p + 1)) with ((count_upto (is_fpga_prop ∩₁ in_chan chan) p) + 1) in BUF_SIZE.
  2: { unfold count_upto.
       rewrite Nat.add_1_r with (n := p), seqS, Nat.add_0_l.
       rewrite map_app, filterP_app, length_app. simpl.
       rewrite RESTR_EQUIV in PROP.
       destruct (excluded_middle_informative ((is_fpga_prop∩₁ in_chan chan) (trace_nth p tr def_lbl))); vauto. }
  rewrite <- CORR in BUF_SIZE.
  cut (count_upto (fpga_write' ∩₁ in_chan chan) (p + 1) <= count_upto (fpga_write' ∩₁ in_chan chan) w).
  { ins. lia. }
  apply count_upto_more. lia. 
  { vauto. }
Qed. 

Lemma w2p_later w (W: write' (trace_labels w)):
  w < write2prop w.
Proof.
  unfold write' in W. destruct W.
  apply w2p_later_cpu. auto.
  apply w2p_later_fpga. auto.
Qed.

(* Порядок propagate в основную память *)
(* Definition vis (e: Event) :=
  match (excluded_middle_informative (is_cpu_wr e)) with
  | left W => write2prop (trace_index e)
  | right _ => match (excluded_middle_informative (is_wr_resp e)) with
    | left W => write2prop (trace_index e)
    | right _ => (trace_index e)
    end
  end. 

Definition vis_lt := is_init × Eninit ∪ ⦗Eninit⦘ ⨾ (fun x y => vis x < vis y) ⨾ ⦗Eninit⦘.  *)


Lemma read_resp_to_memread_lemma r
    (* (DOM: NOmega.lt_nat_l w (trace_length tr)) *)
    (R: fpga_read_resp' (trace_labels r)):
exists p,
  ⟪THREAD_PROP: (fpga_mem_read' ∩₁ same_chan (trace_labels r)) (trace_labels p)⟫ /\
  (* ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫ /\ *)
  ⟪W_P_CORR: count_upto (fpga_read_resp' ∩₁ same_chan (trace_labels r)) r =
              count_upto (fpga_mem_read' ∩₁ same_chan (trace_labels r)) p⟫.
Proof.
simpl.
assert (DOM: NOmega.lt_nat_l r (trace_length tr)).
{ destruct (classic (NOmega.lt_nat_l r (trace_length tr))); auto.
  exfalso. apply ge_default in H. rewrite H in R.
  unfolder'. intuition. }
pose proof (fpga_read_structure _ R).
desc.
assert (same_chan (trace_labels r) ≡₁ in_chan chan).
{ rewrite H. simpl. unfold same_chan. simpl.
  unfold in_chan.
  red. split; red; ins; desc; vauto. }
apply set_extensionality in H0. rewrite H0 in *. 
pose proof sim_subtraces_conv as TMP. specialize_full TMP.
{ eapply (EXACT_CHAN_READS chan). }
{ red. splits; eauto.
  rewrite H. vauto. }
{ auto. }
desc. exists j. splits; vauto.
Qed.

Definition read2mem_read (r: nat) :=
  match (excluded_middle_informative (fpga_read_resp' (trace_labels r))) with
  | left R => (proj1_sig ((constructive_indefinite_description _ (read_resp_to_memread_lemma r R))))
  | right _ => match (excluded_middle_informative (cpu_read' (trace_labels r))) with
    | left _ => r
    | right _ => 0
    end
  end.

(* Lemma mem_read_source: *)
(*   let st := trace_states tr TR in *)
(*   forall i loc val (MEM: fst (st i) loc = val), *)
(*   exists thread iw ip t_iw, *)
(*     ⟪PROP_BEFORE: ip <= i⟫ /\ *)
(*     ⟪NTH_THREAD_WRITE:  ⟫ *)


Definition exact_tid e := match e with
                          | InitEvent _ => 0
                          | ThreadEvent thread _ _ => thread
                          | FpgaEvent _ _ _ => 1
                          end.


(* Definition rf' w r :=
let (wp, rp, ups, downs, mem, bufs) := (state_before_event r) in
match filter (fun loc_val: Loc * Val => Nat.eqb (fst loc_val) (loc r))
              (bufs (exact_tid r)) with
| nil => latest_of_by (fun e => loc e = loc r /\ vis_lt e r /\ EG e /\ is_w e) vis_lt w
| _ => latest_of_by (fun e => loc e = loc r /\ trace_before e r /\ exact_tid e = exact_tid r /\ Eninit e /\ is_w e) trace_before w
end.  *)

Definition vis' (e: Event) :=
  match (excluded_middle_informative (is_cpu_wr e)) with
  | left W => write2prop (trace_index e)
  | right _ => match (excluded_middle_informative (is_wr_resp e)) with
    | left W => write2prop (trace_index e)
    | right _ => match (excluded_middle_informative (is_rd_resp e)) with 
      | left R => read2mem_read (trace_index e)
      | right _ => trace_index e
      end
    end
  end. 

Definition vis_lt' := is_init × Eninit ∪ ⦗Eninit⦘ ⨾ (fun x y => vis' x < vis' y) ⨾ ⦗Eninit⦘. 

Lemma mem_read_to_down_bufs st1 st2 (c: Chan) (x: nat) 
    (MEM_READ: fpga_mem_read' (trace_labels x)) 
    (IN_CHAN: in_chan c (trace_labels x))
    (STEP: TSOFPGA_step st1 (trace_labels x) st2)
    (IN_TRACE: NOmega.lt_nat_l x (trace_length tr))
  : length (down_bufs (states (S x)) c) > 0.
Proof.
  unfold in_chan in IN_CHAN.
  unfold lbl_chan_opt in IN_CHAN. 
  remember (TSi x IN_TRACE def_lbl) as STEP'.
  simpl in STEP'.
  unfold trace_labels in *.
  unfold fpga_mem_read' in MEM_READ.
  inv STEP'; desf.
  simpl.
  rewrite upds.
  rewrite length_app.
  simpl; lia.
Qed.

Lemma mem_read_from_up_bufs st1 st2 (c: Chan) (x: nat) 
    (MEM_READ: fpga_mem_read' (trace_labels x)) 
    (IN_CHAN: in_chan c (trace_labels x))
    (STEP: TSOFPGA_step st1 (trace_labels x) st2)
    (IN_TRACE: NOmega.lt_nat_l x (trace_length tr))
  : length (filter is_read_ups (up_bufs (states x) c)) > 0.
Proof.
  unfold in_chan in IN_CHAN.
  unfold lbl_chan_opt in IN_CHAN. 
  remember (TSi x IN_TRACE def_lbl) as STEP'.
  simpl in STEP'.
  unfold trace_labels in *.
  unfold fpga_mem_read' in MEM_READ.
  inv STEP'; desf.
  simpl.
  rewrite UPSTREAM.
  assert ((read_up loc, meta) :: up_buf' = ((read_up loc, meta) :: nil) ++ up_buf') by vauto.
  rewrite H.
  erewrite filter_app.
  rewrite length_app.
  assert (is_read_ups (read_up loc, meta)) by vauto.
  simpl.
  lia.
Qed.

Lemma rd_resp_after_memread rd (EN: Eninit rd) (RD: is_rd_resp rd) : (trace_index rd) > read2mem_read (trace_index rd).
Proof.
  unfold read2mem_read.
  desf.
  2: { exfalso. apply n. erewrite trace_index_simpl'; vauto. }
  2: { exfalso. apply n. erewrite trace_index_simpl'; vauto. }
  destruct (constructive_indefinite_description _); simpl; desf.
  erewrite trace_index_simpl' in f; eauto.
  destruct rd; desf.
  destruct e; desf.
  erewrite trace_index_simpl' in W_P_CORR; eauto.

  erewrite (count_same_chan_in_chan c) in W_P_CORR.
  2: { unfold in_chan; ins. }
  erewrite (count_same_chan_in_chan c) in W_P_CORR.
  2: { unfold in_chan; ins. }

  assert (NOmega.lt_nat_l x (trace_length tr)) as IN_TR. { 
    apply not_default_found.
    intro.
    unfold def_lbl in H.
    rewrite H in *.
    destruct THREAD_PROP; vauto.
  }

     cut (trace_index (FpgaEvent (Fpga_read_resp c x0 v) index m) > x
        \/ trace_index (FpgaEvent (Fpga_read_resp c x0 v) index m) = x
        \/ trace_index (FpgaEvent (Fpga_read_resp c x0 v) index m) < x); [|lia].
     intro T; destruct T as [GE | [EQ | LE]].
     { auto. }
     { exfalso. unfolder'. unfold fpga_mem_read' in *. subst x. desf. rewrite trace_index_simpl' in Heq; desf. }
     remember (trace_index (FpgaEvent (Fpga_read_resp c x0 v) index m)) as rsp.

  forward eapply (buffer_size_downstream c (rsp + 1)) as BUF_SIZE.
  { red in IN_TR; ins; destruct (trace_length tr); lia. }
  replace (count_upto (fpga_read_resp' ∩₁ in_chan c) (rsp + 1)) with ((count_upto (fpga_read_resp' ∩₁ in_chan c) rsp) + 1) in BUF_SIZE.
  2: { unfold count_upto.
       rewrite Nat.add_1_r with (n := rsp), seqS, Nat.add_0_l.
       rewrite map_app, filterP_app, length_app. simpl.
       fold (trace_labels rsp).
       destruct (excluded_middle_informative ((fpga_read_resp' ∩₁ in_chan c) (trace_labels rsp))); vauto. rewrite trace_index_simpl' in n; vauto. destruct n; unfolder'; desf. }
  rewrite W_P_CORR in BUF_SIZE.
 
  cut (count_upto (fpga_mem_read' ∩₁ in_chan c) (rsp + 1) <= count_upto (fpga_mem_read' ∩₁ in_chan c) x).
  { ins. lia. }
  apply count_upto_more. lia. 
Qed.

Lemma r_vis e (Rr: is_cpu_rd e): vis' e = trace_index e.
Proof.
  unfold vis'.
  generalize Rr. unfolder'. destruct e; vauto.
  destruct e; ins.
  all: destruct (excluded_middle_informative _ ); intuition.
Qed. 

Lemma vis_SPO:
  strict_partial_order vis_lt'. 
Proof.
  unfold vis_lt', map_rel. 
  red. split. 
  { apply irreflexive_union. split.
    { red. ins. red in H. desc. by apply (proj1 Eninit_non_init x). }
    red. ins. apply seq_eqv_lr in H. desc. lia. }
  apply transitiveI.
  rewrite seq_union_l. apply inclusion_union_l.
  { apply inclusion_union_r1_search. red. ins.
    red in H. desc. red in H. desc.
    red. red in H0. des.
    { red in H0. by desc. }
    apply seq_eqv_lr in H0. by desc. }
  apply inclusion_union_r2_search.
  rewrite seq_union_r.
  rewrite !seqA. arewrite (⦗Eninit⦘ ⨾ is_init × Eninit ⊆ ∅₂).
  { generalize Eninit_non_init. basic_solver. }
  rewrite !seq_false_r, union_false_l.
  hahn_frame_l. hahn_frame_r. rewrite !inclusion_seq_eqv_l.
  red. ins. red in H. desc. lia. 
Qed. 

(* True only for normal vis. Can add WR constraint *)
Lemma TI_LE_VIS e (ENINIT: Eninit e) (NOT_FPGA_RD: ~is_rd_resp e): trace_index e <= vis' e.
Proof.
  unfold vis'. simpl.
  destruct (excluded_middle_informative (is_cpu_wr e)).
  {
    apply Nat.lt_le_incl. apply w2p_later_cpu.
    unfold trace_labels. rewrite trace_index_simpl; auto.
  }
  destruct (excluded_middle_informative (is_wr_resp e)).
  { apply Nat.lt_le_incl. apply w2p_later_fpga.
  unfold trace_labels. rewrite trace_index_simpl; auto. }
  destruct (excluded_middle_informative (is_rd_resp e)); [vauto| ].
  lia.
Qed.


(* Definition rf' w r :=
  let (wp, rp, ups, downs, mem, bufs) := (state_before_event r) in
  match (excluded_middle_informative (is_cpu_wr w)) with
  | left W => 
    match filter (fun loc_val: Loc * Val => Nat.eqb (fst loc_val) (loc r))
                  (bufs (exact_tid r)) with
      | nil => latest_of_by (fun e => loc e = loc r /\ vis_lt' e r /\ EG e /\ is_w e) vis_lt' w
      | _ => latest_of_by (fun e => loc e = loc r /\ trace_before e r /\ exact_tid e = exact_tid r /\ Eninit e /\ is_w e) trace_before w
      end
  | right _ => latest_of_by (fun e => loc e = loc r /\ vis_lt' e r /\ EG e /\ is_w e ) vis_lt' w
  end. *)

Definition rf' w r :=
  let (wp, rp, ups, downs, mem, bufs) := (state_before_event r) in
  match (excluded_middle_informative (is_cpu_rd r)) with
  | left R => 
    match filter (fun loc_val: Loc * Val => Nat.eqb (fst loc_val) (loc r))
                  (bufs (exact_tid r)) with
      | nil => latest_of_by (fun e => loc e = loc r /\ vis_lt' e r /\ EG e /\ is_w e) vis_lt' w
      | _ => latest_of_by (fun e => loc e = loc r /\ trace_before e r /\ exact_tid e = exact_tid r /\ Eninit e /\ is_cpu_wr e) trace_before w
      end
  | right _ => latest_of_by (fun e => loc e = loc r /\ vis_lt' e r /\ EG e /\ is_w e ) vis_lt' w
  end.


Definition readpair' req resp := is_rd_req req /\ is_rd_resp resp /\ meta req = meta resp.
Definition writepair' req resp := is_wr_req req /\ is_wr_resp resp /\ meta req = meta resp.
Definition fenceonepair' req resp := is_fence_req_one req /\ is_fence_resp_one resp /\ meta req = meta resp.
Definition fenceallpair' req resp := is_fence_req_all req /\ is_fence_resp_all resp /\ meta req = meta resp.
Definition pair' req resp := readpair' req resp \/ writepair' req resp \/ fenceonepair' req resp \/ fenceallpair' req resp.
  

Definition nth_such n S i := count_upto S i = n /\ S (trace_labels i).

Lemma rd_rest_vis r (Rr: is_rd_resp r): vis' r = read2mem_read (trace_index r).
Proof.
  unfold vis'.
  destruct (excluded_middle_informative (is_cpu_wr r)).
  { unfolder'; desf. }
  destruct (excluded_middle_informative (is_wr_resp r)).
  { unfolder'; desf. }
  destruct (excluded_middle_informative (is_rd_resp r)).
  2: { vauto. }
  auto.
Qed.


Lemma cpuw_vis e (RMW: is_cpu_wr e): vis' e = write2prop (trace_index e). 
Proof.
  unfold vis'.
  destruct (excluded_middle_informative (is_cpu_wr e)); vauto.
Qed.

Lemma fpgaw_vis e (RMW: is_wr_resp e): vis' e = write2prop (trace_index e). 
Proof.
  unfold vis'.
  destruct (excluded_middle_informative (is_cpu_wr e)); vauto.
  destruct (excluded_middle_informative (is_wr_resp e)); vauto.
Qed.

Lemma RESTR_EQUIV thread index lbl:
  same_thread (EventLab (ThreadEvent thread index lbl)) = in_cpu_thread thread.
Proof.
  ins. apply set_extensionality. 
  unfold same_thread, in_cpu_thread. simpl. red. splits; red; ins; desc; vauto.
Qed. 

(* Lemma RESTR_EQUIV_CHAN chan index lbl meta:
  same_chan (EventLab (FpgaEvent lbl index meta)) = in_chan chan.
Proof.
  ins. apply set_extensionality. 
  unfold same_chan, in_chan. simpl.
  red. splits; red; ins; desc; vauto.
  destruct lbl, x; desf.
  destruct x; vauto.
  unfold lbl_chan_opt in *; destruct lbl; simpl; desf.
Qed.  *)
    
Definition G :=
  {| acts := EG;
     co := ⦗EG ∩₁ is_w⦘ ⨾ restr_eq_rel SyEvents.loc vis_lt' ⨾ ⦗EG ∩₁ is_w⦘;     
     rf := ⦗EG ∩₁ is_w⦘ ⨾ rf' ⨾ ⦗EG ∩₁ is_r⦘;
     readpair := ⦗EG ∩₁ is_rd_req⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_rd_resp⦘;
     writepair := ⦗EG ∩₁ is_wr_req⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_wr_resp⦘;
     fenceonepair := ⦗EG ∩₁ is_fence_req_one⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_fence_resp_one⦘;
     fenceallpair := ⦗EG ∩₁ is_fence_req_all⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_fence_resp_all⦘
  |}.

Lemma WFG: Wf_fpga G.
Proof.
  destruct WF.
  split; ins.
  all: try basic_solver.
  (* TODO: 4 repetitions *)
  {
    unfold set_subset.
    intros.
    destruct H.
    destruct H.
    {
      unfolder'.
      destruct x; vauto. 
    }
    unfold dom_rel.
    remember (trace_index x) as i.
    assert (trace_nth (trace_index x) tr def_lbl = EventLab x).
    { eapply trace_index_simpl; eauto. }
    assert (is_req x). { 
      unfolder'. desf.
    }
    remember (PAIR_EXISTS (trace_index x) def_lbl x H1 H2) as E.
    destruct E as [j [e2 [comes_before [is_trace [in_trace' is_resp_pair]]]]].

    assert (Eninit e2). {
      unfold Eninit.
      rewrite <- in_trace'.
      eapply trace_nth_in. eauto.
    }
    exists e2.
    unfold eqv_rel; unfold seq.
    exists x.
    repeat split; vauto.
    exists e2.
    repeat split; vauto.
    unfolder'.
    desf.
  }
  {
    unfold set_subset.
    intros.
    destruct H.
    destruct H.
    {
      unfolder'.
      destruct x; vauto. 
    }
    unfold dom_rel.
    remember (trace_index x) as i.
    assert (trace_nth (trace_index x) tr def_lbl = EventLab x).
    { eapply trace_index_simpl; eauto. }
    assert (is_req x). { 
      unfolder'. desf.
    }
    remember (PAIR_EXISTS (trace_index x) def_lbl x H1 H2) as E.
    destruct E as [j [e2 [comes_before [is_trace [in_trace' is_resp_pair]]]]].

    assert (Eninit e2). {
      unfold Eninit.
      rewrite <- in_trace'.
      eapply trace_nth_in. eauto.
    }
    exists e2.
    unfold eqv_rel; unfold seq.
    exists x.
    repeat split; vauto.
    exists e2.
    repeat split; vauto.
    unfolder'.
    desf.
  }
  {
    unfold set_subset.
    intros.
    destruct H.
    destruct H.
    {
      unfolder'.
      destruct x; vauto. 
    }
    unfold dom_rel.
    remember (trace_index x) as i.
    assert (trace_nth (trace_index x) tr def_lbl = EventLab x).
    { eapply trace_index_simpl; eauto. }
    assert (is_req x). { 
      unfolder'. desf.
    }
    remember (PAIR_EXISTS (trace_index x) def_lbl x H1 H2) as E.
    destruct E as [j [e2 [comes_before [is_trace [in_trace' is_resp_pair]]]]].

    assert (Eninit e2). {
      unfold Eninit.
      rewrite <- in_trace'.
      eapply trace_nth_in. eauto.
    }
    exists e2.
    unfold eqv_rel; unfold seq.
    exists x.
    repeat split; vauto.
    exists e2.
    repeat split; vauto.
    unfolder'.
    desf.
  }
  {
    unfold set_subset.
    intros.
    destruct H.
    destruct H.
    {
      unfolder'.
      destruct x; vauto. 
    }
    unfold dom_rel.
    remember (trace_index x) as i.
    assert (trace_nth (trace_index x) tr def_lbl = EventLab x).
    { eapply trace_index_simpl; eauto. }
    assert (is_req x). { 
      unfolder'. desf.
    }
    remember (PAIR_EXISTS (trace_index x) def_lbl x H1 H2) as E.
    destruct E as [j [e2 [comes_before [is_trace [in_trace' is_resp_pair]]]]].

    assert (Eninit e2). {
      unfold Eninit.
      rewrite <- in_trace'.
      eapply trace_nth_in. eauto.
    }
    exists e2.
    unfold eqv_rel; unfold seq.
    exists x.
    repeat split; vauto.
    exists e2.
    repeat split; vauto.
    unfolder'.
    desf.
  }
Qed.


Lemma vis_lt_init_helper_cpu x y (SB: sb G x y): vis_lt' x y \/ (Eninit x /\ Eninit y).
Proof.
unfold sb in SB. apply seq_eqv_lr in SB. destruct SB as [Ex [SBxy Ey]]. ins.  
do 2 red in Ex. des.
{ do 2 red in Ey. des; vauto.
  red in SBxy. destruct x, y; vauto. }
do 2 red in Ey. des.
{ red in SBxy. destruct x, y; vauto. }
vauto.
Qed.


Lemma rf_same_tid_ext_sb w r (RF: rf G w r) (TID: tid w = tid r) : ext_sb w r.
Proof.
  unfold ext_sb.
  simpl in RF.
  apply seq_eqv_lr in RF.
  destruct RF as [Ew [RFwr Er]].
  unfold rf' in RFwr.
  destruct Ew, Er.
  unfold is_w, is_r in *.
  destruct (state_before_event r) as [wp rp up downs mem bufs].
  desf.
  simpl in RFwr.
  red in RFwr.
  destruct RFwr as [[LOC [VISLT [EG' TT]]] UNUSED].
  { split. reflexivity. destruct VISLT as [BAD | VISLT].
    { destruct BAD. desf. }
    clear UNUSED.
    destruct VISLT as [WR [EN1 [RD [VIS EN2]]]]; desf.
    destruct EN1 as [WREQ ENWR].
    destruct EN2 as [RDEQ ENRD].
    unfold vis' in VIS.
    unfold loc in *.
    rewrite WREQ in *.
    rewrite RDEQ in *.
    desf.
    remember (ThreadEvent thread0 index (Cpu_store x0 v0)) as wr.
    remember (ThreadEvent thread0 index0 (Cpu_load x0 v)) as rd.
    assert (cpu_write' (trace_labels(trace_index wr))) 
      as CPU. { ins. erewrite trace_index_simpl'; vauto. }
    remember (w2p_later_cpu (trace_index wr) CPU).
    assert (trace_index (wr) < trace_index (rd)) by lia.
    assert ((⦗Eninit⦘ ⨾ ext_sb ⨾ ⦗Eninit⦘) wr rd) as SB'. {
      eapply tb_respects_sb.
      apply seq_eqv_lr.
      split; desf; vauto. }
    apply seq_eqv_lr in SB'.
    destruct SB' as [Ex [SBxy Ey]].
    rename index into wr_i.
    rename index0 into rd_i.
    assert (~ is_init wr). { intro. eapply Eninit_non_init; red; eauto. }
    assert (index wr < index rd) as INDEX_INEQ. { eapply ext_sb_index; eauto. }
    unfold index in INDEX_INEQ.
    desf. }
  2: { destruct RFwr as [[LOC [VISLT [EG' TT]]] UNUSED].
    clear UNUSED.
    destruct VISLT as [BAD | VISLT].
    { destruct BAD; desf. }
    destruct VISLT as [WR [EN1 [RD [VIS EN2]]]]; desf.
    destruct EN1 as [WREQ ENWR].
    destruct EN2 as [RDEQ ENRD].
    unfold vis' in VIS.
    unfold loc in *.
    rewrite WREQ in *.
    rewrite RDEQ in *.
    desf.
    remember (FpgaEvent (Fpga_read_resp c x v) index0 m0) as rd.
    remember (FpgaEvent (Fpga_write_resp c0 x v0) index m) as wr.
    assert (fpga_write' (trace_labels(trace_index wr))) 
      as FPGA. { ins. erewrite trace_index_simpl'; vauto. }
    remember (w2p_later_fpga (trace_index wr) FPGA).
    assert (trace_index (wr) < read2mem_read (trace_index rd)) as INEQ by lia.
    assert (read2mem_read (trace_index rd) < trace_index (rd)) as INEQ'.
    { apply rd_resp_after_memread; vauto. }
    assert (trace_index wr < trace_index rd) by lia.
    rename index into wr_i.
    rename index0 into rd_i.
    assert ((⦗Eninit⦘ ⨾ ext_sb ⨾ ⦗Eninit⦘) wr rd) as SB'. {
      eapply tb_respects_sb.
      apply seq_eqv_lr.
      split; desf; vauto. }
    apply seq_eqv_lr in SB'.
    destruct SB' as [Ex [SBxy Ey]].
    assert (index wr < index rd) as INDEX_INEQ. { eapply ext_sb_index; vauto. }
    unfold index in INDEX_INEQ.
    desf.
    }
  {
  simpl in RFwr.
  red in RFwr.
  destruct RFwr as [[LOC [TRACE_BEFORE [S_TID [EN_WR TT]]]] UNUSED].
  split; [reflexivity |].
  remember ((ThreadEvent thread0 index (Cpu_store x0 v0))) as wr.
  remember ((ThreadEvent thread0 index0 (Cpu_load x v))) as rd.

  assert (same_tid rd wr) by vauto.
  destruct (excluded_middle_informative (Eninit rd)) as [ENRD | NENRD].
  2: { exfalso.  
       unfold trace_before in TRACE_BEFORE.
       assert (trace_index wr >= 0). { unfold trace_index. desf. lia. }
       assert (trace_index rd = 0). { unfold trace_index. desf. }
       lia. }
  assert ((⦗Eninit⦘ ⨾ ext_sb ⨾ ⦗Eninit⦘) wr rd) as SB'. {
    eapply tb_respects_sb.
    apply seq_eqv_lr.
    repeat split; vauto.
  }
  apply seq_eqv_lr in SB'.
  destruct SB' as [Ex [SBxy Ey]].
  rename index into wr_i.
  rename index0 into rd_i.
  assert (index wr < index rd) as INDEX_INEQ. { eapply ext_sb_index; vauto. }
  unfold index in INDEX_INEQ; desf.
  } 
Qed.
  
Lemma cpu_vis_respects_sb_w: restr_rel (is_cpu ∩₁ is_w) (sb G) ⊆ vis_lt'.
Proof.
unfold restr_rel. red. ins. destruct H as [SBxy [Wx Wy]].
destruct (vis_lt_init_helper_cpu x y SBxy) as [|[E'x E'y]]; auto. 
red. red. right. apply seq_eqv_lr. splits; auto.
red in SBxy. apply seq_eqv_lr in SBxy. destruct SBxy as [_ [SBxy _]].
forward eapply (proj1 tb_respects_sb x y) as H; [basic_solver| ].
apply seq_eqv_lr in H. destruct H as [_ [[TBxy TIDxy] _]]. 
(* apply tb_respects_sb in SBxy. destruct SBxy as [TBxy TIDxy].  *)
red in TBxy.
unfold vis'. 
destruct (excluded_middle_informative _) as [X | X].
{
  destruct (excluded_middle_informative _) as [Y | Y].
  2: {
    unfolder'.
    unfold is_w in *.
    desf.
  }
  unfold write2prop. destruct (excluded_middle_informative _).
  2: {
    unfold trace_labels in n. rewrite trace_index_simpl in n; vauto.
  }
  destruct (excluded_middle_informative _).
  2: {
    unfold trace_labels in n. rewrite trace_index_simpl in n; vauto.
  }
    destruct (constructive_indefinite_description _ _) as [px Px].
    destruct (constructive_indefinite_description _ _) as [py Py].
    simpl in *. desc.
    unfold trace_labels in *. rewrite !trace_index_simpl in *; auto.
    assert (exists thread, same_thread (EventLab x) = in_cpu_thread thread /\ same_thread (EventLab y) = in_cpu_thread thread).
    { pose proof (reg_write_structure _ c). desc. inv H. 
      pose proof (reg_write_structure _ c0). desc. inv H0. 
      red in TIDxy. simpl in TIDxy. inv TIDxy.
      exists thread0. 
      split; apply RESTR_EQUIV. }
    desc. rewrite H, H0 in *. 
    assert (count_upto (cpu_write' ∩₁ in_cpu_thread thread) (trace_index x) < count_upto (cpu_write' ∩₁ in_cpu_thread thread) (trace_index y)).
    { subst. apply Nat.lt_le_trans with (m := count_upto (cpu_write' ∩₁ in_cpu_thread thread) (trace_index x + 1)).
      2: { eapply count_upto_more. lia. }
      rewrite Nat.add_1_r, count_upto_next.
      rewrite check1; [lia|].
      unfold trace_labels. rewrite trace_index_simpl; auto. red. split; auto.
      rewrite <- H. unfold same_thread. generalize c. 
      destruct x; unfolder'; intuition; vauto.
    } 
    apply lt_diff in H1. desc. rewrite W_P_CORR0, W_P_CORR in H1. 
    destruct (NPeano.Nat.lt_ge_cases px py); auto. 
    remember (count_upto_more py px (is_cpu_prop ∩₁ in_cpu_thread thread) H2); lia. }
  destruct Wx.
  unfold is_cpu, is_cpu_wr, is_w in *.
  unfolder'.
  desf.
Qed.



Lemma rfe_diff_tid w r (RFE: rfe G w r): tid w <> tid r. 
Proof.
  intro.
  (* destruct w, r; desf. *)
  unfold rfe in RFE.
  (* unfold rf, sb in RFE.
  simpl in RFE. *)
  destruct RFE as [RF NOT_SB].
  destruct NOT_SB.
  unfold sb.
  apply seq_eqv_lr.
  assert (ext_sb w r) by (apply rf_same_tid_ext_sb; vauto).
  simpl.
  simpl in RF.
  apply seq_eqv_lr in RF.
  destruct RF as [[EGW WW] [RF [EGR RR]]].
  vauto.
Qed.
  
Lemma sb_same_tid w r (SB: sb G w r) (NOT_INIT: Eninit w): tid w = tid r.
Proof.
  red in SB.
  assert (~ is_init w).
  { intro.
    eapply Eninit_non_init; red; eauto. }
  unfold tid.
  apply seq_eqv_lr in SB.
  destruct SB as [Ex [SBxy Ey]].
  unfold ext_sb in SBxy.
  destruct w, r; desf.
Qed.

Lemma no_read_from_future': irreflexive (rf G ⨾ sb G).
Proof.
  rewrite rfi_union_rfe.
  arewrite (rfi G ⊆ sb G).
  rewrite seq_union_l.
  apply irreflexive_union.
  split.
  { rewrite rewrite_trans.
    apply sb_irr.
    apply sb_trans.
  }
  unfold irreflexive; ins.
  unfold seq in H.
  destruct H as [e [RFE SB]].
  assert (Eninit e). {
    destruct RFE as [RF NSB].
    destruct RF as [A [B [C [D IS_R]]]].
    destruct IS_R as [EQ [EG IS_R]].
    subst.
    unfold is_r in *.
    destruct EG; destruct e; desf.
  }
  apply rfe_diff_tid in RFE.
  apply sb_same_tid in SB; vauto.
  symmetry in SB; auto.
Qed.

(* Requires memory fairness to prove? *)
Lemma fsupp_vis_loc: fsupp (restr_eq_rel loc vis_lt').
Proof.
  Admitted.

Lemma vis_inj_lemma x y (E'x: Eninit x) (E'y: Eninit y) (VIS_EQ: vis' x = vis' y) (CPU_X: is_cpu_wr x) (FPGA_Y: is_wr_resp y): x = y.
Proof.
  unfold vis' in VIS_EQ.
  repeat destruct (excluded_middle_informative _); desf.
  { unfolder'. desf. }
  unfold write2prop in VIS_EQ. 

  do 2 destruct (excluded_middle_informative _).
  all: try (rewrite trace_index_simpl' in *; vauto).
  { clear VIS_EQ. erewrite trace_index_simpl' in c0; vauto. }
  destruct (excluded_middle_informative _).
  all: try (rewrite trace_index_simpl' in *; vauto).
  do 2 destruct (constructive_indefinite_description _ _). desc. simpl in *.
  subst. rewrite trace_index_simpl' in *; auto.

  pose proof (reg_write_structure _ c). pose proof (fpga_write_structure _ f).
  desc. inversion H. inversion H0. subst.
  rewrite RESTR_EQUIV in *. 
  remember (ThreadEvent thread index0 (Cpu_store loc0 val0)) as w1.
  remember (FpgaEvent (Fpga_write_resp chan loc val) index meta) as w2.
  { generalize THREAD_PROP0, THREAD_PROP. unfolder'.
    destruct (trace_labels x1); vauto; intuition. }
Qed.

Lemma vis_inj_weak x y (E'x: Eninit x) (E'y: Eninit y) (VIS_EQ: vis' x = vis' y) (WX: is_w x) (WY: is_w y): x = y.
Proof.
  assert (vis' x = vis' y) as VIS_EQ' by auto.
  unfold vis' in VIS_EQ.
  destruct (excluded_middle_informative (is_cpu_wr x)) as [X | X]; destruct (excluded_middle_informative (is_cpu_wr y)) as [Y | Y].
  { unfold write2prop in VIS_EQ. 
    do 2 destruct (excluded_middle_informative _).
    all: try (rewrite trace_index_simpl' in *; vauto).
    do 2 destruct (constructive_indefinite_description _ _). desc. simpl in *.
    subst. rewrite trace_index_simpl' in *; auto.
    pose proof (reg_write_structure _ c). pose proof (reg_write_structure _ c0).
    desc. inversion H. inversion H0. subst.
    rewrite RESTR_EQUIV in *. 
    remember (ThreadEvent thread0 index0 (Cpu_store loc0 val0)) as w1.
    remember (ThreadEvent thread index (Cpu_store loc val)) as w2.
    assert (thread0 = thread); [| subst thread0]. 
    { generalize THREAD_PROP0, THREAD_PROP. unfolder'.
      destruct (trace_labels x1); vauto; intuition. congruence. }
    rewrite <- W_P_CORR0 in W_P_CORR.
    pose proof (Nat.lt_trichotomy (trace_index w1) (trace_index w2)). des.
    2: { apply ti_inj; vauto. }
    { apply lt_diff in H1. desc. rewrite H1 in W_P_CORR.
      assert (count_upto (cpu_write' ∩₁ in_cpu_thread thread) (S (trace_index w1)) = count_upto (cpu_write' ∩₁ in_cpu_thread thread) (trace_index w1) + 1).
      { rewrite count_upto_next. rewrite check1; [lia| ].
        rewrite trace_index_simpl'; auto. red. splits; vauto. }
      forward eapply (@count_upto_more (S (trace_index w1)) (trace_index w1 + S d)(cpu_write' ∩₁ in_cpu_thread thread)) as LE; lia. }
    { apply lt_diff in H1. desc. rewrite H1 in W_P_CORR.
      assert (count_upto (cpu_write' ∩₁ in_cpu_thread thread) (S (trace_index w2)) = count_upto (cpu_write' ∩₁ in_cpu_thread thread) (trace_index w2) + 1).
      { rewrite count_upto_next. rewrite check1; [lia| ].
        rewrite trace_index_simpl'; auto. red. splits; vauto. }
      forward eapply (@count_upto_more (S (trace_index w2)) (trace_index w2 + S d)(cpu_write' ∩₁ in_cpu_thread thread)) as LE; lia. } }

  { apply vis_inj_lemma; vauto. exact (proj1 (write_cases' y WY E'y) Y). }

  { assert (is_wr_resp x). { exact (proj1 (write_cases' x WX E'x) X). }
    symmetry; apply vis_inj_lemma; vauto. }

  unfold write2prop in VIS_EQ. 
  assert (is_wr_resp x) as RESP_X by (exact (proj1 (write_cases' x WX E'x) X)).
  assert (is_wr_resp y) as RESP_Y by (exact (proj1 (write_cases' y WY E'y) Y)).
  all: try (rewrite trace_index_simpl' in *; vauto).
  do 2 destruct (excluded_middle_informative _).
  { clear VIS_EQ; rewrite trace_index_simpl' in *; vauto. }
  2: { unfolder'; vauto. }
  2: { unfolder'; vauto. }
  do 2 destruct (excluded_middle_informative _).
  all: try (rewrite trace_index_simpl' in *; vauto).
  destruct (excluded_middle_informative).
  { clear VIS_EQ. rewrite trace_index_simpl' in *; vauto. }
  destruct (excluded_middle_informative).
  2: { clear VIS_EQ. rewrite trace_index_simpl' in *; vauto. }

  do 2 destruct (constructive_indefinite_description _ _). desc. simpl in *.
  subst. rewrite trace_index_simpl' in *; auto.
  pose proof (fpga_write_structure _ f). pose proof (fpga_write_structure _ f0).
  desc. inversion H. inversion H0. subst.
  remember (FpgaEvent (Fpga_write_resp chan0 loc0 val0) index0 meta0) as w1.
  remember (FpgaEvent (Fpga_write_resp chan loc val) index meta) as w2.

    assert (chan0 = chan); [| subst chan0]. 
    { generalize THREAD_PROP0, THREAD_PROP. unfolder'. unfold same_chan in *. unfold lbl_chan_opt in *.
      destruct (trace_labels x1); vauto; intuition. congruence. }
    assert (in_chan chan (EventLab w1)) as CH_W1 by vauto.
    assert (in_chan chan (EventLab w2)) as CH_W2 by vauto.
    do 2 rewrite (count_same_chan_in_chan chan _ CH_W1 _ _) in W_P_CORR0.
    do 2 rewrite (count_same_chan_in_chan chan _ CH_W2 _ _) in W_P_CORR.
    rewrite <- W_P_CORR0 in W_P_CORR.
    pose proof (Nat.lt_trichotomy (trace_index w1) (trace_index w2)). des.
    2: { apply ti_inj; vauto. }
    { apply lt_diff in H1. desc. rewrite H1 in W_P_CORR.
      assert (count_upto (fpga_write' ∩₁ in_chan chan) (S (trace_index w1)) = count_upto (fpga_write' ∩₁ in_chan chan) (trace_index w1) + 1).
      { rewrite count_upto_next. rewrite check1; [lia| ].
        rewrite trace_index_simpl'; auto. red. splits; vauto. }
      forward eapply (@count_upto_more (S (trace_index w1)) (trace_index w1 + S d)(fpga_write' ∩₁ in_chan chan)) as LE; lia. }
    { apply lt_diff in H1. desc. rewrite H1 in W_P_CORR.
      assert (count_upto (fpga_write' ∩₁ in_chan chan) (S (trace_index w2)) = count_upto (fpga_write' ∩₁ in_chan chan) (trace_index w2) + 1).
      { rewrite count_upto_next. rewrite check1; [lia| ].
        rewrite trace_index_simpl'; auto. red. splits; vauto. }
      forward eapply (@count_upto_more (S (trace_index w2)) (trace_index w2 + S d)(fpga_write' ∩₁ in_chan chan)) as LE; lia. }
Qed. 

Lemma co_loc_total l:
  strict_total_order (EG ∩₁ is_w ∩₁ (fun a => loc a = l)) (co G). 
Proof.
  red. split.
  { red. split.
    { red. ins. apply seq_eqv_lr in H. desc.
      red in H0. desc. do 2 red in H0. des.
      { by apply (proj1 Eninit_non_init x). }
      apply seq_eqv_lr in H0. desc. lia. }
    { simpl. red. ins. apply seq_eqv_lr in H. apply seq_eqv_lr in H0. desc.
      apply seq_eqv_lr. splits; auto.
      red in H3, H1. desc. red. split; [| congruence].
      red in H3, H1. red in H3, H1. des.
      { red in H3, H1. desc. vauto. }
      { apply seq_eqv_lr in H3. red in H1. desc. destruct (proj1 Eninit_non_init y); vauto. }
      { red in H3. apply seq_eqv_lr in H1. desc. red. left. red. vauto. }
      apply seq_eqv_lr in H3. apply seq_eqv_lr in H1. desc. red. right.
      apply seq_eqv_lr. splits; auto. lia. } }
  red. intros x [[Ex Wx] Lx] y [[Ey Wy] Ly] NEQ.
  simpl in Ex, Ey. do 2 red in Ex, Ey. des.
  { destruct x, y; vauto. unfold loc in Ly. simpl in Ly. by subst. }
  { right. simpl. apply seq_eqv_lr. splits; vauto. }
  { left. simpl. apply seq_eqv_lr. splits; vauto. }
  pose proof (Nat.lt_trichotomy (vis' x) (vis' y)). des.
  2: { forward eapply (vis_inj_weak x y); vauto. }
  { left. simpl. apply seq_eqv_lr. splits; vauto. red. split; auto.
    red. right. apply seq_eqv_lr. splits; auto. }  
  { right. simpl. apply seq_eqv_lr. splits; vauto. red. split; auto.
    red. right. apply seq_eqv_lr. splits; auto. }
Qed.

Lemma w2p_regw w thread (REG: cpu_write' (EventLab w))
      (TID: tid w = (CpuTid thread)) (E'w: Eninit w):
  (is_prop ∩₁ in_cpu_thread thread) (trace_nth (write2prop (trace_index w)) tr def_lbl).
Proof.
  unfold write2prop. destruct (excluded_middle_informative _).
  (* 2: { generalize REG, n. rewrite trace_index_simpl'; auto. intuition. } *)
  2: { rewrite trace_index_simpl' in n; vauto. }
  destruct (constructive_indefinite_description _ _). desc. simpl in *.
  rewrite trace_index_simpl' in *; auto.
  apply reg_write_structure in c. desc. inversion c. subst. 
  destruct THREAD_PROP as [CPU_PROP SAME_TID].
  split; vauto.
  assert (thread0 = thread) as TID_EQ. { unfold tid in TID; vauto. }
  rewrite TID_EQ in *; clear TID_EQ.
  erewrite <- RESTR_EQUIV; eauto.
Qed. 

Lemma w2p_fpgawr w ch (REG: fpga_write' (EventLab w))
      (TID: chan w = ch) (E'w: Eninit w):
  (is_prop ∩₁ in_chan ch) (trace_nth (write2prop (trace_index w)) tr def_lbl).
Proof.
  unfold write2prop. destruct (excluded_middle_informative _).
  (* 2: { generalize REG, n. rewrite trace_index_simpl'; auto. intuition. } *)
  { exfalso; rewrite trace_index_simpl' in c; unfolder'; desf; vauto. }
  destruct (excluded_middle_informative _).
  2: { rewrite trace_index_simpl' in *; vauto. }
  destruct (constructive_indefinite_description _ _). desc. simpl in *.
  rewrite trace_index_simpl' in *; auto.
  apply fpga_write_structure in f. desc. inversion f. subst. 
  destruct THREAD_PROP as [CPU_PROP SAME_TID].
  split; vauto.
  simpl.
  unfold same_chan, in_chan in *. desf.
Qed. 

Lemma ti_uniq i j thread ind lbl (EQ: trace_nth i tr def_lbl = trace_nth j tr def_lbl)
      (EVENT: trace_nth i tr def_lbl = EventLab (ThreadEvent thread ind lbl)):
  i = j.
Proof.
  fold (trace_labels i) in EQ, EVENT. fold (trace_labels j) in EQ. 
  pose proof WF as WF'. 
  destruct WF' as [WF' FPGA_WF PU PE].
  red in WF'. specialize WF' with (d := def_lbl) (thread := thread) (lbl1 := lbl) (lbl2 := lbl). 
  pose proof (Nat.lt_trichotomy i j). des; auto; exfalso. 
  { specialize (@WF' i j ind ind H). forward eapply WF'; eauto; [| unfold trace_labels in *; congruence| lia].
    apply lt_nondefault. by rewrite <- EQ, EVENT. }
  { specialize (@WF' j i ind ind H). forward eapply WF'; eauto; [| unfold trace_labels in *; congruence| lia].
    apply lt_nondefault. by rewrite EVENT. }
Qed.

Lemma ti_uniq_fpga i j meta ind lbl (EQ: trace_nth i tr def_lbl = trace_nth j tr def_lbl)
      (EVENT: trace_nth i tr def_lbl = EventLab (FpgaEvent lbl ind meta)):
  i = j.
Proof.
  fold (trace_labels i) in EQ, EVENT. fold (trace_labels j) in EQ. 
  pose proof WF as WF'. 
  destruct WF' as [TSO_WF WF' PU PE].
  red in WF'. specialize WF' with (d := def_lbl) (meta1 := meta) (meta2 := meta) (lbl1 := lbl) (lbl2 := lbl). 
  pose proof (Nat.lt_trichotomy i j). des; auto; exfalso. 
  { specialize (@WF' i j ind ind H). forward eapply WF'; eauto; [| unfold trace_labels in *; congruence| lia].
    apply lt_nondefault. by rewrite <- EQ, EVENT. }
  { specialize (@WF' j i ind ind H). forward eapply WF'; eauto; [| unfold trace_labels in *; congruence| lia].
    apply lt_nondefault. by rewrite EVENT. }
Qed.

Lemma ti_infer ind thread index lbl
      (TRACE: trace_nth ind tr def_lbl = EventLab (ThreadEvent thread index lbl)):
  trace_index (ThreadEvent thread index lbl) = ind.
Proof.
  forward eapply ti_uniq with (i := ind) (j := trace_index (ThreadEvent thread index lbl)); eauto.
  rewrite trace_index_simpl; auto.
  red. rewrite <- TRACE. apply trace_nth_in.
  apply lt_nondefault. unfold trace_labels. rewrite TRACE. vauto.
Qed.

Lemma ti_infer_fpga ind meta index lbl
      (TRACE: trace_nth ind tr def_lbl = EventLab (FpgaEvent lbl index meta)):
  trace_index (FpgaEvent lbl index meta) = ind.
Proof.
  forward eapply ti_uniq_fpga with (i := ind) (j := trace_index (FpgaEvent lbl index meta)); eauto.
  rewrite trace_index_simpl; auto.
  red. rewrite <- TRACE. apply trace_nth_in.
  apply lt_nondefault. unfold trace_labels. rewrite TRACE. vauto.
Qed.

Lemma nth_such_self (F: SyLabel -> Prop) i (Fi: F (trace_labels i)):
  nth_such (count_upto F i) F i.
Proof.
  red. split; auto.
Qed. 

Lemma nth_such_unique k F i j (NTH_I: nth_such k F i) (NTH_J: nth_such k F j):
  i = j.
Proof.
  red in NTH_I, NTH_J. desc. 
  pose proof (Nat.lt_trichotomy i j) as LT. des; auto.
  { exfalso. apply lt_diff in LT. desc. subst.
    forward eapply (@count_upto_more (S i) (i + S d) F) as MORE; [lia| ].
    rewrite count_upto_next, check1 in MORE; auto. lia. }
  { exfalso. apply lt_diff in LT. desc. subst.
    forward eapply (@count_upto_more (S j) (j + S d) F) as MORE; [lia| ].
    rewrite count_upto_next, check1 in MORE; auto. lia. }  
Qed. 

Lemma buffer_sources_cpu i thread (DOM: NOmega.lt_nat_l i (trace_length tr)):
  let buf := cpu_bufs (states i) thread in
  let ip := count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) i in
  forall k l v (AT_K: Some (l, v) = nth_error buf k),
  exists ind,
    let lab_w := ThreadEvent thread ind (Cpu_store l v) in
    let w := trace_index lab_w in 
    ⟪ WRITE_POS: nth_such (ip + k) (cpu_write' ∩₁ in_cpu_thread thread) w ⟫ /\
    (* ⟪ WRITE_VALUE: trace_labels w =  ⟫ /\ *)
    ⟪ WRITE_BEFORE: w < i ⟫ /\
    ⟪ PROP_AFTER: i <= write2prop w ⟫ /\
    ⟪ ENINIT: Eninit lab_w ⟫. 
Proof.
  induction i.
  { ins. rewrite <- TS0 in AT_K. simpl in AT_K. by destruct k. }
  simpl in *. ins.
  assert (NOmega.lt_nat_l i (trace_length tr)) as DOM'.
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  specialize (IHi DOM').

  assert (Some (l, v) = nth_error (cpu_bufs (states i) thread) k ->
          ~ (is_cpu_prop ∩₁ in_cpu_thread thread) (trace_nth i tr def_lbl) ->
          exists ind : nat,
            nth_such (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) (S i) + k)
                     (cpu_write' ∩₁ in_cpu_thread thread)
                     (trace_index (ThreadEvent thread ind (Cpu_store l v))) /\
            trace_index (ThreadEvent thread ind (Cpu_store l v)) < S i /\
            S i <= write2prop (trace_index (ThreadEvent thread ind (Cpu_store l v))) /\
            Eninit (ThreadEvent thread ind (Cpu_store l v))) as SAME.
  { ins. specialize (IHi k l v). specialize_full IHi; [congruence| ].
    desc. exists ind. splits; vauto.
    { cut (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) (S i) = count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) i); [congruence| ].
      rewrite count_upto_next, check0; [lia| ]. auto. }
    apply le_lt_or_eq in PROP_AFTER. des; [lia| ].
    forward eapply (@w2p_regw (ThreadEvent thread ind (Cpu_store l v)) thread) as W2P_PROP; try (by vauto). 
    assert ((is_cpu_prop ∩₁ in_cpu_thread thread) (trace_nth (write2prop (trace_index (ThreadEvent thread ind (Cpu_store l v)))) tr def_lbl)) as PROP_CPU.
    { unfold is_prop in W2P_PROP. destruct W2P_PROP. split; vauto. destruct H1; vauto. unfolder'; desf. }
    vauto. }
    
  forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
  inversion TSi.
  all: try (apply SAME; [destruct H0, H2; simpl in *; congruence | ]; rewrite <- H; unfolder'; intuition; vauto ).
  { rewrite <- H2 in AT_K. simpl in AT_K.
    destruct (classic (thread0 = thread)).
    2: { rewrite updo in AT_K; auto.
         apply SAME; [by rewrite <- H0| ].
         rewrite <- H. unfolder'. intuition. }
    subst thread0. 
    rewrite upds in AT_K.
    assert (k <= length (cpu_bufs thread)) as W_POS.
    { forward eapply (proj1 (nth_error_Some (cpu_bufs thread ++ (loc, val) :: nil) k)).
      { apply opt_val. eauto. }
      rewrite length_app. simpl. lia. }
    apply le_lt_or_eq in W_POS. des.
    { apply SAME.
      { rewrite nth_error_app1 in AT_K; auto. by rewrite <- H0. }
      rewrite <- H. unfolder'. unfold is_cpu_prop. unfolder'. intuition. }
    exists index.
    assert (l = loc /\ v = val).  
    { rewrite W_POS in AT_K. rewrite nth_error_app2 in AT_K; [| lia].
      rewrite Nat.sub_diag in AT_K. simpl in AT_K. by inversion AT_K. }
    desc. subst loc val.
    forward eapply (ti_infer i) as IND; eauto. 
    splits.
    { forward eapply (buffer_size_cpu thread (i)) as BUF_SIZE.
      { destruct (trace_length tr); vauto. simpl in *. lia. }
      simpl in BUF_SIZE. rewrite W_POS.
      rewrite count_upto_next, check0.
      2: { unfold trace_labels. rewrite <- H. unfolder'. intro. desf. }
      rewrite Nat.add_0_r.
      rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE. rewrite <- BUF_SIZE.
      rewrite IND. apply nth_such_self.
      unfold trace_labels. rewrite <- H. unfolder'. intuition. }
    { lia. }
    { rewrite IND. forward eapply (w2p_later i) as LATER.
      { unfold trace_labels. rewrite <- H. unfolder'. intuition. }
      lia. }
    red. rewrite H. apply trace_nth_in. auto. }
  { destruct (classic (thread0 = thread)).
    2: { apply SAME.
         { rewrite <- H0. rewrite <- H2 in AT_K. simpl in AT_K. rewrite updo in AT_K; auto. }
         rewrite <- H. unfolder'. intuition. vauto. }
    subst thread0. rewrite <- H2 in AT_K. simpl in AT_K. rewrite upds in AT_K.
    specialize (IHi (S k) l v). specialize_full IHi. 
    { rewrite <- H0. simpl. by rewrite CPU_BUF. }
    desc. exists ind.
    splits; vauto.
    { replace (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) (S i)) with (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) i + 1).
      { by rewrite <- NPeano.Nat.add_assoc, Nat.add_1_l. }
      rewrite count_upto_next, check1; auto.
      unfold trace_labels. by rewrite <- H. }
    apply le_lt_or_eq in PROP_AFTER. des; [done| ].

    exfalso.
    unfold write2prop in PROP_AFTER. destruct (excluded_middle_informative _).
    2: { generalize n. rewrite trace_index_simpl'; auto. unfolder'. intuition. }
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    rewrite trace_index_simpl' in *; auto.
    rewrite RESTR_EQUIV in *. subst x.
    red in WRITE_POS. desc. lia. }
Qed. 

Lemma rf_before_prop w r (RF: rf G w r) (CPU_R: is_cpu_rd r) (CPU_W: is_cpu_wr w)
      (BUF:   let (_, _, _, _, _, bufs) := (state_before_event r) in
              filter (fun loc_val: Loc * Val => Nat.eqb (fst loc_val) (loc r))
                     (bufs (exact_tid r)) <> nil):
  trace_index r < vis' w.
Proof.
  simpl in RF. apply seq_eqv_lr in RF. destruct RF as [[E'w Ww] [RF [E'r Rr]]].
  do 2 red in E'r. des.
  { edestruct init_non_r; eauto. }
  remember (state_before_event r) as st. destruct st as [mem bufs].
  red in RF. 
  destruct (excluded_middle_informative _).
  2: vauto.
  rewrite <- Heqst in RF.
  remember (filter (fun loc_val : Loc * Val => fst loc_val =? loc r)
                   (cpu_bufs (exact_tid r))) as buf_flt.
  destruct buf_flt; [done| ].
  rename buf_flt into h. remember (p :: h) as buf_flt. clear Heqbuf_flt0.  
  clear E'w. red in RF. destruct RF as [[LOC [TBwr [TID [E'w _]]]] LATEST].
  contra BEFORE. apply not_lt in BEFORE. red in BEFORE.
  apply le_lt_or_eq in BEFORE. des.
  2: { assert (trace_labels (vis' w) = trace_labels (trace_index r)) by auto.
       rewrite trace_index_simpl' in H; auto.
       unfold vis' in H. destruct (excluded_middle_informative _).
       2: vauto.
       unfold write2prop in H. destruct (excluded_middle_informative _).
       2: { generalize i, n. rewrite trace_index_simpl'; auto. }
       destruct (constructive_indefinite_description _ _). desc. simpl in *.
       generalize THREAD_PROP, Rr. rewrite H. unfolder'. intuition. }
  assert (exists flt_ind val, Some (loc r, val) = nth_error buf_flt flt_ind) as FLT_POS. 
  { destruct buf_flt; [vauto| ]. exists 0. destruct p0. exists v. simpl.
    do 2 f_equal.
    assert (In (l, v) (filter (fun loc_val : Loc * Val => fst loc_val =? loc r)
                              (cpu_bufs (exact_tid r)))).
    { by rewrite <- Heqbuf_flt. }
    apply in_filter_iff in H. desc. simpl in H0. by apply beq_nat_true in H0. }
  desc.
  remember (cpu_bufs (exact_tid r)) as buf. 
  assert (exists buf_ind, Some (loc r, val) = nth_error buf buf_ind) as BUF_POS.
  { symmetry in FLT_POS. apply nth_error_In in FLT_POS.
    rewrite Heqbuf_flt in FLT_POS. apply in_filter_iff in FLT_POS. desc.
    apply In_nth_error in FLT_POS. desc. eauto. }
  desc. 
  forward eapply (@buffer_sources_cpu (trace_index r) (exact_tid r)) with (k := buf_ind) (l := (loc r)) (v := val) as [w_ind SOURCE].
  { apply lt_nondefault. rewrite trace_index_simpl'; auto.
    generalize Rr. unfolder'. destruct r; vauto. } 
  { unfold state_before_event in Heqst. rewrite <- Heqst. simpl. vauto. } 
  simpl in SOURCE. desc. remember (ThreadEvent (exact_tid r) w_ind (Cpu_store (loc r) val)) as w'.

  specialize (LATEST w'). specialize_full LATEST.
  { splits; vauto. }

  red in LATEST. des.
  { subst w'. red in TBwr. rewrite LATEST in *.
    rewrite cpuw_vis in BEFORE.
    2: { subst. unfolder'. intuition. }
    lia. }

  forward eapply (@cpu_vis_respects_sb_w w' w) as VISw'w.
  { red. splits; try (by vauto). red. apply seq_eqv_lr. splits; auto.
    1,3: by (simpl; unfold EG; vauto).
    forward eapply (proj2 tb_respects_sb w' w) as TB.
    2: { apply seq_eqv_lr in TB. by desc. }
    apply seq_eqv_lr. splits; auto. 
    split; auto. 
    red. unfold exact_tid in TID. 
    subst w'; destruct w, r; vauto.
    unfolder'; desf. }
  do 2 red in VISw'w. des.
  { red in VISw'w. desc. destruct (proj1 Eninit_non_init w'); vauto. }
  apply seq_eqv_lr in VISw'w. desc.
  rewrite cpuw_vis in VISw'w0; [| subst w'; unfolder'; intuition].  
  lia. 
Qed. 

Lemma len_filter_leq A (l: list A) (P: A -> bool): 
  length (filter P l) <= length l.
Proof.
  induction l; simpl; auto.
  destruct (P a); simpl; lia.
Qed.

Lemma len_filter_leq' A (l: list A) (P: A -> bool) k: 
  k < length (filter P l) -> k < length l.
Proof.
  forward eapply (len_filter_leq A l P). ins. lia.
Qed.

Lemma buffer_sources_upstream_wr i chan (DOM: NOmega.lt_nat_l i (trace_length tr)):
  let buf := filter is_store_ups (up_bufs (states i) chan) in
  let ip := count_upto (is_fpga_prop ∩₁ in_chan chan) i in
  forall k l v meta (AT_K: Some (store_up l v, meta) = nth_error buf k),
  exists ind, 
    let lab_w := FpgaEvent (Fpga_write_resp chan l v) ind meta in
    let w := trace_index lab_w in 
    ⟪ WRITE_POS: nth_such (ip + k) (fpga_write' ∩₁ in_chan chan) w ⟫ /\
    (* ⟪ WRITE_VALUE: trace_labels w =  ⟫ /\ *)
    ⟪ WRITE_BEFORE: w < i ⟫ /\
    ⟪ PROP_AFTER: i <= write2prop w ⟫ /\
    ⟪ ENINIT: Eninit lab_w ⟫. 
Proof.
  induction i.
  { ins. rewrite <- TS0 in AT_K. simpl in AT_K. by destruct k. }
  simpl in *. ins.
  assert (NOmega.lt_nat_l i (trace_length tr)) as DOM'.
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  specialize (IHi DOM').

  assert (forall meta, Some (store_up l v, meta) = nth_error (filter is_store_ups (up_bufs (states i) chan)) k ->
          ~ (is_fpga_prop ∩₁ in_chan chan) (trace_nth i tr def_lbl) ->
          exists ind : nat,
            nth_such (count_upto (is_fpga_prop ∩₁ in_chan chan) (S i) + k)
                     (fpga_write' ∩₁ in_chan chan)
                     (trace_index (FpgaEvent (Fpga_write_resp chan l v) ind meta)) /\
            trace_index (FpgaEvent (Fpga_write_resp chan l v) ind meta) < S i /\
            S i <= write2prop (trace_index (FpgaEvent (Fpga_write_resp chan l v) ind meta)) /\
            Eninit (FpgaEvent (Fpga_write_resp chan l v) ind meta)) as SAME.
  { ins. specialize (IHi k l v meta0). specialize_full IHi; [congruence| ].
    desc. exists ind. splits; vauto.
    { cut (count_upto (is_fpga_prop ∩₁ in_chan chan) (S i) = count_upto (is_fpga_prop ∩₁ in_chan chan) i); [congruence| ].
      rewrite count_upto_next, check0; [lia| ]. auto. }
    apply le_lt_or_eq in PROP_AFTER. des; [lia| ].
    forward eapply (@w2p_fpgawr (FpgaEvent (Fpga_write_resp chan l v) ind meta0) chan) as W2P_PROP; try (by vauto). 
    assert ((is_fpga_prop ∩₁ in_chan chan) (trace_nth (write2prop (trace_index (FpgaEvent (Fpga_write_resp chan l v) ind meta0))) tr def_lbl)) as PROP_CPU.
    { unfold is_prop in W2P_PROP. destruct W2P_PROP. split; vauto. destruct H1; vauto. unfolder'; desf. }
    vauto. }
    
  forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
  inversion TSi.
  all: try (apply SAME; [destruct H0, H2; simpl in *; congruence | ]; rewrite <- H; unfolder'; intuition; vauto ).
  { rewrite <- H2 in AT_K. simpl in AT_K.
    destruct (classic (channel = chan)).
    2: { rewrite updo in AT_K; auto.
         apply SAME; [by rewrite <- H0| ].
         rewrite <- H. unfolder'. intuition. }
    (* destruct (classic (meta0 = meta)).
    2: { } *)
    subst channel. 
    rewrite upds in AT_K.
    (* assert (k <= length (up_bufs chan)) as W_POS.
    { forward eapply (proj1 (nth_error_Some  (up_bufs chan ++ (store_up loc val, meta0) :: nil) k)).
      { apply opt_val. exists (store_up l v, meta). symmetry. auto. }
      rewrite length_app. simpl. lia. } *)
    assert (k <= length (filter is_store_ups (up_bufs chan))) as W_POS.
    { forward eapply (proj1 (nth_error_Some (filter is_store_ups (up_bufs chan ++ (store_up loc val, meta0) :: nil)) k)).
      { apply opt_val. exists (store_up l v, meta). auto.  }
      rewrite filter_app. rewrite length_app. simpl. lia. }
    apply le_lt_or_eq in W_POS. des.
    { apply SAME.
      { rewrite filter_app in AT_K. rewrite nth_error_app1 in AT_K; auto. by rewrite <- H0. }
      rewrite <- H. unfolder'. intuition. }
    exists index.
    assert (l = loc /\ v = val /\ meta = meta0).  
    { rewrite filter_app in AT_K. rewrite W_POS in AT_K. rewrite nth_error_app2 in AT_K; [| lia].
      rewrite Nat.sub_diag in AT_K. simpl in AT_K. by inversion AT_K. }
    desc. subst loc val meta.
    forward eapply (ti_infer_fpga i) as IND; eauto. 
    splits.
    { forward eapply (buffer_size_upstream_write chan (i)) as BUF_SIZE.
      { destruct (trace_length tr); vauto. simpl in *. lia. }
      simpl in BUF_SIZE. rewrite W_POS.
      rewrite count_upto_next, check0.
      2: { unfold trace_labels. rewrite <- H. unfolder'. intro. desf. }
      rewrite Nat.add_0_r.
      rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE. rewrite <- BUF_SIZE.
      rewrite IND. apply nth_such_self.
      unfold trace_labels. rewrite <- H. unfolder'. intuition.
      red. simpl. auto. }
    { lia. }
    { rewrite IND. forward eapply (w2p_later i) as LATER.
      { unfold trace_labels. rewrite <- H. unfolder'. intuition. }
      lia. }
    red. rewrite H. apply trace_nth_in. auto. }
  { destruct (classic (chan = channel)).
    2: { apply SAME.
         { rewrite <- H0. rewrite <- H2 in AT_K. simpl in AT_K. rewrite updo in AT_K; auto. }
         rewrite <- H. unfolder'. unfold in_chan. unfold lbl_chan_opt. intuition. vauto. }
    subst chan. rewrite <- H2 in AT_K. simpl in AT_K. rewrite upds in AT_K.
    specialize (IHi (S k) l v meta). specialize_full IHi. 
    { rewrite <- H0. simpl. by rewrite UPSTREAM. }
    desc. exists ind.
    splits; vauto.
    { replace (count_upto (is_fpga_prop ∩₁ in_chan channel) (S i)) with (count_upto (is_fpga_prop ∩₁ in_chan channel) i + 1).
      { by rewrite <- NPeano.Nat.add_assoc, Nat.add_1_l. }
      rewrite count_upto_next, check1; auto.
      unfold trace_labels. by rewrite <- H. }
    apply le_lt_or_eq in PROP_AFTER. des; [done| ].

    exfalso.
    unfold write2prop in PROP_AFTER. 
    destruct (excluded_middle_informative _).
    { generalize c. rewrite trace_index_simpl'; auto. }
    destruct (excluded_middle_informative _).
    2: { generalize n0. rewrite trace_index_simpl'; auto. intuition. }
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    rewrite trace_index_simpl' in *; auto.
    assert (same_chan (EventLab
       (FpgaEvent (Fpga_write_resp channel l v) ind meta)) = in_chan channel) as CH_REWR.
    { ins. apply set_extensionality. 
      unfold same_chan, in_chan. simpl. red. splits; red; ins; desc; vauto. }
    rewrite CH_REWR in *. subst x.
    red in WRITE_POS. desc. lia. }
    { apply SAME.
      2: { rewrite <- H. intro. destruct H1; desf. }
      cut (filter is_store_ups (TSOFPGA.up_bufs (states (S i)) chan) = filter is_store_ups (TSOFPGA.up_bufs (states i) chan)).
      { ins. rewrite <- H1. vauto. }
      rewrite <- H0, <- H2; simpl.
      destruct (classic (channel = chan)).
      { subst chan. rewrite upds. rewrite filter_app; simpl. apply app_nil_r. }
      rewrite updo; vauto; lia. }
    { apply SAME.
      2: { rewrite <- H. intro. destruct H1; desf. }
      cut (filter is_store_ups (TSOFPGA.up_bufs (states (S i)) chan) = filter is_store_ups (TSOFPGA.up_bufs (states i) chan)).
      { ins. rewrite <- H1. vauto. }
      rewrite <- H0, <- H2; simpl.
      destruct (classic (channel = chan)).
      { subst chan. rewrite UPSTREAM. rewrite upds. simpl. auto. }
      rewrite updo; vauto; lia. }
Qed.


Lemma no_writes_no_buffer thread l i (DOM: NOmega.lt_nat_l i (trace_length tr))
      (NO_LOC_WRITES: forall e, ~ (loc e = l /\ trace_index e < i /\
                              i <= write2prop (trace_index e) /\
                              exact_tid e = thread /\ Eninit e /\ is_cpu_wr e)):
  let buf := cpu_bufs (states i) thread in
  filter (fun loc_val: Loc * Val => fst loc_val =? l) buf = nil.
Proof.
  simpl. 
  remember (filter (fun loc_val : Loc * Val => fst loc_val =? l)
                   (cpu_bufs (states i) thread)) as buf_flt.
  apply length_zero_iff_nil. destruct (Nat.eq_0_gt_0_cases (length buf_flt)) as [| NEMPTY]; [vauto|]. exfalso.
  apply lt_diff in NEMPTY. desc.
  assert (exists elt, Some elt = nth_error buf_flt d) as [elt NTH_FLT]. 
  { forward eapply (proj2 (nth_error_Some buf_flt d)); [lia| ].
    destruct (nth_error buf_flt d); vauto. }
  forward eapply nth_error_In as IN_FLT; eauto.
  rewrite Heqbuf_flt in IN_FLT. apply in_filter_iff in IN_FLT. desc.
  apply In_nth_error in IN_FLT. desc.
  destruct elt as (l0, v).
  remember (states i) as st. destruct st as [mem bufs]. simpl in *. 
  simpl in *. apply beq_nat_true in IN_FLT0. subst.

  forward eapply (@buffer_sources_cpu i thread DOM n l v) as [ind H].
  { by rewrite <- IN_FLT, <- Heqst. }
  simpl in H. desc.
  apply (NO_LOC_WRITES (ThreadEvent thread ind (Cpu_store l v))).
  splits; auto.
  unfolder'; vauto.
Qed. 

Lemma read_source_cpu r (Er: EG r) (Rr: is_cpu_rd r):
  exists! w, rf G w r.
Proof.
  assert (is_r r) as GEN_R. { unfold is_cpu_rd, is_r in *; desf. }
  cut ((exists! w, (EG ∩₁ is_w) w /\ rf' w r) /\ (EG ∩₁ is_r) r).
  { ins. unfold unique in H. desc.
    exists x. red. splits.
    { apply seq_eqv_lr. splits; auto. }
    ins. desc. apply seq_eqv_lr in H3. desc. apply H1. splits; auto. }
  split; [| vauto].
  unfold rf'.
  do 2 red in Er. des.
  { exfalso. eapply init_non_r; eauto. }
  (* red in Er. pose proof Er as Er_.  *)
  (* apply trace_in_nth with (d := def_lbl) in Er. desc. *)
  unfold state_before_event.
  forward eapply (TSi (trace_index r)) with (d := def_lbl) as TSi; eauto.
  { contra GE.
    pose proof (proj2 (ge_default (trace_index r)) GE).
    unfold def_lbl in H. by rewrite trace_index_simpl' in H; vauto. }
  
  rewrite trace_index_simpl in TSi; auto.
  remember (states (trace_index r)) as st. destruct st as [wp rp ups downs mem bufs].
  destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r) (bufs (exact_tid r))) eqn:BUF.
  { remember (fun e : Event => loc e = loc r /\ vis_lt' e r /\ EG e /\ is_w e) as writes.
    cut (exists! w, latest_of_by writes (co G) w).
    {
      subst writes. intros [w [LATEST UNIQ]]. red in LATEST. desc.
      exists w.
      assert (is_w w). { unfolder'; desf. }
      red.
      destruct excluded_middle_informative as [CPU_R | NOT_CPU_R].
      { split.
        { split; vauto.
          red. splits; vauto. intros. specialize (LATEST0 y S').
          red in LATEST0. des; [vauto| ]. simpl in LATEST0. apply seq_eqv_lr in LATEST0. desc. red in LATEST4. desc. vauto. }
        ins. desc.
        assert (latest_of_by
            (fun e : Event =>
             loc e = loc r /\
             vis_lt' e r /\ EG e /\ is_w e)
            vis_lt' x') as H2 by desf; vauto.
        red in H1. desc. apply UNIQ. red. splits; vauto.
        ins. specialize (H3 y S').
        red in H3. des; [vauto| ].
        red. right. apply seq_eqv_lr. splits; vauto.
        red. split; auto. congruence. }
      { vauto. }
    }
    apply latest_unique.
    { apply antisymmetric_inclusion with (r := co G); [| basic_solver].
      apply strict_partial_order_antisymmetric.
      by destruct (co_loc_total (loc r)). }
    assert (set_finite writes) as WRITES_FIN.
    { arewrite (writes ⊆₁ fun e => loc e = loc r /\ vis_lt' e r) by basic_solver.
      pose proof (fsupp_vis_loc r) as [findom FINDOM].
      red. exists findom. ins. desc. apply FINDOM. red. split; auto. }
    assert (~ writes ≡₁ ∅) as HAS_WRITES.
    { apply set_nonemptyE. exists (InitEvent (loc r)).
      subst. splits; vauto. }
    assert (strict_total_order writes (co G)) as TOTAL.
    { red. split.
      { by destruct (co_loc_total (loc r)). }
      forward eapply (@is_total_mori _ (EG ∩₁ is_w ∩₁ (fun a => loc a = loc r)) writes) as H.
      { subst. unfold Basics.flip. basic_solver. }
      { eapply (inclusion_refl2 (co G)). }
      apply H, co_loc_total. }
    apply latest_fin; eauto. }
  remember (fun e : Event => loc e = loc r /\ trace_before e r /\ exact_tid e = exact_tid r /\  Eninit e /\ is_cpu_wr e) as writes.
  destruct (excluded_middle_informative (is_cpu_rd r)).
  2: vauto.
  cut (exists w, unique (latest_of_by writes trace_before) w).
  { ins. unfold unique in H. desc. red in H. desc.
    rewrite Heqwrites in H. desc.
    exists w. red. splits; vauto.
    (* {  unfold latest_of_by in *. remember (H0 r). splits; vauto.
      2: {intro. ins. assert (is_w y). { destruct y; unfold is_w, is_cpu_wr in *; desf. } apply H1. destruct S' as [LOC [TRB [ETID [EN WR]]]]; splits; vauto. }
      destruct w; desf.
      destruct (exact_tid r); vauto.
    } *)
    { unfolder'; unfold is_w; desf; vauto. }
    ins. desc. red in H7. desc. apply H0. red. splits; vauto. }

  assert (set_finite writes) as WRITES_FIN.
  { apply set_finite_mori with (x := fun e => trace_before e r /\ Eninit e).
    { red. rewrite Heqwrites. basic_solver. }
    red.
    set (extract_event := fun i => match (trace_labels i) with
                                | CpuFlush _ => InitEvent 0
                                | EventLab e => e
                                | _ => InitEvent 1
                                end).
    exists (map extract_event (List.seq 0 (trace_index r))).
    ins. desc.
    replace x with (extract_event (trace_index x)).
    2: { unfold extract_event.
         unfold trace_labels. by rewrite trace_index_simpl. }
    apply in_map. by apply in_seq0_iff. }
  assert (~ writes ≡₁ ∅) as HAS_WRITES.
  { red. ins.
    forward eapply (@no_writes_no_buffer (exact_tid r) (loc r) (trace_index r)) as BUF_EMPTY; eauto.
    { contra GE. forward eapply (proj2 (ge_default (trace_index r))); auto.
      unfold trace_labels. destruct r; desf; rewrite trace_index_simpl; auto; by unfolder'. }
    { ins. red. ins. desc.
      apply le_lt_or_eq in H2. des.
      2: { unfold write2prop in H2. destruct (excluded_middle_informative _).
           2: { clear H2; rewrite trace_index_simpl' in n; vauto. }
           destruct (constructive_indefinite_description _ _). simpl in *. desc.
           destruct r; desf.
           subst. rewrite trace_index_simpl' with (e := ThreadEvent _ _ _) in THREAD_PROP; auto.
           generalize THREAD_PROP. unfolder'. intuition. }
      apply (proj1 H e). rewrite Heqwrites. splits; auto. }
    simpl in BUF_EMPTY. rewrite <- Heqst in BUF_EMPTY. simpl in BUF_EMPTY.
    by rewrite BUF in BUF_EMPTY. }
  assert (strict_total_order writes trace_before) as TOTAL.
  { cdes tb_SPO.
    red. split; auto.
    forward eapply (@is_total_mori _ Eninit writes) as H.
    { red. basic_solver. }
    { eapply (inclusion_refl2 trace_before). }
      by apply H. }
  forward eapply (@latest_fin _ _ trace_before WRITES_FIN HAS_WRITES) as LATEST'; [vauto| ].
  apply latest_unique in LATEST'.
  2: { apply antisymmetric_inclusion with (r := trace_before); [| basic_solver].
       apply strict_partial_order_antisymmetric. by cdes tb_SPO. }
  unfold unique in LATEST'. desc. exists x. split; [vauto| ].
  red in LATEST'. desc. by rewrite Heqwrites in LATEST'. 
Qed. 

Lemma read_source_fpga r (Er: EG r) (Rr: is_rd_resp r):
  exists! w, rf G w r.
Proof.
  assert (is_r r) as GEN_R. { unfold is_cpu_rd, is_r in *; desf. }
  cut ((exists! w, (EG ∩₁ is_w) w /\ rf' w r) /\ (EG ∩₁ is_r) r).
  { ins. unfold unique in H. desc.
    exists x. red. splits.
    { apply seq_eqv_lr. splits; auto. }
    ins. desc. apply seq_eqv_lr in H3. desc. apply H1. splits; auto. }
  split; [| vauto].
  unfold rf'.
  do 2 red in Er. des.
  { exfalso. eapply init_non_r; eauto. }
  (* red in Er. pose proof Er as Er_.  *)
  (* apply trace_in_nth with (d := def_lbl) in Er. desc. *)
  unfold state_before_event.
  forward eapply (TSi (trace_index r)) with (d := def_lbl) as TSi; eauto.
  { contra GE.
    pose proof (proj2 (ge_default (trace_index r)) GE).
    unfold def_lbl in H. by rewrite trace_index_simpl' in H; vauto. }
  
  rewrite trace_index_simpl in TSi; auto.
  remember (states (trace_index r)) as st. destruct st as [wp rp ups downs mem bufs].
  destruct (excluded_middle_informative (is_cpu_rd r)).
  { exfalso. unfold is_cpu_rd, is_rd_resp in *; desf. }
  { remember (fun e : Event => loc e = loc r /\ vis_lt' e r /\ EG e /\ is_w e) as writes.
    cut (exists! w, latest_of_by writes (co G) w).
    {
      subst writes. intros [w [LATEST UNIQ]]. red in LATEST. desc.
      exists w.
      assert (is_w w). { unfolder'; desf. }
      red.
      { split.
        { split; vauto.
          red. splits; vauto. intros. specialize (LATEST0 y S').
          red in LATEST0. des; [vauto| ]. simpl in LATEST0. apply seq_eqv_lr in LATEST0. desc. red in LATEST4. desc. vauto. }
        ins. desc.
        assert (latest_of_by
            (fun e : Event =>
             loc e = loc r /\
             vis_lt' e r /\ EG e /\ is_w e)
            vis_lt' x') as H2 by desf; vauto.
        red in H1. desc. apply UNIQ. red. splits; vauto.
        ins. specialize (H3 y S').
        red in H3. des; [vauto| ].
        red. right. apply seq_eqv_lr. splits; vauto.
        red. split; auto. congruence. }
    }
    apply latest_unique.
    { apply antisymmetric_inclusion with (r := co G); [| basic_solver].
      apply strict_partial_order_antisymmetric.
      by destruct (co_loc_total (loc r)). }
    assert (set_finite writes) as WRITES_FIN.
    { arewrite (writes ⊆₁ fun e => loc e = loc r /\ vis_lt' e r) by basic_solver.
      pose proof (fsupp_vis_loc r) as [findom FINDOM].
      red. exists findom. ins. desc. apply FINDOM. red. split; auto. }
    assert (~ writes ≡₁ ∅) as HAS_WRITES.
    { apply set_nonemptyE. exists (InitEvent (loc r)).
      subst. splits; vauto. }
    assert (strict_total_order writes (co G)) as TOTAL.
    { red. split.
      { by destruct (co_loc_total (loc r)). }
      forward eapply (@is_total_mori _ (EG ∩₁ is_w ∩₁ (fun a => loc a = loc r)) writes) as H.
      { subst. unfold Basics.flip. basic_solver. }
      { eapply (inclusion_refl2 (co G)). }
      apply H, co_loc_total. }
    apply latest_fin; eauto. }
Qed.

Lemma read_source r (Er: EG r) (Rr: is_r r):
  exists! w, rf G w r.
Proof.
  assert (is_cpu_rd r \/ is_rd_resp r) by (destruct r; desf; vauto).
  destruct H as [CPU | FPGA].
  - apply read_source_cpu; vauto.
  - apply read_source_fpga; vauto.
Qed.

Lemma no_vis_lt_init e l (VIS: vis_lt' e (InitEvent l)): False.
Proof.
  do 2 red in VIS. des.
  { red in VIS. desc. by destruct (proj1 Eninit_non_init (InitEvent l)). }
  apply seq_eqv_lr in VIS. desc. by destruct (proj1 Eninit_non_init (InitEvent l)).
Qed.

Lemma winit_helper ind w l (DOM: NOmega.lt_nat_l ind (trace_length tr))
      (LATEST : latest_of_by
             (fun e' : Event =>
              loc e' = l /\ (is_init e' \/ vis' e' < ind) /\ EG e' /\ is_w e')
             vis_lt' w)
      (W_: is_init w): 
  sh_mem (states ind) l = valw w.
Proof.
  red in LATEST. desc.
  destruct w; vauto. unfold loc, valw. simpl in *. clear LATEST1. 
  generalize dependent DOM. generalize dependent LATEST0. induction ind.
  { ins.  by rewrite <- TS0. }
  ins.
  rewrite <- IHind.
  3: { destruct (trace_length tr); vauto. simpl in *. lia. }
  2: { ins. desc. apply LATEST0. splits; vauto. des; auto. }
  symmetry.
  forward eapply (TSi ind) with (d := def_lbl) as TSi. 
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  inversion TSi; try done.
  {  
  simpl. destruct (classic (loc = x)).
  2: { rewrite updo; auto. }
  subst x. rewrite upds. 
  forward eapply (@buffer_sources_upstream_wr ind channel) with (k :=0) (l := loc) (v := val) as [ind_w SRC].
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  { rewrite <- H0. simpl. by rewrite UPSTREAM. }
  simpl in SRC. desc.
  remember (FpgaEvent (Fpga_write_resp channel loc val) ind_w meta) as w. 
  specialize (LATEST0 w). specialize_full LATEST0.
  { splits; try (by vauto). right. cut (vis' (FpgaEvent (Fpga_write_resp channel loc val) ind_w meta) = ind); [ins; subst w; lia| ].
    unfold vis'. destruct (excluded_middle_informative _ ).
    { unfolder'; desf. }
    destruct (excluded_middle_informative _).
    2: { desf. }
    unfold write2prop.
    destruct (excluded_middle_informative _).
    { exfalso. rewrite trace_index_simpl' in c. desf. vauto. }
    destruct (excluded_middle_informative _).
    2: { exfalso. rewrite trace_index_simpl' in n1. desf. vauto. }
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    rewrite trace_index_simpl', <- Heqw in *; try (by vauto).
    red in WRITE_POS. desc.
    replace (same_chan (EventLab w)) with (in_chan channel) in *.
    2: { symmetry. subst w.
        apply set_extensionality. 
        unfold same_chan, in_chan. simpl. red. splits; red; ins; desc; vauto. }
    rewrite WRITE_POS, Nat.add_0_r in W_P_CORR.
    apply nth_such_unique with (k := count_upto (is_fpga_prop ∩₁ in_chan channel) ind) (F := is_fpga_prop ∩₁ in_chan channel); vauto.
    red. split; auto. unfold trace_labels. by rewrite <- H. }
  red in LATEST0. des; [vauto| ]. exfalso. eapply no_vis_lt_init; eauto. 
  }
  simpl. destruct (classic (loc = x)).
  2: { rewrite updo; auto. }
  subst x. rewrite upds. 
  forward eapply (@buffer_sources_cpu ind thread) with (k :=0) (l := loc) (v := val) as [ind_w SRC].
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  { rewrite <- H0. simpl. by rewrite CPU_BUF. }
  simpl in SRC. desc.
  remember (ThreadEvent thread ind_w (Cpu_store loc val)) as w. 
  specialize (LATEST0 w). specialize_full LATEST0.
  { splits; try (by vauto). right. cut (vis' (ThreadEvent thread ind_w (Cpu_store loc val)) = ind); [ins; subst w; lia| ].
    unfold vis'. destruct (excluded_middle_informative _ ).
    2: { generalize n. unfolder'. intuition. }
    unfold write2prop. destruct (excluded_middle_informative _).
    2: { rewrite trace_index_simpl' in n; vauto. }
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    rewrite trace_index_simpl', <- Heqw in *; try (by vauto).
    red in WRITE_POS. desc.
    replace (same_thread (EventLab w)) with (in_cpu_thread thread) in *.
    2: { symmetry. subst w. apply RESTR_EQUIV. }
    rewrite WRITE_POS, Nat.add_0_r in W_P_CORR.
    apply nth_such_unique with (k := count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) ind) (F := is_cpu_prop ∩₁ in_cpu_thread thread); vauto.
    red. split; auto. unfold trace_labels. by rewrite <- H. }
  red in LATEST0. des; [vauto| ]. exfalso. eapply no_vis_lt_init; eauto. 
Qed. 

Lemma latest_mem_value_kept' ind w l
      (DOM: NOmega.lt_nat_l ind (trace_length tr))
      (LATEST: latest_of_by (fun e' => loc e' = l /\ (vis' e' < ind) /\ EG e' /\ is_w e') vis_lt' w):
  sh_mem (states ind) l = valw w.
Proof.
  red in LATEST. desc. apply lt_diff in LATEST1. desc. rewrite LATEST1 in *.
  clear dependent ind.
  induction d.
  { assert (NOmega.lt_nat_l (vis' w) (trace_length tr)) as DOM'.
    { destruct (trace_length tr); vauto. simpl in *. lia. }
    do 2 red in LATEST2. des.      
    { destruct w; vauto. 
      apply winit_helper; vauto. red. splits; vauto. ins. desc.
      des.
      { destruct y; vauto. }
      apply LATEST0. splits; vauto. }
    destruct w.
    3: { by destruct (proj1 Eninit_non_init (InitEvent x)). }
    { destruct e; [done| | done].
      remember (ThreadEvent thread index (Cpu_store x v)) as w.      
      assert (vis' w = write2prop (trace_index w)) as VISw.
      { apply cpuw_vis. subst w. unfolder'. intuition. }
      rewrite VISw in *. 
      forward eapply (TSi (vis' w)) with (d := def_lbl) as TSi.
      { congruence. }
      assert ((is_cpu_prop ∩₁ same_thread (trace_labels (trace_index w))) (trace_nth (vis' w) tr def_lbl)) as PROP.
      { unfold write2prop in VISw. destruct (excluded_middle_informative _).
        2: { generalize n. rewrite trace_index_simpl'; auto. subst w.
             unfolder'. intuition. }
        destruct (constructive_indefinite_description _ _). desc. simpl in *.
        subst x0. auto. }
      inversion TSi.
      all: try (by generalize PROP; rewrite <- H; unfolder'; intuition).
      assert (thread0 = thread); [| subst thread0].
      { red in PROP. desc.
        rewrite trace_index_simpl' in PROP0; auto. rewrite <- H in PROP0.
        subst w. red in PROP0. unfold lbl_thread in PROP0.
        desc. by inversion PROP0. }      
      rewrite Nat.add_1_r, <- VISw, <- H2. simpl.
      forward eapply (@buffer_sources_cpu (vis' w) thread) with (k := 0) (l := loc) (v :=val) as [ind_w INDw].
      { destruct (trace_length tr); vauto. simpl in *. lia. }
      { rewrite <- H0. simpl. by rewrite CPU_BUF. }
      simpl in INDw. desc.
      remember (ThreadEvent thread ind_w (Cpu_store loc val)) as w'.
      rewrite Nat.add_0_r in WRITE_POS.
      cut (w' = w).
      { ins. subst w' w. inversion H1. subst.
        unfold loc, valw. simpl. by apply upds. }
      apply ti_inj; try (by vauto).
      apply (@nth_such_unique (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) (vis' w))
                              (cpu_write' ∩₁ in_cpu_thread thread)); auto.
      unfold write2prop in VISw. destruct (excluded_middle_informative _).
      2: { generalize n. rewrite trace_index_simpl'; auto. subst w.
           unfolder'. intuition. }
      destruct (constructive_indefinite_description _ _). desc. simpl in *. subst x0.
      rewrite trace_index_simpl' in *; auto.
      replace (same_thread (EventLab w)) with (in_cpu_thread thread) in *.
      2: { symmetry. subst w. apply RESTR_EQUIV. }
      split; auto.
      rewrite trace_index_simpl'; auto. subst w. vauto. }
      destruct e.
      all: try by done.
      remember (FpgaEvent (Fpga_write_resp c x v) index m) as w.      
      assert (vis' w = write2prop (trace_index w)) as VISw.
      { apply fpgaw_vis. subst w. unfolder'. intuition. }
      rewrite VISw in *. 
      forward eapply (TSi (vis' w)) with (d := def_lbl) as TSi.
      { congruence. }
      assert ((is_fpga_prop ∩₁ same_chan (trace_labels (trace_index w))) (trace_nth (vis' w) tr def_lbl)) as PROP.
      { unfold write2prop in VISw. destruct (excluded_middle_informative _).
        { generalize c0. rewrite trace_index_simpl'; auto. subst w.
             unfolder'. intuition. }
        destruct (excluded_middle_informative _).
        2: { generalize n0. rewrite trace_index_simpl'; auto. subst w.
             unfolder'. intuition. }
        destruct (constructive_indefinite_description _ _). desc. simpl in *.
        subst x0. auto. }
      inversion TSi.
      all: try (by generalize PROP; rewrite <- H; unfolder'; intuition).
      assert (channel = c); [| subst channel].
      { red in PROP. desc.
        rewrite trace_index_simpl' in PROP0; auto. rewrite <- H in PROP0.
        subst w. red in PROP0.
        desc. by inversion PROP0. }      
      (* assert (meta = m); [| subst meta].
      { red in PROP. desc.
        rewrite trace_index_simpl' in PROP0; auto. rewrite <- H in PROP0.
        subst w. red in PROP0. unfold lbl_thread in PROP0.
        desc. by inversion PROP0. }       *)
      rewrite Nat.add_1_r, <- VISw, <- H2. simpl.
      forward eapply (@buffer_sources_upstream_wr (vis' w) c) with (k := 0) (l := loc) (v :=val) as [ind_w INDw].
      { destruct (trace_length tr); vauto. simpl in *. lia. }
      { rewrite <- H0. simpl. by rewrite UPSTREAM. }
      simpl in INDw. desc.
      (* remember (ThreadEvent thread ind_w (Cpu_store loc val)) as w'. *)
      remember (FpgaEvent (Fpga_write_resp c loc val) ind_w meta) as w'.
      rewrite Nat.add_0_r in WRITE_POS.
      cut (w' = w).
      { ins. subst w' w. inversion H1. subst.
        unfold loc, valw. simpl. by apply upds. }
      apply ti_inj; try (by vauto).
      apply (@nth_such_unique (count_upto (is_fpga_prop ∩₁ in_chan c) (vis' w))
                              (fpga_write' ∩₁ in_chan c)); auto.
      unfold write2prop in VISw. 
      destruct (excluded_middle_informative _).
      { generalize c0. rewrite trace_index_simpl'; auto. subst w.
           unfolder'. intuition. }
      destruct (excluded_middle_informative _).
      2: { generalize n0. rewrite trace_index_simpl'; auto. subst w.
           unfolder'. intuition. }
      destruct (constructive_indefinite_description _ _). desc. simpl in *. subst x0.
      rewrite trace_index_simpl' in *; auto.
      replace (same_chan (EventLab w)) with (in_chan c) in *.
      2: { ins. apply set_extensionality. 
      unfold same_chan, in_chan. simpl. red. splits; red; ins; desc; vauto. }
      (* 2: { symmetry. subst w. apply RESTR_EQUIV. } *)
      split; auto.
      rewrite trace_index_simpl'; auto; subst w; vauto.
    }
  specialize_full IHd.
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  { ins. desc. apply LATEST0. splits; vauto. lia. }
  rewrite <- IHd. symmetry. replace (vis' w + S (S d)) with (S (vis' w + (S d))) by lia.
  assert (NOmega.lt_nat_l (vis' w + S d) (trace_length tr)) as DOM'. 
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  forward eapply (TSi (vis' w + S d)) with (d := def_lbl) as TSi; auto. 
  inversion TSi; auto.
  2: { simpl. destruct (classic (loc = l)).
    2: { rewrite updo; auto. }
    subst loc. exfalso. 
    forward eapply (@buffer_sources_cpu (vis' w + S d) thread) with (k := 0) (l := l) (v := val) as [ind_w INDw].
    { destruct (trace_length tr); vauto. }
    { rewrite <- H0. simpl. by rewrite CPU_BUF. }
    simpl in INDw. desc.
    remember (ThreadEvent thread ind_w (Cpu_store l val)) as w'.
    assert (vis' w' = vis' w + S d) as VISw'.
    { rewrite cpuw_vis; [| subst w'; unfolder'; intuition].
      (* red in WRITE_POS. desc. rewrite Nat.add_0_r in WRITE_POS. *)
      unfold write2prop in PROP_AFTER. unfold write2prop.
      destruct (excluded_middle_informative _).
      2: { rewrite trace_index_simpl' in *; vauto. unfolder'; desf. }
      destruct (constructive_indefinite_description _ _). desc. simpl in *.
      replace (same_thread (trace_labels (trace_index w'))) with (in_cpu_thread thread) in *.
      2: { symmetry. rewrite trace_index_simpl'; auto. 
           subst w'. apply RESTR_EQUIV. }
      apply (@nth_such_unique (count_upto (cpu_write' ∩₁ in_cpu_thread thread) (trace_index w')) (is_cpu_prop ∩₁ in_cpu_thread thread)).
      { vauto. }
      red. splits.
      { red in WRITE_POS. lia. }
      unfold trace_labels. rewrite <- H. vauto. }
    specialize (LATEST0 w'). specialize_full LATEST0.
    { splits; vauto. lia. }
    red in LATEST0. des.
    { subst w. lia. }
    do 2 red in LATEST0. des.
    { red in LATEST0. desc. by destruct (proj1 Eninit_non_init w'). }
    apply seq_eqv_lr in LATEST0. desc. lia. }

  { simpl. destruct (classic (loc = l)).
    2: { rewrite updo; auto. }
    subst loc. exfalso. 
    forward eapply (@buffer_sources_upstream_wr (vis' w + S d) channel) with (k := 0) (l := l) (v := val) as [ind_w INDw].
    { destruct (trace_length tr); vauto. }
    { rewrite <- H0. simpl. by rewrite UPSTREAM. }
    simpl in INDw. desc.
    remember (FpgaEvent (Fpga_write_resp channel l val) ind_w meta) as w'.
    assert (vis' w' = vis' w + S d) as VISw'.
    { rewrite fpgaw_vis; [| subst w'; unfolder'; intuition].
      (* red in WRITE_POS. desc. rewrite Nat.add_0_r in WRITE_POS. *)
      unfold write2prop in PROP_AFTER. unfold write2prop.
      destruct (excluded_middle_informative _).
      { exfalso. clear PROP_AFTER. rewrite trace_index_simpl' in c; vauto. }
      destruct (excluded_middle_informative _).
      2: { exfalso. clear PROP_AFTER. rewrite trace_index_simpl' in n0; vauto; unfolder'; desf. }
      destruct (constructive_indefinite_description _ _). desc. simpl in *.
      replace (same_chan (trace_labels (trace_index w'))) with (in_chan channel) in *.
      2: { rewrite trace_index_simpl'. apply set_extensionality. unfold same_chan, in_chan in *. simpl. red. splits; red; ins; desc; vauto. vauto. }
      apply (@nth_such_unique (count_upto (fpga_write' ∩₁ in_chan channel) (trace_index w')) (is_fpga_prop ∩₁ in_chan channel)).
      { vauto. }
      red. splits.
      { red in WRITE_POS. lia. }
      unfold trace_labels. rewrite <- H. vauto. }
    specialize (LATEST0 w'). specialize_full LATEST0.
    { splits; vauto. lia. }
    red in LATEST0. des.
    { subst w. lia. }
    do 2 red in LATEST0. des.
    { red in LATEST0. desc. by destruct (proj1 Eninit_non_init w'). }
    apply seq_eqv_lr in LATEST0. desc. lia. }
Qed. 


Lemma latest_mem_value_kept ind w l
      (DOM: NOmega.lt_nat_l ind (trace_length tr))
      (LATEST: latest_of_by (fun e' => loc e' = l /\ (is_init e' \/ vis' e' < ind) /\ EG e' /\ is_w e') vis_lt' w):
  sh_mem (states ind) l = valw w.
Proof.
  destruct (classic (is_init w)) as [W_ | W_]. 
  { by apply winit_helper. }
  apply latest_mem_value_kept'; auto.
  red in LATEST. desc. des; [done| ]. 
  red. splits; vauto. ins. desc. apply LATEST0. splits; vauto. 
Qed. 

Lemma latest_buf_value_read' thread w ind l val
      (TB_LATEST:
         latest_of_by
              (fun e => loc e = l /\ trace_index e < ind /\
              exact_tid e = thread /\ Eninit e /\ is_cpu_wr e) trace_before w
         /\ ind < vis' w )
      (BUF_LATEST: let bufs := cpu_bufs (states ind) in 
                   latest_buffered (bufs thread) l (Some val))
      (DOM: NOmega.lt_nat_l ind (trace_length tr)):
  val = valw w.
Proof.
  set (prev_write := fun i => (fun e : Event =>
                 loc e = l /\
                 trace_index e < i 
                 /\ exact_tid e = thread /\ Eninit e /\ is_cpu_wr e)).
  fold (prev_write ind) in TB_LATEST.
  generalize dependent w. generalize dependent val. generalize dependent DOM.
  set (P := fun ind => NOmega.lt_nat_l ind (trace_length tr) ->
  forall val : Val,
  (let bufs := cpu_bufs (states ind) in
   latest_buffered (bufs thread) l (Some val)) ->
  forall w : Event, latest_of_by (prev_write ind) trace_before w /\ ind < vis' w
               ->  val = valw w).
  cut (P ind); [done| ].
  apply (@lt_wf_ind ind P). clear ind. intros ind IH.
  red. intros DOM val LATEST_BUFFERED w LATEST_OF.
  destruct ind as [| ind_prev].
  { rewrite <- TS0 in LATEST_BUFFERED. by inversion LATEST_BUFFERED. }
  remember (S ind_prev) as ind_cur.
  specialize (IH ind_prev). specialize_full IH; [lia| ].
  subst P. simpl in IH.
  assert (NOmega.lt_nat_l ind_prev (trace_length tr)) as DOM_prev.
  { destruct (trace_length tr); auto. simpl in *. lia. }
  specialize (IH DOM_prev).

  (* check: if e_prev is not W@loc, is it always latest_of_by for prev index? *)
  remember (trace_nth ind_prev tr def_lbl) as e_prev.
  (* specify just one part of statement for now*)
  desc.
  destruct (classic (trace_index w = ind_prev)) as [W_IND | W_IND]. 
  { pose proof (TSi ind_prev DOM_prev def_lbl) as TSi. simpl in TSi.
    red in LATEST_OF. desc. red in LATEST_OF. desc.
    rewrite <- W_IND, trace_index_simpl in TSi; auto.    
    assert (w = ThreadEvent thread (index w) (Cpu_store l (SyEvents.valw w))) as W.
    { destruct w.
      3: { by destruct (proj1 Eninit_non_init (InitEvent x)). }
      { simpl.
        simpl in LATEST_OF3. subst thread0. f_equal.
        destruct l; auto.
        { generalize LATEST_OF5. unfolder'. desf. }
        { generalize LATEST_OF5. unfolder'. desf. } }
      desf. }
    rewrite W in TSi at 2. inversion TSi. subst loc val0 thread0.
    rewrite W_IND in H5. rewrite Heqind_cur, <- H5 in LATEST_BUFFERED.
    move LATEST_BUFFERED at bottom.
    simpl in LATEST_BUFFERED. rewrite upds in LATEST_BUFFERED.
    inversion LATEST_BUFFERED; [discriminate| ].
    inversion LATEST_VALUE. subst val0. clear LATEST_VALUE. 
    simpl in LATEST_BUF. rewrite filter_app, length_app in LATEST_BUF.
    simpl in LATEST_BUF. rewrite Nat.eqb_refl in LATEST_BUF.
    rewrite nth_error_app2 in LATEST_BUF.
    2: { simpl. lia. }
    simpl in LATEST_BUF. rewrite Nat.add_sub, Nat.sub_diag in LATEST_BUF.
    simpl in LATEST_BUF. vauto. }
  assert (latest_of_by (prev_write ind_prev) trace_before w) as PREV_LATEST.
  { subst prev_write. red in LATEST_OF. desc. 
    subst ind_cur.
    move LATEST_OF2 at bottom. 
    red in LATEST_OF2. apply Peano.le_S_n, le_lt_or_eq in LATEST_OF2. des; [|done].
    red. splits; vauto.
    ins. desc. apply LATEST_OF1. splits; vauto. }

  specialize IH with (val := val) (w := w). apply IH.
  2: { splits; [done | lia]. }
  pose proof (TSi ind_prev DOM_prev def_lbl) as TSi. simpl in TSi.
  rewrite <- Heqe_prev in TSi.
  rewrite Heqind_cur in LATEST_BUFFERED.
  inversion TSi.
  all: try (by congruence).
  all: try by (simpl; destruct H; simpl in *; vauto).
  { rewrite <- H in LATEST_BUFFERED. simpl in *.
    destruct (classic (thread0 = thread)).
    2: { rewrite updo in LATEST_BUFFERED; auto. }
    subst thread0. rewrite upds in LATEST_BUFFERED.
    inversion LATEST_BUFFERED; [discriminate| ].
    inversion LATEST_VALUE. subst val1. clear LATEST_VALUE.
    simpl in LATEST_BUF. rewrite filter_app, length_app in LATEST_BUF.
    simpl in LATEST_BUF. 
    destruct (Nat.eqb loc l) eqn:L.
    2: { simpl in LATEST_BUF. rewrite app_nil_r, Nat.add_0_r in LATEST_BUF. vauto. }
    apply beq_nat_true in L. subst loc.
    exfalso. apply W_IND.
    remember (Cpu_store l val0) as lbl'. 
    remember (ThreadEvent thread index lbl') as w'. 
    assert (Eninit w') as E'w'.
    { red. rewrite H1. subst. by apply trace_nth_in. }
    forward eapply (@ti_uniq (trace_index w') ind_prev thread index lbl') as IND; eauto.
    { rewrite trace_index_simpl; vauto. }
    { rewrite trace_index_simpl; vauto. }
    assert (latest_of_by (prev_write ind_cur) trace_before w').
    { red. split.
      { red. splits; vauto. }
      ins. red in S'. desc. rewrite Heqind_cur in S'0. apply lt_n_Sm_le, le_lt_or_eq in S'0.
      unfold trace_before. red. des; [by vauto| ].
      left. apply ti_inj; vauto. }
    cut (w' = w); [by ins; vauto| ]. 
    forward eapply (@latest_unique _ (prev_write ind_cur) trace_before) as UNIQ; eauto.
    { cdes tb_SPO. cdes tb_SPO0. by apply trans_irr_antisymmetric. }
    unfold unique in UNIQ. desc. rewrite <- UNIQ0; auto.
    rewrite (UNIQ0 w'); auto. }
  rewrite <- H in LATEST_BUFFERED. simpl in *.
  destruct (classic (thread0 = thread)).
  2: { rewrite updo in LATEST_BUFFERED; auto. }
  subst thread0. rewrite upds in LATEST_BUFFERED. rewrite CPU_BUF.
  inversion LATEST_BUFFERED; [discriminate| ].
  inversion LATEST_VALUE. subst val1. clear LATEST_VALUE. 
  simpl in LATEST_BUF. 
  eapply latest_loc; eauto. simpl in *.
  destruct (Nat.eqb loc l); [| done].
  simpl. rewrite Nat.sub_0_r.
  remember (filter (fun loc_val : Loc * Val => fst loc_val =? l) cpu_buf') as buf_flt.
  destruct buf_flt; [done |]. simpl in *. by rewrite Nat.sub_0_r in LATEST_BUF.
Qed.
  

Lemma latest_buf_value_read thread w r val
      (TB_LATEST:
         latest_of_by
           (fun e => loc e = loc r /\ trace_before e r /\
              exact_tid e = thread /\ Eninit e /\ is_cpu_wr e) trace_before w)
      (BUF_LATEST: let bufs := cpu_bufs (states (trace_index r)) in 
                   latest_buffered (bufs thread) (loc r) (Some val))
      (DOM: NOmega.lt_nat_l (trace_index r) (trace_length tr))
      (Rr: is_cpu_rd r)
      (E'r: Eninit r)
      (TID_R: exact_tid r = thread):
  val = valw w.
Proof.
  eapply latest_buf_value_read' with (ind := trace_index r) (l := loc r) (thread := thread); auto.
  desc. 
  unfold trace_before at 1 in TB_LATEST.
  red in TB_LATEST. desc.
  pose proof (r_vis r Rr) as VISr. 
  unfold latest_of_by. splits; auto.
  remember (states (trace_index r)) as st. destruct st as [mem bufs]. simpl in *.
  assert (filter (fun loc_val : Loc * Val => fst loc_val =? loc r) (cpu_bufs (exact_tid r)) <> nil) as BUF_NEMPTY. 
  1: { unfold state_before_event. 
       inversion BUF_LATEST; [discriminate| ].
       simpl in LATEST_BUF. red. ins.
       replace (exact_tid r) with thread in H.
       by rewrite H in LATEST_BUF. }
  
  apply rf_before_prop; vauto.
  2: { unfold state_before_event. by rewrite <- Heqst. }
  simpl. apply seq_eqv_lr. unfold set_inter. splits; vauto.
  1,3: by (unfolder'; unfold is_w, is_r; desf).
  red. unfold state_before_event. rewrite <- Heqst.
  destruct (excluded_middle_informative).
  2: vauto.
  destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r)
                   (cpu_bufs (exact_tid r))); vauto.
  (* Set Printing All. *)
  red. splits; vauto. ins. apply TB_LATEST0. desc. splits; vauto. congruence. 
Qed.

Lemma rf_same_value w r (RF: rf G w r): valw w = valr r.
Proof.
  simpl in RF. apply seq_eqv_lr in RF. destruct RF as [W [RF [Er Rr]]].
  do 2 red in Er. des; [by destruct (init_non_r r)| ]. 
  red in RF. unfold state_before_event in RF.
  (* pose proof TR as TR'. apply LTS_traceE in TR'. desc. *)
  destruct (excluded_middle_informative (is_cpu_rd r)).
  {
  remember (states (trace_index r)) as st.
  assert (NOmega.lt_nat_l (trace_index r) (trace_length tr)) as DOMr. 
  { contra GE. forward eapply (proj2 (ge_default (trace_index r))); auto.
    rewrite trace_index_simpl'; auto. unfolder'. ins. vauto. }
  forward eapply (TSi (trace_index r)) with (d := def_lbl) as TSi; eauto. 
  destruct st as [wp rp ups downs sh_mem bufs].
  rewrite trace_index_simpl in TSi; auto.
    destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r)
                    (bufs (exact_tid r))) eqn:BUF_FLT.
    { cut (sh_mem (loc r) = valw w). 
      { ins.            
        inversion TSi; vauto.
        { rewrite <- Heqst in H1. inversion H1. subst.
          unfold SyEvents.loc in BUF_FLT. simpl in BUF_FLT.        
          inversion CPU_BUF; vauto. simpl in LATEST_BUF.  
          by rewrite BUF_FLT in LATEST_BUF. }
        { rewrite <- Heqst in H1. inversion H1. subst.
          unfold SyEvents.loc in H. simpl in H.
          by unfold valr. } }
      
      forward eapply (@latest_mem_value_kept (trace_index r) w (loc r)); vauto.
      2: by rewrite <- Heqst.
      (* { by rewrite trace_index_simpl'. } *)
      red. red in RF. desc. splits; vauto.
      { do 2 red in RF1. des.
        { red in RF1. desc. by left. }
        right. apply seq_eqv_lr in RF1. desc.
        by rewrite (r_vis r) in RF4. }
      ins. desc.
      (* des. *)
      destruct (classic (is_init y)). 
      { do 2 red in RF2. destruct RF2. 
        { destruct w, y; vauto. left. f_equal. unfold loc in *. simpl in *.
          congruence. }
        red. right. red. left. split; vauto. }
      des; [done| ]. do 2 red in S'1. des; [done| ]. 
      
      apply RF0. splits; vauto. do 2 red. des; vauto. 
      right. apply seq_eqv_lr. splits; vauto.
      by rewrite (r_vis r). }
    
    inversion TSi; vauto.
    { rewrite <- Heqst in H0. inversion H0. subst.
      unfold valr, valr, SyEvents.loc in *. simpl in *. 
      cut (val = valw w).
      { ins. }
      desc. 
      eapply (@latest_buf_value_read thread w (ThreadEvent thread index (Cpu_load loc val)) val); eauto.
      simpl. rewrite <- Heqst. vauto. }
      (* split; vauto. red. splits; vauto.  *)
    { rewrite <- Heqst in H0. inversion H0. subst.
      unfold SyEvents.loc in BUF_FLT. simpl in BUF_FLT. 
      inversion CPU_BUF; vauto. by rewrite BUF_FLT in EMPTY_BUF. } }

    assert (is_rd_resp r) as FPGA_RD by (destruct r; desf).

    remember (states (read2mem_read (trace_index r))) as st.
    assert (NOmega.lt_nat_l (trace_index r) (trace_length tr)) as DOMr. 
    { contra GE. forward eapply (proj2 (ge_default (trace_index r))); auto.
      rewrite trace_index_simpl'; auto. unfolder'. ins. vauto. }
    assert (NOmega.lt_nat_l (read2mem_read (trace_index r)) (trace_length tr)) as DOMr0. 
    { forward eapply rd_resp_after_memread; eauto. ins. eapply NOmega.lt_lt_nat; eauto. }
    forward eapply (TSi (read2mem_read (trace_index r))) with (d := def_lbl) as TSi; eauto. 
    destruct st as [wp rp ups downs sh_mem bufs].

      cut (sh_mem (loc r) = valw w). 
      (* TODO: can be generalized to reason about fpga read source *)
      { ins.            
        rewrite <- H.
        (* prove that a read gets whatever is in memory during it's mem visit 
           read_req -> MemoryRead at read2mem_read with same loc and same meta ->
           -> whatever is in this loc goes back to downstream with same loc and meta
           -> if downstreamRead (l, v, m) enters downstream, then
         *)
        unfold read2mem_read in TSi, Heqst.
        destruct (excluded_middle_informative (fpga_read_resp' (trace_labels (trace_index r)))).
        2: { rewrite trace_index_simpl' in n0; vauto. }
        destruct (constructive_indefinite_description); simpl in *.
        desf.
        destruct THREAD_PROP as [MEM_READ SAME_CH].
        unfold trace_labels in MEM_READ.
        rewrite <- Heqst in TSi.
        inversion TSi; vauto.
        all: try by (unfold fpga_mem_read' in MEM_READ; desf).
        assert (SyEvents.loc r = loc). { admit. }
        rewrite H0.     
        admit.
      } 
      (* { ins.            
        inversion TSi; vauto.
        (* { rewrite <- Heqst in H1. inversion H1. subst.
          unfold SyEvents.loc in BUF_FLT. simpl in BUF_FLT.        
          inversion CPU_BUF; vauto. simpl in LATEST_BUF.  
          by rewrite BUF_FLT in LATEST_BUF. } *)
        { rewrite <- Heqst in H1. inversion H1. subst.
          unfold SyEvents.loc in H. simpl in H.
          simpl. admit.  } } *)
      
      forward eapply (@latest_mem_value_kept (read2mem_read (trace_index r)) w (loc r)); vauto.
      { red. desf. destruct RF as [[LOC [VIS [EGW IS_W]]] LATEST]. splits; vauto.
        { unfold vis_lt' in VIS. destruct VIS.
          { left. destruct H. vauto. }
          right. destruct H as [EX [ENX [EY [VISLT ENY]]]].
          destruct ENX, ENY. rewrite <- H, H1 in *.
          erewrite (rd_rest_vis r FPGA_RD) in VISLT; eauto. }
        ins. red. 
        desf. 
        { destruct (classic (is_init w)). 
          - left. rewrite <- LOC in S'. unfold loc in S'. destruct y, w; desf.
          - right. red. left. split; vauto. destruct W. destruct H0; vauto. }
        forward eapply (LATEST y) as YW_REL; vauto.
        splits; vauto.
        destruct (classic (is_init y)).
        { left. split; vauto. }
        right.
        rewrite <- rd_rest_vis in S'0; vauto.
        apply seq_eqv_lr. splits; vauto.
        destruct S'1; desf. 
      }
      by rewrite <- Heqst.
Qed. 

(* Well formed *)

Lemma G_well_formed: Wf G.
Proof.
  split.
  pose proof WF as WF'.
  destruct WF'.
  { ins. desc. do 2 red in H. des; [vauto|].
    assert (~ is_init b).
    { destruct a, b; vauto. }
    do 2 red in H0. des; [vauto|].
    destruct a, b; vauto.
    3: { exfalso. by simpl in H3. }

    { red in H2. simpl in H2. subst index0.
    red in H, H0. apply trace_in_nth with (d := def_lbl) in H. apply trace_in_nth with (d := def_lbl) in H0. desc.
    simpl in *. red in TSO_TR_WF.
    specialize TSO_TR_WF with (d := def_lbl) (thread := thread0) (index1 := index) (index2 := index). 
    pose proof (Nat.lt_trichotomy n n0). des.
    2: { subst. congruence. }
    all: subst; specialize_full TSO_TR_WF; eauto; lia. }

    red in H2. simpl in H2. subst index0.
    red in H, H0. apply trace_in_nth with (d := def_lbl) in H. apply trace_in_nth with (d := def_lbl) in H0. desc.
    simpl in *. red in FPGA_TR_WF.
    pose proof (Nat.lt_trichotomy n n0). des.
    2: { subst. congruence. }
    { specialize FPGA_TR_WF with (d := def_lbl) (index1 := index) (index2 := index) (meta1 := m0) (meta2 := m). 
      subst; specialize_full FPGA_TR_WF; eauto; lia. }
    { specialize FPGA_TR_WF with (d := def_lbl) (index1 := index) (index2 := index) (meta1 := m) (meta2 := m0). 
      subst; specialize_full FPGA_TR_WF; eauto; lia. }}
  { simpl. basic_solver. }
  { simpl. basic_solver. }
  { simpl. rewrite inclusion_seq_eqv_r, inclusion_seq_eqv_l.
    unfold rf'. red. ins. desf.
    3: { unfold latest_of_by in H. by desc. }
    all: destruct (state_before_event y); destruct (filter _ _); unfold latest_of_by in H; by desc. }
  { admit. }
  { unfold functional. intros r w1 w2 RF1 RF2. unfold transp in *.
    forward eapply (@read_source r) as [w' [RF' UNIQ]]. 
    1, 2: generalize RF1; simpl; basic_solver.
    rewrite <- (UNIQ w1), <- (UNIQ w2); [auto|generalize RF2 |generalize RF1]; simpl; basic_solver. }
  { simpl. basic_solver. }
  { simpl. basic_solver. }
  { simpl. basic_solver. }
  { destruct (co_loc_total 0). by cdes H. }
  { ins. by destruct (co_loc_total x). }
  { red. ins. apply seq_eqv_lr in H. desc.
    red in H0. desc. do 2 red in H0. des.
    { by apply (proj1 Eninit_non_init x). }
    apply seq_eqv_lr in H0. desc. lia. }
  { simpl. unfold EG. basic_solver. }
  { split; [| basic_solver]. rewrite seq_eqv_r.
    red. ins. desc. apply seq_eqv_lr in H. desc. red in H1. desc.
    do 2 red in H1. des.
    { apply (proj1 Eninit_non_init y). red in H1. by desc. }
    apply seq_eqv_lr in H1. desc. by apply (proj1 Eninit_non_init y). }
  (* { ins. do 2 red in ACT. des.
    { by destruct e. }
    specialize (NO_TID0 e ACT). destruct e; vauto. } *)
  Admitted.



(* \\Well formed *)


Lemma Ax86ConsistentG: Ax86Consistent G.
Proof.
  Admitted.

Lemma TSO_op_implies_decl:
  (fun e => trace_elems tr (EventLab e)) ≡₁ acts G \₁ is_init /\ 
  Wf_fpga G /\
  Ax86Consistent G.
Proof.
  Admitted.


End SyLemmas.