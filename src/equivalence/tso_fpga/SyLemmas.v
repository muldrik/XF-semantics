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
Hypothesis (TSO_FAIR: TSO_fair tr states).
Hypothesis (RP_FAIR: readpool_fair tr states).
Hypothesis (EXACT_CHAN_READS: downstream_fair_alt tr).
Hypothesis (EXACT_CHAN_PROPS: mem_flush_fair_alt tr).
Hypothesis (EXACT_CHAN_MEMREADS: mem_read_fair_alt tr).

Definition Ecpu := fun e => trace_elems tr (EventLab e) /\ is_cpu e.
Definition Efpga := fun e => trace_elems tr (EventLab e) /\ is_fpga e.
Definition Eninit := fun e => trace_elems tr (EventLab e).

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

Lemma trace_index_label i e (ENINIT: Eninit e) (LAB: trace_labels i = EventLab e):
  trace_index e = i.
Proof.
  unfold trace_index. destruct (excluded_middle_informative _); [| done].
  destruct (constructive_indefinite_description _ _). desc.
  cut (x = i \/ x < i \/ x > i); [| lia].
  destruct WF.
  ins; desf.
  { destruct e.
  3: { exfalso. eapply (proj1 Eninit_non_init (InitEvent x0)); split; vauto. }
  { forward eapply (TSO_TR_WF x i); eauto.
    - apply not_default_found. rewrite LAB. desf.
    - lia. }
  forward eapply (FPGA_TR_WF x i); eauto.
    - apply not_default_found. rewrite LAB. desf.
    - lia. }
  destruct e.
  3: { exfalso. eapply (proj1 Eninit_non_init (InitEvent x0)); split; vauto. }
  { forward eapply (TSO_TR_WF i x); eauto; lia. }
  forward eapply (FPGA_TR_WF i x); eauto; lia. 
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

Definition count_upto S bound :=
  length (filterP S (map (fun i : nat => trace_nth i tr def_lbl) (List.seq 0 bound))).


Definition state_before_event e := states (trace_index e). 


Definition check {A: Type } S (elt: A) := length (ifP S elt then elt :: nil else nil).

Lemma check0 {A: Type } S (elt: A) (NS: ~ S elt): check S elt = 0.
Proof. unfold check. destruct (excluded_middle_informative (S elt)); vauto. Qed.  

Lemma check1 {A: Type } (S: A -> Prop) (elt: A) (SSS: S elt): check S elt = 1.
Proof. unfold check. destruct (excluded_middle_informative (S elt)); vauto. Qed.  

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

Lemma in_trace_Eninit i e 
      (Ei: trace_labels i = EventLab e)
      (IN: NOmega.lt_nat_l i (trace_length tr)):
  Eninit e.
Proof.
  unfold trace_labels in Ei.
  unfold Eninit.
  rewrite <- Ei.
  apply trace_nth_in.
  auto.
Qed.

Lemma Eninit_in_trace e (EN: Eninit e):
      NOmega.lt_nat_l (trace_index e) (trace_length tr).
Proof.
  unfold trace_index.
  destruct (excluded_middle_informative); vauto.
  destruct constructive_indefinite_description; desf.
Qed.

Lemma in_trace_Eninit' i e 
      (Ei: trace_labels i = EventLab e)
      (NOT_DEF: trace_labels i <> def_lbl):
  Eninit e.
Proof.
  destruct (classic (NOmega.lt_nat_l i (trace_length tr))).
  2: { exfalso. apply NOT_DEF. apply ge_default. auto. }
  eapply in_trace_Eninit; eauto.
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

Definition nth_such n S i := count_upto S i = n /\ S (trace_labels i).

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

Lemma count_upto_more_strict i j (F: SyLabel -> Prop) (LE: i < j) (Fi: F (trace_labels i)):
  count_upto F i < count_upto F j. 
Proof.
  red in LE.
  forward eapply (count_upto_more (S i) j F); auto.
  intro CNT.
  rewrite count_upto_next in CNT.
  rewrite check1 in CNT; auto.
  lia.
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

Lemma upstream_size_inv_read st1 st2 lbl chan (STEP: TSOFPGA_step st1 lbl st2):
length (filter is_read_ups (up_bufs st1 chan)) +
check (fpga_read_ups' ∩₁ in_chan chan) lbl =
check (fpga_mem_read' ∩₁ in_chan chan) lbl +
length (filter is_read_ups (up_bufs st2 chan)).
Proof.
destruct st1 as [wp1 rp1 up_buf1 db1 shm1 cpu_b1]. destruct st2 as [wp2 rp2 up_buf2 db2 shm2 cpu_b2]. simpl.
destruct (classic (lbl_chan_opt lbl = Some chan)) as [EQ | NEQ] .
2: { forward eapply upstream_same_transition as SAME_BUF; eauto. simpl in SAME_BUF.
      rewrite SAME_BUF. 
      repeat rewrite check0; [lia| |].
      all: apply set_compl_inter; right; vauto. }
inversion STEP; subst; simpl in EQ; inv EQ.
 all: try (repeat rewrite check0; [lia| |]; apply set_compl_inter; left; vauto).
{ rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite upds. rewrite filter_app. rewrite length_app. by simpl. }
{ rewrite upds. rewrite UPSTREAM. simpl.
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite check0; [| unfolder'; simpl; intuition].
  lia. }
{ rewrite check1.
  2: { unfolder'. simpl. intuition. }
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite upds. rewrite filter_app. rewrite length_app. simpl.
  lia.
}
{
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite check1.
  2: { unfolder'. simpl. intuition. }
  rewrite UPSTREAM.
  rewrite upds. 
  simpl.
  lia.
}
Qed.

Lemma upstream_size_inv_any st1 st2 lbl chan (STEP: TSOFPGA_step st1 lbl st2):
length (up_bufs st1 chan) +
check (fpga_up_prop ∩₁ in_chan chan) lbl =
check (fpga_any_mem_prop ∩₁ in_chan chan) lbl +
length (up_bufs st2 chan).
Proof.
destruct st1 as [wp1 rp1 up_buf1 db1 shm1 cpu_b1]. destruct st2 as [wp2 rp2 up_buf2 db2 shm2 cpu_b2]. simpl.
destruct (classic (lbl_chan_opt lbl = Some chan)) as [EQ | NEQ] .
2: { forward eapply upstream_same_transition as SAME_BUF; eauto. simpl in SAME_BUF.
      rewrite SAME_BUF. 
      repeat rewrite check0; [lia| |].
      all: apply set_compl_inter; right; vauto. }
inversion STEP; subst; simpl in EQ; inv EQ.
 all: try by (repeat rewrite check0; [lia| |]; apply set_compl_inter; left; apply set_compl_union; vauto).
{ rewrite check1.
  2: { unfolder'. simpl. intuition. }
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite upds. rewrite length_app. by simpl. }
{ rewrite upds. rewrite UPSTREAM. simpl.
  rewrite check0; [| unfolder'; simpl; intuition].
  rewrite check1; [| unfolder'; simpl; intuition].
  lia. }
{ rewrite check1.
  2: { unfolder'. simpl. intuition. }
  rewrite check0.
  2: { unfolder'. simpl. intuition. }
  rewrite upds. rewrite length_app. by simpl. }
rewrite upds. rewrite UPSTREAM. simpl.
rewrite check0; [| unfolder'; simpl; intuition].
rewrite check1; [| unfolder'; simpl; intuition].
lia.
Qed.


Lemma downstream_size_inv st1 st2 lbl chan (STEP: TSOFPGA_step st1 lbl st2):
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

Lemma buffer_size_upstream_any chan i (DOM: NOmega.le (NOnum i) (trace_length tr)):
  count_upto (fpga_up_prop ∩₁ in_chan chan) i = 
  count_upto (fpga_any_mem_prop ∩₁ in_chan chan) i + length (up_bufs (states i) chan).
Proof.
  induction i.
  { simpl. unfold count_upto. rewrite seq0. simpl.
    pose proof TS0 as TS0. simpl in TS0. by rewrite <- TS0. }
  remember (states (S i)) as s. simpl.
  unfold count_upto. rewrite !seqS, !Nat.add_0_l, !map_app, !filterP_app, !length_app. simpl.
  fold (count_upto (fpga_up_prop ∩₁ in_chan chan) i).
  fold (count_upto (fpga_any_mem_prop ∩₁ in_chan chan) i).
  specialize_full IHi.
  { apply NOmega.le_trans with (m := NOnum (S i)); vauto. } 
  fold (check (fpga_up_prop ∩₁ in_chan chan) (trace_nth i tr def_lbl)). 
  fold (check (fpga_any_mem_prop ∩₁ in_chan chan) (trace_nth i tr def_lbl)). 
  remember (states i) as st_prev.
  rewrite IHi.
  rewrite <- !Nat.add_assoc.
  f_equal. 

  simpl in IHi. 
  apply upstream_size_inv_any.
  forward eapply (TSi i) with (d := def_lbl) as TSi; vauto.
Qed.

Lemma buffer_size_upstream_read chan i (DOM: NOmega.le (NOnum i) (trace_length tr)):
  count_upto (fpga_read_ups' ∩₁ in_chan chan) i = 
  count_upto (fpga_mem_read' ∩₁ in_chan chan) i + length (filter is_read_ups (up_bufs (states i) chan)).
Proof.
  induction i.
  { simpl. unfold count_upto. rewrite seq0. simpl.
    pose proof TS0 as TS0. simpl in TS0. by rewrite <- TS0. }
  remember (states (S i)) as s. simpl.
  unfold count_upto. rewrite !seqS, !Nat.add_0_l, !map_app, !filterP_app, !length_app. simpl.
  fold (count_upto (fpga_read_ups' ∩₁ in_chan chan) i).
  fold (count_upto (fpga_mem_read' ∩₁ in_chan chan) i).
  specialize_full IHi.
  { apply NOmega.le_trans with (m := NOnum (S i)); vauto. } 
  fold (check (fpga_read_ups' ∩₁ in_chan chan) (trace_nth i tr def_lbl)). 
  fold (check (fpga_mem_read' ∩₁ in_chan chan) (trace_nth i tr def_lbl)). 
  remember (states i) as st_prev.
  rewrite IHi.
  rewrite <- !Nat.add_assoc.
  f_equal. 

  simpl in IHi. 
  apply upstream_size_inv_read.
  forward eapply (TSi i) with (d := def_lbl) as TSi; vauto.
Qed.


Lemma filterP_union_length [A : Type] [p1 p2: A -> Prop] l (DIFFERENT: p1 ∩₁ p2 ≡₁ ∅):
  length (filterP (p1 ∪₁ p2) l) = length (filterP p1 l) + length (filterP p2 l).
Proof.
  induction l; simpl; auto.
  destruct (excluded_middle_informative (p1 a)).
  { assert ((p1 ∪₁ p2) a) by vauto.
    destruct (excluded_middle_informative (p2 a)).
    { exfalso. assert ((p1 ∩₁ p2) a) by vauto. eapply (proj1 DIFFERENT); vauto. }
    simpl. destruct excluded_middle_informative; vauto. simpl. lia. }
  destruct (excluded_middle_informative (p2 a)).
  2: { assert (~((p1 ∪₁ p2) a)) by (intro H; destruct H; vauto). 
      destruct (excluded_middle_informative); vauto. }
  assert ((p1 ∪₁ p2) a) by vauto.
  destruct excluded_middle_informative; vauto.
  simpl; lia.
Qed.

Lemma read_ups_or_store_ups entry: 
  (is_read_ups entry /\ ~is_store_ups entry) 
  \/ (is_store_ups entry /\ ~is_read_ups entry).
Proof.
  destruct entry.
  destruct u; vauto; desf.
Qed.

Lemma buffer_size_upstream chan i (DOM: NOmega.le (NOnum i) (trace_length tr)):
  count_upto (fpga_up_prop ∩₁ in_chan chan) i = 
  count_upto (fpga_any_mem_prop ∩₁ in_chan chan) i + length (up_bufs (states i) chan).
Proof.
  unfold fpga_up_prop, fpga_any_mem_prop.
  remember (set_inter_union_l fpga_read_ups' fpga_write' (in_chan chan)) as s.
  remember (set_extensionality s) as e.
  rewrite e.
  clear Heqs; clear Heqe; clear s; clear e.

  remember (set_inter_union_l fpga_mem_read' is_fpga_prop (in_chan chan)) as s.
  remember (set_extensionality s) as e.
  rewrite e.
  clear Heqs; clear Heqe; clear s; clear e.
  unfold count_upto.
  erewrite filterP_union_length.
  2: { split; (try basic_solver); intro; ins; exfalso; destruct H as [[H1 H2] [H3 H4]]; unfolder'; desf. }
  erewrite filterP_union_length.
  2: { split; (try basic_solver); intro; ins; exfalso; destruct H as [[H1 H2] [H3 H4]]; unfolder'; desf. }
  forward eapply (buffer_size_upstream_write chan i); vauto.
  forward eapply (buffer_size_upstream_read chan i); vauto.
  unfold count_upto in *.
  cut (length (filter is_read_ups (up_bufs (states i) chan)) + 
       length (filter is_store_ups (up_bufs (states i) chan)) = 
       length (up_bufs (states i) chan)).
  { ins. lia. }
  induction (up_bufs (states i) chan); simpl; auto.
  destruct (read_ups_or_store_ups a).
  { destruct H. desf. simpl; lia. }
  { destruct H. desf. simpl; lia. }
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
  forward eapply downstream_size_inv; eauto.
  forward eapply (TSi i) with (d := def_lbl) as TSi; vauto.
Qed.


Lemma EXACT_CHAN_ANY_PROPS chan:
  trace_length (trace_filter (fpga_up_prop ∩₁ in_chan chan) tr) =
  trace_length (trace_filter (fpga_any_mem_prop ∩₁ in_chan chan) tr).
Proof.
  (* forward eapply (EXACT_CHAN_PROPS chan) as EXACT_CHAN_PROPS.
  forward eapply (EXACT_CHAN_MEMREADS chan) as EXACT_CHAN_MEMREADS.
  unfold fpga_up_prop, fpga_any_mem_prop.
  replace ((fpga_read_ups' ∪₁ fpga_write') ∩₁ in_chan chan) with
      ((fpga_read_ups' ∩₁ in_chan chan) ∪₁ (fpga_write' ∩₁ in_chan chan)).
  2: { apply set_extensionality. rewrite set_inter_union_l. auto. }
  replace ((fpga_mem_read' ∪₁ is_fpga_prop) ∩₁ in_chan chan) with
      ((fpga_mem_read' ∩₁ in_chan chan) ∪₁ (is_fpga_prop ∩₁ in_chan chan)).
  2: { apply set_extensionality. rewrite set_inter_union_l. auto. }
  unfold trace_length in *.
  destruct tr.
  { unfold trace_filter in *.
    erewrite filterP_union_length.
    2: { red; splits; vauto. red; ins; destruct H; unfolder'; desf. }
    erewrite filterP_union_length.
    2: { red; splits; vauto. red; ins; destruct H; unfolder'; desf. }
    f_equal.
    desf.
    lia. }
  destruct (trace_filter (fpga_mem_read' ∩₁ in_chan chan) (trace_inf fl)). *)
  Admitted.


Definition same_chan x y :=
  let chan := lbl_chan_opt x in
  chan = lbl_chan_opt y /\ chan <> None. 

Definition same_thread x y := lbl_thread x = lbl_thread y.

Lemma write2prop_fpga_lem w
    (W: fpga_write' (trace_labels w)):  
exists p,
  ⟪THREAD_PROP: (is_fpga_prop ∩₁ same_chan (trace_labels w)) (trace_labels p)⟫ /\
  ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫ /\
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

Lemma any_ups2prop_fpga_lem w
    (U: fpga_up_prop (trace_labels w)):
exists p,
  ⟪THREAD_PROP: (fpga_any_mem_prop ∩₁ same_chan (trace_labels w)) (trace_labels p)⟫ /\
  ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫ /\
  ⟪W_P_CORR: count_upto (fpga_up_prop ∩₁ same_chan (trace_labels w)) w =
             count_upto (fpga_any_mem_prop ∩₁ same_chan (trace_labels w)) p⟫.
Proof.
simpl.
assert (DOM: NOmega.lt_nat_l w (trace_length tr)).
{ destruct (classic (NOmega.lt_nat_l w (trace_length tr))); auto.
  exfalso. apply ge_default in H. rewrite H in U.
  unfolder'. intuition. }
assert (fpga_write' (trace_labels w) \/ fpga_read_ups' (trace_labels w)) as UPS_TYPE.
{ unfold fpga_up_prop in *; unfolder'; desf; intuition. }
destruct UPS_TYPE as [W | R].
{ pose proof (fpga_write_structure _ W). 
  desc.
  assert (same_chan (trace_labels w) ≡₁ in_chan chan).
  { rewrite H. simpl. unfold same_chan. simpl.
    unfold in_chan.
    red. split; red; ins; desc; vauto. }
  apply set_extensionality in H0. rewrite H0 in *. 
  pose proof sim_subtraces_conv as TMP. specialize_full TMP.
  { eapply (EXACT_CHAN_ANY_PROPS chan). }
  { red. splits; eauto.
    rewrite H. vauto. }
  { auto. }
  desc. exists j. splits; vauto.
}
pose proof (fpga_rflush_structure _ R). 
desc.
assert (same_chan (trace_labels w) ≡₁ in_chan chan).
{ rewrite H. simpl. unfold same_chan. simpl.
  unfold in_chan.
  red. split; red; ins; desc; vauto. }
apply set_extensionality in H0. rewrite H0 in *. 
pose proof sim_subtraces_conv as TMP. specialize_full TMP.
{ eapply (EXACT_CHAN_ANY_PROPS chan). }
{ red. splits; eauto.
  rewrite H. vauto. }
{ auto. }
desc. exists j. splits; vauto.
Qed.

Lemma read_buffer_prop_lem r
    (R: fpga_read_req' (trace_labels r)):
exists p,
  ⟪LATER: r < p⟫ /\
  ⟪UPS_PROP: (fpga_read_ups' ∩₁ same_chan (trace_labels r)) (trace_labels p)⟫ /\
  ⟪SAME_META: meta_l (trace_labels r) = meta_l (trace_labels p)⟫ /\
  ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫.
Proof.
  assert (DOM: NOmega.lt_nat_l r (trace_length tr)).
  { destruct (classic (NOmega.lt_nat_l r (trace_length tr))); auto.
    exfalso. apply ge_default in H. rewrite H in R.
    unfolder'. intuition. }
  remember RP_FAIR as FAIR_.
  red in FAIR_.
  pose proof (fpga_read_req_structure _ R). desc.
  clear HeqFAIR_.
  specialize FAIR_ with (i:=S r) (chan:=chan) (loc:=loc) (meta:=meta).
  specialize_full FAIR_.
  { red; destruct (trace_length tr); vauto; lia. }
  { red. 
    remember (TSi r DOM def_lbl) as STEP.
    inversion STEP.
    all: try (fold (trace_labels r) in H2; rewrite H in H2; by unfolder'; desf).
    fold (trace_labels r) in H2; rewrite H in H2; desf.
    set (next_st := mkState w_pool (r_pool ++ nil) (upd up_bufs chan (up_bufs chan ++ cons(read_up loc, meta) nil)) down_bufs sh_mem cpu_bufs).
    exists next_st.
    unfold next_st.
    apply fpga_flush_read; vauto.
   }
  desf.
  fold (trace_labels j) in FAIR_1.
  exists j. splits; vauto; try lia.
  rewrite FAIR_1.
  { split; unfolder'; desf; intuition. }
  unfold meta_l; desf.
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
set (enabled_cpu st := exists st', TSOFPGA_step st (CpuFlush thread) st').
assert (forall i (GE: i >= (extra_write_pos + 1))
          (LE: NOmega.le (NOnum i) (trace_length tr)),
            enabled_cpu (states i)) as ENABLED_AFTER_WRITES.
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



Lemma write2prop_cpu_lem w
      (W: cpu_write' (trace_labels w)):
  exists p,
    ⟪THREAD_PROP: (is_cpu_prop ∩₁ same_thread (trace_labels w)) (trace_labels p)⟫ /\
    ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫ /\
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

Definition any_ups2prop (w: nat) :=
  match (excluded_middle_informative (fpga_up_prop (trace_labels w))) with
  | left W => (proj1_sig ((constructive_indefinite_description _ (any_ups2prop_fpga_lem w W))))
  | right _ => 0
  end.
                   
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
  destruct (constructive_indefinite_description _ _) as [p [PROP [INT CORR]]]. simpl.
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
  destruct (constructive_indefinite_description _ _) as [p [PROP [INT CORR]]]. simpl.
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

Lemma memread_to_read_resp_lemma r
    (MR: fpga_mem_read' (trace_labels r)):
exists p,
  ⟪THREAD_PROP: (fpga_read_resp' ∩₁ same_chan (trace_labels r)) (trace_labels p)⟫ /\
  ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫ /\
  ⟪RS_MR_CORR: count_upto (fpga_mem_read' ∩₁ same_chan (trace_labels r)) r =
              count_upto (fpga_read_resp' ∩₁ same_chan (trace_labels r)) p⟫.
Proof.
simpl.
assert (DOM: NOmega.lt_nat_l r (trace_length tr)).
{ destruct (classic (NOmega.lt_nat_l r (trace_length tr))); auto.
  exfalso. apply ge_default in H. rewrite H in MR.
  unfolder'. intuition. }
pose proof (fpga_memread_structure _ MR).
desc.
assert (same_chan (trace_labels r) ≡₁ in_chan chan).
{ rewrite H. simpl. unfold same_chan. simpl.
  unfold in_chan.
  red. split; red; ins; desc; vauto. }
apply set_extensionality in H0. rewrite H0 in *. 
pose proof sim_subtraces_conv as TMP. specialize_full TMP.
{ symmetry. eapply (EXACT_CHAN_READS chan). }
{ red. splits; eauto.
  rewrite H. vauto. }
{ auto. }
desc. exists j. splits; vauto.
Qed.

Lemma read_resp_to_memread_lemma r
    (R: fpga_read_resp' (trace_labels r)):
exists p,
  ⟪THREAD_PROP: (fpga_mem_read' ∩₁ same_chan (trace_labels r)) (trace_labels p)⟫ /\
  ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫ /\
  ⟪RS_MR_CORR: count_upto (fpga_read_resp' ∩₁ same_chan (trace_labels r)) r =
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

Lemma read_ups_to_memread_lemma r
    (R: fpga_read_ups' (trace_labels r)):
exists p,
  ⟪R_PROP: (fpga_mem_read' ∩₁ same_chan (trace_labels r)) (trace_labels p)⟫ /\
  ⟪P_DOM: NOmega.lt_nat_l p (trace_length tr)⟫ /\
  ⟪RS_MR_CORR: count_upto (fpga_read_ups' ∩₁ same_chan (trace_labels r)) r =
              count_upto (fpga_mem_read' ∩₁ same_chan (trace_labels r)) p⟫.
Proof.
simpl.
assert (DOM: NOmega.lt_nat_l r (trace_length tr)).
{ destruct (classic (NOmega.lt_nat_l r (trace_length tr))); auto.
  exfalso. apply ge_default in H. rewrite H in R.
  unfolder'. intuition. }
pose proof (fpga_rflush_structure _ R). 
desc.
assert (same_chan (trace_labels r) ≡₁ in_chan chan).
{ rewrite H. simpl. unfold same_chan. simpl.
  unfold in_chan.
  red. split; red; ins; desc; vauto. }
apply set_extensionality in H0. rewrite H0 in *. 
pose proof sim_subtraces_conv as TMP. specialize_full TMP.
{ eapply (EXACT_CHAN_MEMREADS chan). }
{ red. splits; eauto.
  rewrite H. vauto. }
{ auto. }
desc. exists j. splits; vauto.
Qed.

Definition read_ups2mem_read (r: nat) :=
  match (excluded_middle_informative (fpga_read_ups' (trace_labels r))) with
  | left R => (proj1_sig ((constructive_indefinite_description _ (read_ups_to_memread_lemma r R))))
  | right _ => 0
  end.

Definition read2mem_read (r: nat) :=
  match (excluded_middle_informative (fpga_read_resp' (trace_labels r))) with
  | left R => (proj1_sig ((constructive_indefinite_description _ (read_resp_to_memread_lemma r R))))
  | right _ => match (excluded_middle_informative (cpu_read' (trace_labels r))) with
    | left _ => r
    | right _ => 0
    end
  end.

Definition mem_read2read (r: nat) :=
  match (excluded_middle_informative (fpga_mem_read' (trace_labels r))) with
  | left R => (proj1_sig ((constructive_indefinite_description _ (memread_to_read_resp_lemma r R))))
  | right _ => 0
  end.

Ltac ex_des :=
  destruct excluded_middle_informative; try by (exfalso; unfolder'; desf).

Lemma mr2r_later_fpga mr (MR: fpga_mem_read' (trace_labels mr)):
  mr < mem_read2read mr.
Proof.
  remember (trace_labels mr) as tlab.
  unfold mem_read2read.
  ex_des.
  destruct (constructive_indefinite_description); desf.
  pose proof (Nat.lt_trichotomy mr x). des; auto.
  { subst. red in THREAD_PROP. exfalso. 
    apply fpga_memread_structure in f. destruct f as [chan [loc [val [meta H0]]]].
    rewrite H0 in THREAD_PROP. desc. vauto. }
  exfalso. rename H into LT. 
  apply fpga_memread_structure in f. destruct f as [chan [loc [val [meta TLAB]]]].
  forward eapply (buffer_size_downstream chan (x + 1)) as BUF_SIZE.
  { contra GE. forward eapply (proj2 (ge_default x)) as P_DEF. 
    { red. intros. apply GE. simpl. red in H. destruct tr; vauto.
      simpl in *. lia. }
    red in THREAD_PROP. rewrite P_DEF in THREAD_PROP.
    generalize THREAD_PROP. unfolder'. intuition. }
  assert (same_chan (trace_labels mr) = in_chan chan) as RESTR_EQUIV. 
  { apply set_extensionality. rewrite TLAB. simpl.
    unfold same_chan, in_cpu_thread. simpl. red. splits; red; ins; desc; vauto. }
  rewrite RESTR_EQUIV in RS_MR_CORR.
  replace (count_upto (fpga_read_resp' ∩₁ in_chan chan) (x + 1)) with ((count_upto (fpga_read_resp' ∩₁ in_chan chan) x) + 1) in BUF_SIZE.
  2: { unfold count_upto.
       rewrite Nat.add_1_r with (n := x), seqS, Nat.add_0_l.
       rewrite map_app, filterP_app, length_app. simpl.
       rewrite RESTR_EQUIV in THREAD_PROP.
       destruct (excluded_middle_informative ((fpga_read_resp' ∩₁ in_chan chan) (trace_nth x tr def_lbl))); vauto. }
  rewrite <- RS_MR_CORR in BUF_SIZE.
  cut (count_upto (fpga_mem_read' ∩₁ in_chan chan) (x + 1) <= count_upto (fpga_mem_read' ∩₁ in_chan chan) mr).
  { ins. lia. }
  apply count_upto_more. lia. 
Qed. 

Lemma r_up2mem_later_fpga mr (MR: fpga_read_ups' (trace_labels mr)):
  mr < read_ups2mem_read mr.
Proof.
  remember (trace_labels mr) as tlab.
  unfold read_ups2mem_read.
  ex_des.
  destruct (constructive_indefinite_description); desf.
  pose proof (Nat.lt_trichotomy mr x). des; auto.
  { subst. red in R_PROP. exfalso. 
    apply fpga_rflush_structure in f. destruct f as [chan [loc [meta H0]]].
    rewrite H0 in R_PROP. desc. vauto. }
  exfalso. rename H into LT. 
  apply fpga_rflush_structure in f. destruct f as [chan [loc [meta TLAB]]].
  forward eapply (buffer_size_upstream_read chan (x + 1)) as BUF_SIZE.
  { contra GE. forward eapply (proj2 (ge_default x)) as P_DEF. 
    { red. intros. apply GE. simpl. red in H. destruct tr; vauto.
      simpl in *. lia. }
    red in R_PROP. rewrite P_DEF in R_PROP.
    generalize R_PROP. unfolder'. intuition. }
  assert (same_chan (trace_labels mr) = in_chan chan) as RESTR_EQUIV. 
  { apply set_extensionality. rewrite TLAB. simpl.
    unfold same_chan, in_cpu_thread. simpl. red. splits; red; ins; desc; vauto. }
  rewrite RESTR_EQUIV in RS_MR_CORR.
  replace (count_upto (fpga_mem_read' ∩₁ in_chan chan) (x + 1)) with ((count_upto (fpga_mem_read' ∩₁ in_chan chan) x) + 1) in BUF_SIZE.
  2: { unfold count_upto.
       rewrite Nat.add_1_r with (n := x), seqS, Nat.add_0_l.
       rewrite map_app, filterP_app, length_app. simpl.
       rewrite RESTR_EQUIV in R_PROP.
       destruct (excluded_middle_informative ((fpga_mem_read' ∩₁ in_chan chan) (trace_nth x tr def_lbl))); vauto. }
  rewrite <- RS_MR_CORR in BUF_SIZE.
  cut (count_upto (fpga_read_ups' ∩₁ in_chan chan) (x + 1) <= count_upto (fpga_read_ups' ∩₁ in_chan chan) mr).
  { ins. lia. }
  apply count_upto_more. lia. 
Qed. 


Lemma read2mem2read r
    (R: fpga_read_resp' (trace_labels r)):
  (mem_read2read (read2mem_read r)) = r.
Proof.
  unfold read2mem_read.
  ex_des.
  destruct constructive_indefinite_description; ins; desf.
  unfold mem_read2read.
  ex_des.
  destruct constructive_indefinite_description; ins; desf.
  destruct THREAD_PROP as [MR RX_CHAN].
  destruct THREAD_PROP0 as [RSP XX0_CHAN'].
  assert (same_chan (trace_labels x) = same_chan (trace_labels r)) as CH'.
  { apply set_extensionality. unfold same_chan in *. destruct RX_CHAN. rewrite H. split; red; ins. }
  assert (same_chan (trace_labels x0) = same_chan (trace_labels r)) as CH''.
  { apply set_extensionality. rewrite <- CH'. unfold same_chan in *. destruct XX0_CHAN', CH'. rewrite <- H. split; red; ins; vauto. }
  rewrite CH' in *.
  rewrite RS_MR_CORR0 in RS_MR_CORR.
  forward eapply (nth_such_self (fpga_read_resp' ∩₁ same_chan (trace_labels r)) r). { unfolder'. splits; eauto. destruct RX_CHAN. vauto. }
  forward eapply (nth_such_self (fpga_read_resp' ∩₁ same_chan (trace_labels r)) x0). { rewrite <- CH''. unfolder'. destruct XX0_CHAN'. destruct (trace_labels x0); desf. }
  ins.
  apply (nth_such_unique (count_upto (fpga_read_resp' ∩₁ same_chan (trace_labels r)) r) (fpga_read_resp' ∩₁ same_chan (trace_labels r)) x0 r); vauto.
Qed.

Lemma mem2read2mem r
    (R: fpga_mem_read' (trace_labels r)):
  (read2mem_read (mem_read2read r)) = r.
Proof.
  unfold mem_read2read.
  ex_des.
  destruct constructive_indefinite_description; ins; desf.
  unfold read2mem_read.
  ex_des.
  destruct constructive_indefinite_description; ins; desf.
  destruct THREAD_PROP as [MR RX_CHAN].
  destruct THREAD_PROP0 as [RSP XX0_CHAN'].
  assert (same_chan (trace_labels x) = same_chan (trace_labels r)) as CH'.
  { apply set_extensionality. unfold same_chan in *. destruct RX_CHAN. rewrite H. split; red; ins. }
  assert (same_chan (trace_labels x0) = same_chan (trace_labels r)) as CH''.
  { apply set_extensionality. rewrite <- CH'. unfold same_chan in *. destruct XX0_CHAN', CH'. rewrite <- H. split; red; ins; vauto. }
  rewrite CH' in *.
  rewrite RS_MR_CORR0 in RS_MR_CORR.
  forward eapply (nth_such_self (fpga_mem_read' ∩₁ same_chan (trace_labels r)) r). { unfolder'. splits; eauto. destruct RX_CHAN. vauto. }
  forward eapply (nth_such_self (fpga_mem_read' ∩₁ same_chan (trace_labels r)) x0). { rewrite <- CH''. unfolder'. destruct XX0_CHAN'. destruct (trace_labels x0); desf. }
  ins.
  apply (nth_such_unique (count_upto (fpga_mem_read' ∩₁ same_chan (trace_labels r)) r) (fpga_mem_read' ∩₁ same_chan (trace_labels r)) x0 r); vauto.
Qed.

Definition exact_tid e := match e with
                          | InitEvent _ => 0
                          | ThreadEvent thread _ _ => thread
                          | FpgaEvent _ _ _ => 1
                          end.


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
  assert ((read_up l, m) :: up_buf' = ((read_up l, m) :: nil) ++ up_buf') by vauto.
  rewrite H.
  erewrite filter_app.
  rewrite length_app.
  assert (is_read_ups (read_up l, m)) by vauto.
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
  erewrite trace_index_simpl' in RS_MR_CORR; eauto.

  erewrite (count_same_chan_in_chan c) in RS_MR_CORR.
  2: { unfold in_chan; ins. }
  erewrite (count_same_chan_in_chan c) in RS_MR_CORR.
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
  rewrite RS_MR_CORR in BUF_SIZE.
 
  cut (count_upto (fpga_mem_read' ∩₁ in_chan c) (rsp + 1) <= count_upto (fpga_mem_read' ∩₁ in_chan c) x).
  { ins. lia. }
  apply count_upto_more. lia. 
Qed.

Lemma r_vis_cpu e (Rr: is_cpu_rd e): vis' e = trace_index e.
Proof.
  unfold vis'.
  generalize Rr. unfolder'. destruct e; vauto.
  destruct e; ins.
  all: destruct (excluded_middle_informative _ ); intuition.
Qed. 

Lemma r_vis e (R: is_r e) (EN: Eninit e): vis' e <= trace_index e.
Proof.
  unfold vis'.
  generalize R. unfolder'. destruct e; vauto.
  destruct e; ins.
  destruct excluded_middle_informative; vauto.
  destruct e; desf.
  ins.
  forward eapply (rd_resp_after_memread (FpgaEvent (Fpga_read_resp c x v) index m)); eauto.
  ins.
  lia.
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

Lemma TI_GE_VIS e (ENINIT: Eninit e) (NOT_W: ~is_w e): trace_index e >= vis' e.
Proof.
  unfold vis'. simpl.
  ex_des.
  ex_des.
  destruct excluded_middle_informative; [|lia].
  forward eapply (rd_resp_after_memread e); vauto.
  lia.
Qed.


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

Lemma fpgar_vis e (R: is_rd_resp e): vis' e = read2mem_read (trace_index e). 
Proof.
  unfold vis'.
  ex_des.
  ex_des.
  ex_des.
  vauto.
Qed.

Lemma RESTR_EQUIV thread index lbl:
  same_thread (EventLab (ThreadEvent thread index lbl)) = in_cpu_thread thread.
Proof.
  ins. apply set_extensionality. 
  unfold same_thread, in_cpu_thread. simpl. red. splits; red; ins; desc; vauto.
Qed. 
    
Definition G :=
  {| acts := EG;
     co := ⦗EG ∩₁ is_w⦘ ⨾ restr_eq_rel SyEvents.loc vis_lt' ⨾ ⦗EG ∩₁ is_w⦘;     
     rf := ⦗EG ∩₁ is_w⦘ ⨾ rf' ⨾ ⦗EG ∩₁ is_r⦘;
     readpair := ⦗EG ∩₁ is_rd_req⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_rd_resp⦘;
     writepair := ⦗EG ∩₁ is_wr_req⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_wr_resp⦘;
     fenceonepair := ⦗EG ∩₁ is_fence_req_one⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_fence_resp_one⦘;
     fenceallpair := ⦗EG ∩₁ is_fence_req_all⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_fence_resp_all⦘
  |}.



Lemma vis_lt_init_helper x y (SB: sb G x y): vis_lt' x y \/ (Eninit x /\ Eninit y).
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
  
Lemma cpu_vis_respects_sb_notr: restr_rel (fun e => is_cpu e /\ ~is_r e) (sb G) ⊆ vis_lt'.
Proof.
unfold restr_rel. red. ins. destruct H as [SBxy [Wx Wy]].
destruct (vis_lt_init_helper x y SBxy) as [|[E'x E'y]]; auto. 
red. red. right. apply seq_eqv_lr. splits; auto.
red in SBxy. apply seq_eqv_lr in SBxy. destruct SBxy as [_ [SBxy _]].
forward eapply (proj1 tb_respects_sb x y) as H; [basic_solver| ].
apply seq_eqv_lr in H. destruct H as [_ [[TBxy TIDxy] _]]. 
red in TBxy.
unfold vis'. 
destruct (excluded_middle_informative _) as [X | X].
{
  destruct (excluded_middle_informative _) as [Y | Y].
  {
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
      destruct (excluded_middle_informative).
      { unfolder'. unfold is_cpu in *. desf. }
      destruct excluded_middle_informative.
      { unfolder'. unfold is_cpu in *. desf. }
  destruct (NPeano.Nat.lt_ge_cases (write2prop (trace_index x)) (trace_index y)) as [| LE]; auto.
  exfalso.
  forward eapply (@reg_write_structure (EventLab x)) as H. 
  { vauto. }
  desc. inversion H. clear H.  
  destruct y; desf.
  destruct e; desf.
  assert (thread0 = thread); [|subst thread0]. 
  { red in TIDxy. vauto. }
  remember (ThreadEvent thread index0 Cpu_fence) as tlab. 
  assert (NOmega.lt_nat_l (trace_index tlab) (trace_length tr)) as DOM. 
  { contra GE. apply ge_default in GE.
    unfold trace_labels in GE. rewrite trace_index_simpl in GE; auto. 
    rewrite Heqtlab in GE. discriminate GE. }
  set (st := states (trace_index tlab)).
  forward eapply (TSi (trace_index tlab)) with (d := def_lbl) as TSi; eauto. 
  rewrite trace_index_simpl in TSi; auto.
  rewrite Heqtlab in TSi at 2. inversion TSi. subst. 
  remember (ThreadEvent thread index0 Cpu_fence) as e_fence. 
  remember (ThreadEvent thread index (Cpu_store loc val)) as e_w.
  forward eapply (@buffer_size_cpu thread (trace_index e_fence)) as BUF_SIZE. 
  { destruct (trace_length tr); auto. simpl in *. lia. }
  simpl in BUF_SIZE. rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE.
  rewrite NO_WB in BUF_SIZE. simpl in BUF_SIZE. rewrite Nat.add_0_r in BUF_SIZE.
  remember (write2prop (trace_index e_w)) as vis_w. 
  assert (count_upto (cpu_write' ∩₁ same_thread (trace_labels (trace_index e_w))) (trace_index e_w) =
          count_upto (is_cpu_prop ∩₁ same_thread (trace_labels (trace_index e_w))) vis_w) as VIS_W.
  { subst vis_w. unfold write2prop in *. destruct (excluded_middle_informative _).
    2: { generalize n, X. rewrite trace_index_simpl' in *; auto. by unfolder'. }
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    lia. }
  replace (same_thread (trace_labels (trace_index e_w))) with (in_cpu_thread thread) in VIS_W.
  2: { rewrite trace_index_simpl'; auto. subst e_w. by rewrite RESTR_EQUIV. }
  assert (count_upto (cpu_write' ∩₁ in_cpu_thread thread) (trace_index e_w) < count_upto (cpu_write' ∩₁ in_cpu_thread thread) (trace_index e_fence)) as MORE_WRITES.
  { unfold lt. rewrite <- Nat.add_1_r.
    rewrite <- (@check1 _ (cpu_write' ∩₁ in_cpu_thread thread) (trace_labels ((trace_index e_w)))).
    2: { red. rewrite trace_index_simpl'; auto. by subst e_w. }
    rewrite <- count_upto_next. apply count_upto_more. lia. }
  assert (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) (trace_index e_fence) <= count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) vis_w) as MORE_PROPS.
  { apply count_upto_more. lia. }
  lia. }
  ex_des.
  ex_des.
  destruct (excluded_middle_informative _).
  { forward eapply (w2p_later (trace_index y)); [rewrite trace_index_simpl'; unfold write'; unfolder'; desf; intuition|].
    lia. }
  destruct (excluded_middle_informative).
  { destruct Wy. unfold is_cpu, is_wr_resp in *; desf. }
  destruct (excluded_middle_informative).
  { destruct Wy. unfold is_cpu, is_rd_resp in *; desf. }
  auto.
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

Ltac same_chan_prover := ins; apply set_extensionality; unfold same_chan, in_chan, lbl_chan_opt, fpga_chan_opt in *; simpl; red; splits; red; ins; desc; vauto.

Lemma fpga_all_fence_sb_respects_vis: (sb G ⨾ ⦗is_fence_resp_all⦘) ⊆ vis_lt'.
Proof.
  red; ins.
  destruct H as [x0 [SBxy FN]].
  destruct FN as [EQ FN].
  subst x0.
  destruct (vis_lt_init_helper x y SBxy) as [|[E'x E'y]]; auto. 
  red. red. right. apply seq_eqv_lr. splits; auto.
  red in SBxy. apply seq_eqv_lr in SBxy. destruct SBxy as [_ [SBxy _]].
  forward eapply (proj1 tb_respects_sb x y) as H; [basic_solver| ].
  apply seq_eqv_lr in H. destruct H as [_ [[TBxy TIDxy] _]]. 
  red in TBxy.
  assert (is_fpga y) as FPY. { unfolder'; desf. }
  assert (is_fpga x) as FPX. { unfold same_tid in *. unfolder'; desf. }
  cut (is_wr_resp x \/ ~is_wr_resp x).
  2: { unfolder'; unfold is_fpga in *; desf; intuition. }
  intro K; destruct K as [WRX | NWRX].
  2: {
    forward eapply (TI_LE_VIS y); vauto.
    { unfolder'; desf. }
    forward eapply (TI_GE_VIS x); vauto.
    { unfolder'; desf. }
    lia.
  }
  unfold vis'.
  do 5 ex_des.
  destruct (NPeano.Nat.lt_ge_cases (write2prop (trace_index x)) (trace_index y)) as [| LE]; auto.
  exfalso.
  forward eapply (@fpga_write_structure (EventLab x)) as H. 
  { vauto. }
  desc. inversion H. clear H.  
  destruct y; desf.
  destruct e; desf.
    remember (FpgaEvent (Fpga_fence_resp_all) index0 m) as tlab.
    rename chan into c.
    assert (NOmega.lt_nat_l (trace_index tlab) (trace_length tr)) as DOM. 
    { contra GE. apply ge_default in GE.
      unfold trace_labels in GE. rewrite trace_index_simpl in GE; auto. 
      rewrite Heqtlab in GE. discriminate GE. }
    set (st := states (trace_index tlab)).
    forward eapply (TSi (trace_index tlab)) with (d := def_lbl) as TSi; eauto. 
    rewrite trace_index_simpl in TSi; auto.
    rewrite Heqtlab in TSi at 2. inversion TSi. subst. 
    remember (FpgaEvent (Fpga_fence_resp_all) index0 m) as e_fence. 
    remember (FpgaEvent (Fpga_write_resp c loc val) index meta) as e_w.
    forward eapply (@buffer_size_upstream_write c (trace_index e_fence)) as BUF_SIZE. 
    { destruct (trace_length tr); auto. simpl in *. lia. }
    simpl in BUF_SIZE. rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE.
    rewrite NO_UPSTREAMS in BUF_SIZE. simpl in BUF_SIZE. rewrite Nat.add_0_r in BUF_SIZE.
    remember (write2prop (trace_index e_w)) as vis_w.  
    assert (count_upto (fpga_write' ∩₁ same_chan (trace_labels (trace_index e_w))) (trace_index e_w) =
            count_upto (is_fpga_prop ∩₁ same_chan (trace_labels (trace_index e_w))) vis_w) as VIS_W.
    { subst vis_w. unfold write2prop in *. destruct (excluded_middle_informative _).
      { exfalso. clear LE. rewrite trace_index_simpl' in c0; auto.  }
      destruct (excluded_middle_informative) as [FWX | NW].
      2: { exfalso. clear LE. rewrite trace_index_simpl' in NW; auto.  }
      destruct (constructive_indefinite_description _ _). desc. simpl in *.
      lia. }
    replace (same_chan (trace_labels (trace_index e_w))) with (in_chan c) in VIS_W.
    2: { rewrite trace_index_simpl'; auto. subst e_w. same_chan_prover. }
    assert (count_upto (fpga_write' ∩₁ in_chan c) (trace_index e_w) < count_upto (fpga_write' ∩₁ in_chan c) (trace_index e_fence)) as MORE_WRITES.
    { unfold lt. rewrite <- Nat.add_1_r.
      rewrite <- (@check1 _ (fpga_write' ∩₁ in_chan c) (trace_labels ((trace_index e_w)))).
      2: { red. rewrite trace_index_simpl'; auto. by subst e_w. }
      rewrite <- count_upto_next. apply count_upto_more. lia. }
    assert (count_upto (is_fpga_prop ∩₁ in_chan c) (trace_index e_fence) <= count_upto (is_fpga_prop ∩₁ in_chan c) vis_w) as MORE_PROPS.
    { apply count_upto_more. lia. }
    lia.
Qed.

Lemma fpga_resp_vis_respects_sb_notr: (⦗is_fpga⦘ ⨾ poch G ⨾ ⦗minus_event (is_resp) is_rd_resp⦘ ) ⊆ vis_lt'.
Proof.
  red. ins. destruct H as [x0 [[EQ Rx] [y0 [POCHxy [EQ' NR_RESP]]]]].
  subst x0; subst y0.
  destruct POCHxy as [SBxy CHxy].
  destruct (vis_lt_init_helper x y); vauto.
  destruct H as [ENX ENY].
  cut (is_fence_resp_all y \/ ~is_fence_resp_all y).
  2: { unfolder'; desf; intuition. }
  intro FN; destruct FN as [FNY | NFNY].
  { forward eapply (fpga_all_fence_sb_respects_vis x y); vauto. }
  destruct (vis_lt_init_helper x y SBxy) as [|[E'x E'y]]; auto. 
  red. red. right. apply seq_eqv_lr. splits; auto.
  red in SBxy. apply seq_eqv_lr in SBxy. destruct SBxy as [_ [SBxy _]].
  forward eapply (proj1 tb_respects_sb x y) as H; [basic_solver| ].
  apply seq_eqv_lr in H. destruct H as [_ [[TBxy TIDxy] _]]. 
  red in CHxy.
  red in TBxy.
  cut (is_wr_resp x \/ ~is_wr_resp x).
  2: { unfolder'; unfold is_fpga in *; desf; intuition. }
  intro K; destruct K as [WRX | NWRX].
  2: {
    forward eapply (TI_LE_VIS y); vauto.
    { red in NR_RESP; desf. }
    forward eapply (TI_GE_VIS x); vauto.
    { unfolder'. unfold is_w; desf. }
    lia.
  }
  unfold vis'.
  do 3 ex_des.
  destruct excluded_middle_informative.
  { unfold write2prop. destruct (excluded_middle_informative _).
    { exfalso; rewrite trace_index_simpl' in c; vauto. }
    destruct (excluded_middle_informative _).
    2: { rewrite trace_index_simpl' in *; vauto. }
    destruct (excluded_middle_informative _).
    { exfalso; rewrite trace_index_simpl' in c; vauto. }
    destruct (excluded_middle_informative (fpga_write' (trace_labels (trace_index y)))).
    2: { rewrite trace_index_simpl' in *; vauto. }
      destruct (constructive_indefinite_description _ _) as [px Px].
      destruct (constructive_indefinite_description _ _) as [py Py].
      simpl in *. desc.
      unfold trace_labels in *. rewrite !trace_index_simpl in *; auto.
      assert (exists ch, same_chan (EventLab x) = in_chan ch /\ same_chan (EventLab y) = in_chan ch).
      { pose proof (fpga_write_structure _ f). desc. inv H. 
        pose proof (fpga_write_structure _ f0). desc. inv H0.
        red in TIDxy. simpl in TIDxy. inv TIDxy.
        exists chan0. 
        split; same_chan_prover. }
      desc. rewrite H, H0 in *. 
      assert (count_upto (fpga_write' ∩₁ in_chan ch) (trace_index x) < count_upto (fpga_write' ∩₁ in_chan ch) (trace_index y)).
      { subst. apply Nat.lt_le_trans with (m := count_upto (fpga_write' ∩₁ in_chan ch) (trace_index x + 1)).
        2: { eapply count_upto_more. lia. }
        rewrite Nat.add_1_r, count_upto_next.
        rewrite check1; [lia|].
        unfold trace_labels. rewrite trace_index_simpl; auto. red. split; auto.
        rewrite <- H. unfold same_chan. 
        destruct x; unfolder'; intuition; vauto; unfolder'; desf.
      } 
      apply lt_diff in H1. desc. rewrite W_P_CORR0, W_P_CORR in H1. 
      destruct (NPeano.Nat.lt_ge_cases px py); auto. 
      remember (count_upto_more py px (is_fpga_prop ∩₁ in_chan ch) H2); lia. }
      destruct NR_RESP.
  ex_des.
  destruct (NPeano.Nat.lt_ge_cases (write2prop (trace_index x)) (trace_index y)) as [| LE]; auto.
  exfalso.
  rename H into H'.
  forward eapply (@fpga_write_structure (EventLab x)) as H. 
  { vauto. }
  desc. inversion H. clear H.  
  destruct y; desf.
  destruct e; desf.
  {
    remember (FpgaEvent (Fpga_fence_resp_one c) index0 m) as tlab.
    assert (NOmega.lt_nat_l (trace_index tlab) (trace_length tr)) as DOM. 
    { contra GE. apply ge_default in GE.
      unfold trace_labels in GE. rewrite trace_index_simpl in GE; auto. 
      rewrite Heqtlab in GE. discriminate GE. }
    set (st := states (trace_index tlab)).
    forward eapply (TSi (trace_index tlab)) with (d := def_lbl) as TSi; eauto. 
    rewrite trace_index_simpl in TSi; auto.
    rewrite Heqtlab in TSi at 2. inversion TSi. subst. 
    remember (FpgaEvent (Fpga_fence_resp_one c) index0 m) as e_fence. 
    remember (FpgaEvent (Fpga_write_resp c loc val) index meta) as e_w.
    forward eapply (@buffer_size_upstream_write c (trace_index e_fence)) as BUF_SIZE. 
    { destruct (trace_length tr); auto. simpl in *. lia. }
    simpl in BUF_SIZE. rewrite <- H1 in BUF_SIZE. simpl in BUF_SIZE.
    rewrite NO_UPSTREAM in BUF_SIZE. simpl in BUF_SIZE. rewrite Nat.add_0_r in BUF_SIZE.
    remember (write2prop (trace_index e_w)) as vis_w.  
    assert (count_upto (fpga_write' ∩₁ same_chan (trace_labels (trace_index e_w))) (trace_index e_w) =
            count_upto (is_fpga_prop ∩₁ same_chan (trace_labels (trace_index e_w))) vis_w) as VIS_W.
    { subst vis_w. unfold write2prop in *. destruct (excluded_middle_informative _).
      { exfalso. clear LE. rewrite trace_index_simpl' in c0; auto.  }
      destruct (excluded_middle_informative) as [FWX | NW].
      2: { exfalso. clear LE. rewrite trace_index_simpl' in NW; auto.  }
      destruct (constructive_indefinite_description _ _). desc. simpl in *.
      lia. }
    replace (same_chan (trace_labels (trace_index e_w))) with (in_chan c) in VIS_W.
    2: { rewrite trace_index_simpl'; auto. subst e_w. same_chan_prover. }
    assert (count_upto (fpga_write' ∩₁ in_chan c) (trace_index e_w) < count_upto (fpga_write' ∩₁ in_chan c) (trace_index e_fence)) as MORE_WRITES.
    { unfold lt. rewrite <- Nat.add_1_r.
      rewrite <- (@check1 _ (fpga_write' ∩₁ in_chan c) (trace_labels ((trace_index e_w)))).
      2: { red. rewrite trace_index_simpl'; auto. by subst e_w. }
      rewrite <- count_upto_next. apply count_upto_more. lia. }
    assert (count_upto (is_fpga_prop ∩₁ in_chan c) (trace_index e_fence) <= count_upto (is_fpga_prop ∩₁ in_chan c) vis_w) as MORE_PROPS.
    { apply count_upto_more. lia. }
    lia. }
Qed.

Lemma cpu_w_not_r: (is_cpu ∩₁ is_w) ⊆₁ (fun e => is_cpu e /\ ~is_r e).
Proof.
  red. ins.
  destruct H.
  unfold is_cpu, is_w, is_r; desf; intuition.
Qed.

Lemma cpu_vis_respects_sb_w: restr_rel (is_cpu ∩₁ is_w) (sb G) ⊆ vis_lt'.
Proof.
  remember cpu_w_not_r as H.
  assert (sb G ⊆ sb G) as H1 by basic_solver.
  forward eapply (restr_rel_mori H H1).
  ins.
  rewrite (H0).
  apply cpu_vis_respects_sb_notr.
Qed.
  

Lemma rfe_diff_tid w r (RFE: rfe G w r): tid w <> tid r. 
Proof.
  intro.
  unfold rfe in RFE.
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


Lemma fsupp_vis_loc: fsupp (restr_eq_rel loc (vis_lt' ∩ (fun x => ~is_rd_resp x) × (fun _ => True))).
Proof.
  red. ins. 
  set (extract_event := fun i => proj_ev (trace_labels i)). 
  exists (InitEvent (loc y) :: map extract_event (List.seq 0 (vis' y))).
  ins. desc.
  red in REL. desc. 
  destruct REL as [REL [CPUX CPUY]].
  do 2 red in REL. des.
  { left. red in REL. desc. 
    rewrite <- REL0. unfold loc, loc_l. desf. }
  right. 
  apply seq_eqv_lr in REL. desc. 
  replace x with (extract_event (trace_index x)).
  2: { unfold extract_event. unfold trace_labels. by rewrite trace_index_simpl. }
  apply in_map. apply in_seq0_iff.
  Search vis' ge.
  forward eapply (TI_LE_VIS x); eauto.
  ins; lia.
Qed.

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
      (TID: chan_opt w = Some ch) (E'w: Eninit w):
  (is_prop ∩₁ in_chan ch) (trace_nth (write2prop (trace_index w)) tr def_lbl).
Proof.
  unfold write2prop. destruct (excluded_middle_informative _).
  { exfalso; rewrite trace_index_simpl' in c; unfolder'; desf; vauto. }
  destruct (excluded_middle_informative _).
  2: { rewrite trace_index_simpl' in *; vauto. }
  destruct (constructive_indefinite_description _ _). desc. simpl in *.
  rewrite trace_index_simpl' in *; auto.
  apply fpga_write_structure in f. desc. inversion f. subst. 
  destruct THREAD_PROP as [CPU_PROP SAME_TID].
  split; vauto.
  simpl.
  fold (trace_labels x).
  unfold same_chan, in_chan, lbl_chan_opt in *. desf.
Qed. 

Lemma mr2r_fpgar r ch (REG: fpga_mem_read' (trace_labels r))
      (CH: lbl_chan_opt (trace_labels r) = Some ch):
  (fpga_read_resp' ∩₁ in_chan ch) (trace_nth (mem_read2read r) tr def_lbl).
Proof.
  unfold mem_read2read. destruct (excluded_middle_informative _).
  2: { vauto. }
  destruct (constructive_indefinite_description _ _). desc. simpl in *.
  fold (trace_labels x) in *.
  apply fpga_memread_structure in f. desc. inversion f. subst. 
  destruct THREAD_PROP as [CPU_PROP SAME_TID].
  split; vauto.
  simpl.
  unfold same_chan, in_chan, lbl_chan_opt in *. desf.
Qed. 

Lemma r2mr_fpga r ch (REG: fpga_read_resp' (trace_labels r))
      (CH: lbl_chan_opt (trace_labels r) = Some ch):
  (fpga_mem_read' ∩₁ in_chan ch) (trace_nth (read2mem_read r) tr def_lbl).
Proof.
  unfold read2mem_read. destruct (excluded_middle_informative _).
  2: { vauto. }
  destruct (constructive_indefinite_description _ _). desc. simpl in *.
  fold (trace_labels x) in *.
  apply fpga_read_structure in f. desc. inversion f. subst. 
  destruct THREAD_PROP as [CPU_PROP SAME_TID].
  split; vauto.
  simpl.
  unfold same_chan, in_chan, lbl_chan_opt in *. desf.
Qed. 

Lemma ups2mr_fpgar r ch (REG: fpga_read_ups' (trace_labels r))
      (CH: lbl_chan_opt (trace_labels r) = Some ch):
  (fpga_mem_read' ∩₁ in_chan ch) (trace_nth (read_ups2mem_read r) tr def_lbl).
Proof.
  unfold read_ups2mem_read. destruct (excluded_middle_informative _).
  2: { vauto. }
  destruct (constructive_indefinite_description _ _). desc. simpl in *.
  fold (trace_labels x) in *.
  apply fpga_rflush_structure in f. desc. inversion f. subst. 
  destruct R_PROP as [CPU_PROP SAME_TID].
  split; vauto.
  simpl.
  unfold same_chan, in_chan, lbl_chan_opt in *. desf.
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


Lemma buffer_sources_cpu i thread (DOM: NOmega.lt_nat_l i (trace_length tr)):
  let buf := cpu_bufs (states i) thread in
  let ip := count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) i in
  forall k l v (AT_K: Some (l, v) = nth_error buf k),
  exists ind,
    let lab_w := ThreadEvent thread ind (Cpu_store l v) in
    let w := trace_index lab_w in 
    ⟪ WRITE_POS: nth_such (ip + k) (cpu_write' ∩₁ in_cpu_thread thread) w ⟫ /\
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
    subst channel. 
    rewrite upds in AT_K.
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

Lemma buffer_sources_upstream_rd i chan (DOM: NOmega.lt_nat_l i (trace_length tr)):
  let buf := filter is_read_ups (up_bufs (states i) chan) in
  let ip := count_upto (fpga_mem_read' ∩₁ in_chan chan) i in
  forall k l meta (AT_K: Some (read_up l, meta) = nth_error buf k),
  exists mr, 
    let lab_mr := FpgaReadToUpstream chan l meta in
    ⟪ MREAD: trace_labels mr = lab_mr ⟫ /\
    ⟪ WRITE_POS: nth_such (ip + k) (fpga_read_ups' ∩₁ in_chan chan) mr ⟫ /\
    ⟪ WRITE_BEFORE: mr < i ⟫ /\
    ⟪ PROP_AFTER: i <= read_ups2mem_read mr ⟫.
Proof.
  induction i.
  { ins. rewrite <- TS0 in AT_K. simpl in AT_K. by destruct k. }
  simpl in *. ins.
  assert (NOmega.lt_nat_l i (trace_length tr)) as DOM'.
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  specialize (IHi DOM').

  assert (forall meta, Some (read_up l, meta) = nth_error (filter is_read_ups (up_bufs (states i) chan)) k ->
          ~ (fpga_mem_read' ∩₁ in_chan chan) (trace_nth i tr def_lbl) ->
          exists mr : nat,
            trace_labels mr = (FpgaReadToUpstream chan l meta) /\
            nth_such (count_upto (fpga_mem_read' ∩₁ in_chan chan) (S i) + k)
                     (fpga_read_ups' ∩₁ in_chan chan)
                     mr /\
            mr < S i /\
            S i <= read_ups2mem_read mr) as SAME.
  { ins. specialize (IHi k l meta0). specialize_full IHi; [congruence| ].
    desc. exists mr. splits; vauto.
    { cut (count_upto (fpga_mem_read' ∩₁ in_chan chan) (S i) = count_upto (fpga_mem_read' ∩₁ in_chan chan) i); [congruence| ].
      rewrite count_upto_next, check0; [lia| ]. auto. }
    apply le_lt_or_eq in PROP_AFTER. des; [lia| ].
    forward eapply (@ups2mr_fpgar mr chan) as UPS2MR_PROP; try (by vauto). 
    { rewrite MREAD; vauto. }
    rewrite MREAD; vauto. }
    
  forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
  inversion TSi.
  all: try (apply SAME; [destruct H0, H2; simpl in *; congruence | ]; rewrite <- H; unfolder'; intuition; vauto ).
  3: { rewrite <- H2 in AT_K. simpl in AT_K.
    destruct (classic (channel = chan)).
    2: { 
         apply SAME. rewrite <- H0. simpl. rewrite AT_K. rewrite updo; vauto; lia.
         rewrite <- H. unfolder'. unfold in_chan in *. intuition.  }
    subst channel. 
    rewrite upds in AT_K.
    assert (k <= length (filter is_read_ups (up_bufs chan))) as R_POS.
    { forward eapply (proj1 (nth_error_Some (filter is_read_ups (up_bufs chan ++ (read_up loc, meta0) :: nil)) k)).
      { apply opt_val. exists (read_up l, meta). vauto.  }
      rewrite filter_app. rewrite length_app. simpl. lia. }
    apply le_lt_or_eq in R_POS. des.
    { apply SAME.
      { rewrite filter_app in AT_K. rewrite nth_error_app1 in AT_K; auto. by rewrite <- H0. }
      rewrite <- H. unfolder'. intuition. }
    exists i.
    assert (l = loc /\ meta = meta0).  
    { rewrite R_POS in AT_K. rewrite filter_app in AT_K. rewrite nth_error_app2 in AT_K; [| lia].
      rewrite Nat.sub_diag in AT_K. simpl in AT_K. by inversion AT_K. }
    desc. subst loc meta.
    splits.
    { fold (trace_labels i) in H. rewrite <- H. auto. }
    { forward eapply (buffer_size_upstream_read chan (i)) as BUF_SIZE.
      { destruct (trace_length tr); vauto. simpl in *. lia. }
      simpl in BUF_SIZE. rewrite R_POS.
      rewrite count_upto_next, check0.
      2: { unfold trace_labels. rewrite <- H. unfolder'. intro. desf. }
      rewrite Nat.add_0_r.
      rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE. rewrite <- BUF_SIZE.
      apply nth_such_self. fold (trace_labels i) in H. rewrite <- H. vauto. }
    { lia. }
    { forward eapply (r_up2mem_later_fpga i) as LATER; vauto.
      fold (trace_labels i) in H. unfolder'; desf. } }
  3: { destruct (classic (chan = channel)).
    2: { apply SAME.
         { rewrite <- H0. rewrite <- H2 in AT_K. simpl in AT_K. rewrite updo in AT_K; auto. }
         rewrite <- H. unfolder'. unfold in_chan. unfold lbl_chan_opt. intuition. vauto. }
    subst chan. rewrite <- H2 in AT_K. simpl in AT_K. rewrite upds in AT_K.
    specialize (IHi (S k) l meta). specialize_full IHi. 
    { rewrite <- H0. simpl. rewrite UPSTREAM. simpl. vauto. }
    desc. exists mr.
    splits; vauto.
    { replace (count_upto (fpga_mem_read' ∩₁ in_chan channel) (S i)) with (count_upto (fpga_mem_read' ∩₁ in_chan channel) i + 1).
      { by rewrite <- NPeano.Nat.add_assoc, Nat.add_1_l. }
      rewrite count_upto_next, check1; auto.
      unfold trace_labels. by rewrite <- H. }
    apply le_lt_or_eq in PROP_AFTER. des; [done| ].

    exfalso.
    assert (fpga_read_ups' (trace_labels mr)) by (unfolder'; desf).
    unfold read_ups2mem_read in PROP_AFTER. 
    destruct (excluded_middle_informative _).
    2: vauto.
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    assert (same_chan (trace_labels mr) = in_chan channel) as CH_REWR.
    { rewrite MREAD. ins. apply set_extensionality. 
      unfold same_chan, in_chan. simpl. red. splits; red; ins; desc; vauto. }
    rewrite CH_REWR in *. subst x.
    red in WRITE_POS. desc. lia. }
    { apply SAME.
      2: { rewrite <- H. intro. destruct H1; desf. }
      cut (filter is_read_ups (TSOFPGA.up_bufs (states (S i)) chan) = filter is_read_ups (TSOFPGA.up_bufs (states i) chan)).
      { ins. rewrite <- H1. vauto. }
      rewrite <- H0, <- H2; simpl.
      destruct (classic (channel = chan)).
      { subst chan. rewrite upds. rewrite filter_app; simpl. apply app_nil_r. }
      rewrite updo; vauto; lia. }
    { apply SAME.
      2: { rewrite <- H. intro. destruct H1; desf. }
      cut (filter is_read_ups (TSOFPGA.up_bufs (states (S i)) chan) = filter is_read_ups (TSOFPGA.up_bufs (states i) chan)).
      { ins. rewrite <- H1. vauto. }
      rewrite <- H0, <- H2; simpl.
      destruct (classic (channel = chan)).
      { subst chan. rewrite UPSTREAM. rewrite upds. simpl. auto. }
      rewrite updo; vauto; lia. }
Qed.

Lemma buffer_sources_upstream_read_generalized i chan (DOM: NOmega.lt_nat_l i (trace_length tr)):
  let buf := up_bufs (states i) chan in
  let ip := count_upto (fpga_any_mem_prop ∩₁ in_chan chan) i in
  forall k l meta (AT_K: Some (read_up l, meta) = nth_error buf k),
  exists mr, 
    let lab_mr := FpgaReadToUpstream chan l meta in
    ⟪ MREAD: trace_labels mr = lab_mr ⟫ /\
    ⟪ WRITE_POS: nth_such (ip + k) (fpga_up_prop ∩₁ in_chan chan) mr ⟫ /\
    ⟪ WRITE_BEFORE: mr < i ⟫.
Proof.
  induction i.
  { ins. rewrite <- TS0 in AT_K. simpl in AT_K. by destruct k. }
  simpl in *. ins.
  assert (NOmega.lt_nat_l i (trace_length tr)) as DOM'.
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  specialize (IHi DOM').

  assert (forall meta, Some (read_up l, meta) = nth_error (up_bufs (states i) chan) k ->
          ~ (fpga_any_mem_prop ∩₁ in_chan chan) (trace_nth i tr def_lbl) ->
          exists mr : nat,
            trace_labels mr = (FpgaReadToUpstream chan l meta) /\
            nth_such (count_upto (fpga_any_mem_prop ∩₁ in_chan chan) (S i) + k)
                     (fpga_up_prop ∩₁ in_chan chan)
                     mr /\
            mr < S i)
            as SAME.
  { ins. specialize (IHi k l meta0). specialize_full IHi; [congruence| ].
    desc. exists mr. splits; vauto.
    cut (count_upto (fpga_any_mem_prop ∩₁ in_chan chan) (S i) = count_upto (fpga_any_mem_prop ∩₁ in_chan chan) i); [congruence| ].
      rewrite count_upto_next, check0; [lia| ]. auto. }
    
  forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
  inversion TSi.
  all: try (apply SAME; [destruct H0, H2; simpl in *; congruence | ]; rewrite <- H; unfolder'; intuition; vauto ).
  3: { rewrite <- H2 in AT_K. simpl in AT_K.
    destruct (classic (channel = chan)).
    2: { 
         apply SAME. rewrite <- H0. simpl. rewrite AT_K. rewrite updo; vauto; lia.
         rewrite <- H. unfolder'. unfold in_chan in *. intuition.  }
    subst channel. 
    rewrite upds in AT_K.
    assert (k <= length (up_bufs chan)) as R_POS.
    { forward eapply (proj1 (nth_error_Some (up_bufs chan ++ (read_up loc, meta0) :: nil) k)).
      { apply opt_val. exists (read_up l, meta). vauto.  }
      rewrite length_app. simpl. lia. }
    apply le_lt_or_eq in R_POS. des.
    { apply SAME.
      { rewrite nth_error_app1 in AT_K; auto. by rewrite <- H0. }
      rewrite <- H. unfolder'. intuition. }
    exists i.
    assert (l = loc /\ meta = meta0).  
    { rewrite R_POS in AT_K. rewrite nth_error_app2 in AT_K; [| lia].
      rewrite Nat.sub_diag in AT_K. simpl in AT_K. by inversion AT_K. }
    desc. subst loc meta.
    splits.
    { fold (trace_labels i) in H. rewrite <- H. auto. }
    { forward eapply (buffer_size_upstream chan (i)) as BUF_SIZE.
      { destruct (trace_length tr); vauto. simpl in *. lia. }
      simpl in BUF_SIZE. rewrite R_POS.
      rewrite count_upto_next, check0.
      2: { unfold trace_labels. rewrite <- H. unfolder'. intro. desf. }
      rewrite Nat.add_0_r.
      rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE. rewrite <- BUF_SIZE.
      apply nth_such_self. fold (trace_labels i) in H. rewrite <- H. vauto. }
    { lia. } }
  3: { destruct (classic (chan = channel)).
    2: { apply SAME.
         { rewrite <- H0. rewrite <- H2 in AT_K. simpl in AT_K. rewrite updo in AT_K; auto. }
         rewrite <- H. unfolder'. unfold in_chan. unfold lbl_chan_opt. intuition. vauto. }
    subst chan. rewrite <- H2 in AT_K. simpl in AT_K. rewrite upds in AT_K.
    specialize (IHi (S k) l meta). specialize_full IHi. 
    { rewrite <- H0. simpl. rewrite UPSTREAM. simpl. vauto. }
    desc. exists mr.
    splits; vauto.
    { replace (count_upto (fpga_any_mem_prop ∩₁ in_chan channel) (S i)) with (count_upto (fpga_any_mem_prop ∩₁ in_chan channel) i + 1).
      { by rewrite <- NPeano.Nat.add_assoc, Nat.add_1_l. }
      rewrite count_upto_next, check1; auto.
      unfold trace_labels. rewrite <- H. vauto. } }
  2: { destruct (classic (chan = channel)).
    2: { apply SAME.
         { rewrite <- H0. rewrite <- H2 in AT_K. simpl in AT_K. rewrite updo in AT_K; auto. }
         rewrite <- H. unfolder'. unfold in_chan. unfold lbl_chan_opt. intuition. vauto. }
    subst chan. rewrite <- H2 in AT_K. simpl in AT_K. rewrite upds in AT_K.
    specialize (IHi (S k) l meta). specialize_full IHi. 
    { rewrite <- H0. simpl. rewrite UPSTREAM. simpl. vauto. }
    desc. exists mr.
    splits; vauto.
    { replace (count_upto (fpga_any_mem_prop ∩₁ in_chan channel) (S i)) with (count_upto (fpga_any_mem_prop ∩₁ in_chan channel) i + 1).
      { by rewrite <- NPeano.Nat.add_assoc, Nat.add_1_l. }
      rewrite count_upto_next, check1; auto.
      unfold trace_labels. rewrite <- H. vauto. } }


    rewrite <- H2 in AT_K. simpl in AT_K.
    destruct (classic (channel = chan)).
    2: { 
         apply SAME. rewrite <- H0. simpl. rewrite AT_K. rewrite updo; vauto; lia.
         rewrite <- H. unfolder'. unfold in_chan in *. intuition.  }
    subst channel. 
    rewrite upds in AT_K.
    assert (k <= length (up_bufs chan)) as R_POS.
    { forward eapply (proj1 (nth_error_Some (up_bufs chan ++ (store_up loc val, meta0) :: nil) k)).
      { apply opt_val. exists (read_up l, meta). vauto.  }
      rewrite length_app. simpl. lia. }
    apply le_lt_or_eq in R_POS. des.
    { apply SAME.
      { rewrite nth_error_app1 in AT_K; auto. by rewrite <- H0. }
      rewrite <- H. unfolder'. intuition. }
    exfalso.
    rewrite R_POS in AT_K. rewrite nth_error_app2 in AT_K; [| lia].
    rewrite Nat.sub_diag in AT_K. simpl in AT_K. by inversion AT_K.
Qed.

Lemma buffer_sources_upstream_write_generalized i chan (DOM: NOmega.lt_nat_l i (trace_length tr)):
  let buf := up_bufs (states i) chan in
  let ip := count_upto (fpga_any_mem_prop ∩₁ in_chan chan) i in
  forall k l v meta (AT_K: Some (store_up l v, meta) = nth_error buf k),
  exists w ind, 
    let lab_w := EventLab (FpgaEvent (Fpga_write_resp chan l v) ind meta) in
    ⟪ MWRITE: trace_labels w = lab_w ⟫ /\
    ⟪ WRITE_POS: nth_such (ip + k) (fpga_up_prop ∩₁ in_chan chan) w ⟫ /\
    ⟪ WRITE_BEFORE: w < i ⟫.
Proof.
  induction i.
  { ins. rewrite <- TS0 in AT_K. simpl in AT_K. by destruct k. }
  simpl in *. ins.
  assert (NOmega.lt_nat_l i (trace_length tr)) as DOM'.
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  specialize (IHi DOM').

  assert (forall meta, Some (store_up l v, meta) = nth_error (up_bufs (states i) chan) k ->
          ~ (fpga_any_mem_prop ∩₁ in_chan chan) (trace_nth i tr def_lbl) ->
          exists w ind : nat,
            trace_labels w = EventLab (FpgaEvent (Fpga_write_resp chan l v) ind meta) /\
            nth_such (count_upto (fpga_any_mem_prop ∩₁ in_chan chan) (S i) + k)
                     (fpga_up_prop ∩₁ in_chan chan)
                     w /\
            w < S i)
            as SAME.

  { ins. specialize (IHi k l v meta0). specialize_full IHi; [congruence| ].
    desc. exists w, ind. splits; vauto.
    cut (count_upto (fpga_any_mem_prop ∩₁ in_chan chan) (S i) = count_upto (fpga_any_mem_prop ∩₁ in_chan chan) i); [congruence| ].
      rewrite count_upto_next, check0; [lia| ]. auto. }
    
  forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
  inversion TSi.
  all: try (apply SAME; [destruct H0, H2; simpl in *; congruence | ]; rewrite <- H; unfolder'; intuition; vauto ).
  { rewrite <- H2 in AT_K. simpl in AT_K.
    destruct (classic (channel = chan)).
    2: { 
         apply SAME. rewrite <- H0. simpl. rewrite AT_K. rewrite updo; vauto; lia.
         rewrite <- H. unfolder'. unfold in_chan in *. intuition.  }
    subst channel. 
    rewrite upds in AT_K.
    assert (k <= length (up_bufs chan)) as R_POS.
    { forward eapply (proj1 (nth_error_Some (up_bufs chan ++ (store_up loc val, meta0) :: nil) k)).
      { apply opt_val. exists (store_up l v, meta). vauto.  }
      rewrite length_app. simpl. lia. }
    apply le_lt_or_eq in R_POS. des.
    { apply SAME.
      { rewrite nth_error_app1 in AT_K; auto. by rewrite <- H0. }
      rewrite <- H. unfolder'. intuition. }
    exists i, index.
    assert (l = loc /\ meta = meta0 /\ v = val).  
    { rewrite R_POS in AT_K. rewrite nth_error_app2 in AT_K; [| lia].
      rewrite Nat.sub_diag in AT_K. simpl in AT_K. by inversion AT_K. }
    desc. subst loc meta val.
    splits.
    { fold (trace_labels i) in H. rewrite <- H. auto. }
    { forward eapply (buffer_size_upstream chan (i)) as BUF_SIZE.
      { destruct (trace_length tr); vauto. simpl in *. lia. }
      simpl in BUF_SIZE. rewrite R_POS.
      rewrite count_upto_next, check0.
      2: { unfold trace_labels. rewrite <- H. unfolder'. intro. desf. }
      rewrite Nat.add_0_r.
      rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE. rewrite <- BUF_SIZE.
      apply nth_such_self. fold (trace_labels i) in H. rewrite <- H. vauto. }
    { lia. } }
  { destruct (classic (chan = channel)).
    2: { apply SAME.
         { rewrite <- H0. rewrite <- H2 in AT_K. simpl in AT_K. rewrite updo in AT_K; auto. }
         rewrite <- H. unfolder'. unfold in_chan. unfold lbl_chan_opt. intuition. vauto. }
    subst chan. rewrite <- H2 in AT_K. simpl in AT_K. rewrite upds in AT_K.
    specialize (IHi (S k) l v meta). specialize_full IHi. 
    { rewrite <- H0. simpl. rewrite UPSTREAM. simpl. vauto. }
    desc. exists w, ind.
    splits; vauto.
    { replace (count_upto (fpga_any_mem_prop ∩₁ in_chan channel) (S i)) with (count_upto (fpga_any_mem_prop ∩₁ in_chan channel) i + 1).
      { by rewrite <- NPeano.Nat.add_assoc, Nat.add_1_l. }
      rewrite count_upto_next, check1; auto.
      unfold trace_labels. rewrite <- H. vauto. } }
  2: { destruct (classic (chan = channel)).
    2: { apply SAME.
         { rewrite <- H0. rewrite <- H2 in AT_K. simpl in AT_K. rewrite updo in AT_K; auto. }
         rewrite <- H. unfolder'. unfold in_chan. unfold lbl_chan_opt. intuition. vauto. }
    subst chan. rewrite <- H2 in AT_K. simpl in AT_K. rewrite upds in AT_K.
    specialize (IHi (S k) l v meta). specialize_full IHi. 
    { rewrite <- H0. simpl. rewrite UPSTREAM. simpl. vauto. }
    desc. exists w, ind.
    splits; vauto.
    { replace (count_upto (fpga_any_mem_prop ∩₁ in_chan channel) (S i)) with (count_upto (fpga_any_mem_prop ∩₁ in_chan channel) i + 1).
      { by rewrite <- NPeano.Nat.add_assoc, Nat.add_1_l. }
      rewrite count_upto_next, check1; auto.
      unfold trace_labels. rewrite <- H. vauto. } }

    rewrite <- H2 in AT_K. simpl in AT_K.
    destruct (classic (channel = chan)).
    2: { 
         apply SAME. rewrite <- H0. simpl. rewrite AT_K. rewrite updo; vauto; lia.
         rewrite <- H. unfolder'. unfold in_chan in *. intuition.  }
    subst channel. 
    rewrite upds in AT_K.
    assert (k <= length (up_bufs chan)) as R_POS.
    { forward eapply (proj1 (nth_error_Some (up_bufs chan ++ (read_up loc, meta0) :: nil) k)).
      { apply opt_val. exists (store_up l v, meta). vauto.  }
      rewrite length_app. simpl. lia. }
    apply le_lt_or_eq in R_POS. des.
    { apply SAME.
      { rewrite nth_error_app1 in AT_K; auto. by rewrite <- H0. }
      rewrite <- H. unfolder'. intuition. }
    exfalso.
    rewrite R_POS in AT_K. rewrite nth_error_app2 in AT_K; [| lia].
    rewrite Nat.sub_diag in AT_K. simpl in AT_K. by inversion AT_K.
Qed.

Lemma buffer_sources_downstream i chan (DOM: NOmega.lt_nat_l i (trace_length tr)):
  let buf := down_bufs (states i) chan in
  let ip := count_upto (fpga_read_resp' ∩₁ in_chan chan) i in
  forall k l v meta (AT_K: Some (l, v, meta) = nth_error buf k),
  exists mr, 
    let lab_mr := FpgaMemRead chan l v meta in
    ⟪ MREAD: trace_labels mr = lab_mr ⟫ /\
    ⟪ WRITE_POS: nth_such (ip + k) (fpga_mem_read' ∩₁ in_chan chan) mr ⟫ /\
    ⟪ WRITE_BEFORE: mr < i ⟫ /\
    ⟪ PROP_AFTER: i <= mem_read2read mr ⟫
    .
Proof.
  induction i.
  { ins. rewrite <- TS0 in AT_K. simpl in AT_K. by destruct k. }
  simpl in *. ins.
  assert (NOmega.lt_nat_l i (trace_length tr)) as DOM'.
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  specialize (IHi DOM').

  assert (forall meta, Some (l, v, meta) = nth_error (down_bufs (states i) chan) k ->
          ~ (fpga_read_resp' ∩₁ in_chan chan) (trace_nth i tr def_lbl) ->
          exists mr : nat,
            trace_labels mr = (FpgaMemRead chan l v meta) /\
            nth_such (count_upto (fpga_read_resp' ∩₁ in_chan chan) (S i) + k)
                     (fpga_mem_read' ∩₁ in_chan chan)
                     mr /\
            mr < S i /\
            S i <= mem_read2read mr) as SAME.
  { ins. specialize (IHi k l v meta0). specialize_full IHi; [congruence| ].
    desc. exists mr. splits; vauto.
    { cut (count_upto (fpga_read_resp' ∩₁ in_chan chan) (S i) = count_upto (fpga_read_resp' ∩₁ in_chan chan) i); [congruence| ].
      rewrite count_upto_next, check0; [lia| ]. auto. }
    apply le_lt_or_eq in PROP_AFTER. des; [lia| ].
    forward eapply (@mr2r_fpgar mr chan) as MR2R_PROP; try (by vauto). 
    { rewrite MREAD; vauto. }
    rewrite MREAD; vauto. }
    
  forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
  inversion TSi.
  all: try (apply SAME; [destruct H0, H2; simpl in *; congruence | ]; rewrite <- H; unfolder'; intuition; vauto ).
  { rewrite <- H2 in AT_K. simpl in AT_K.
    destruct (classic (channel = chan)).
    2: { 
         apply SAME. rewrite <- H0. simpl. rewrite AT_K. rewrite updo; vauto; lia.
         rewrite <- H. unfolder'. unfold in_chan in *. intuition.  }
    subst channel. 
    rewrite upds in AT_K.
    assert (k <= length (down_bufs chan)) as R_POS.
    { forward eapply (proj1 (nth_error_Some (down_bufs chan ++ (loc, val, meta0) :: nil) k)).
      { apply opt_val. exists (l, v, meta). auto.  }
      rewrite length_app. simpl. lia. }
    apply le_lt_or_eq in R_POS. des.
    { apply SAME.
      { rewrite nth_error_app1 in AT_K; auto. by rewrite <- H0. }
      rewrite <- H. unfolder'. intuition. }
    exists i.
    assert (l = loc /\ v = val /\ meta = meta0).  
    { rewrite R_POS in AT_K. rewrite nth_error_app2 in AT_K; [| lia].
      rewrite Nat.sub_diag in AT_K. simpl in AT_K. by inversion AT_K. }
    desc. subst loc val meta.
    splits.
    { fold (trace_labels i) in H. rewrite <- H. rewrite H3. auto. }
    { forward eapply (buffer_size_downstream chan (i)) as BUF_SIZE.
      { destruct (trace_length tr); vauto. simpl in *. lia. }
      simpl in BUF_SIZE. rewrite R_POS.
      rewrite count_upto_next, check0.
      2: { unfold trace_labels. rewrite <- H. unfolder'. intro. desf. }
      rewrite Nat.add_0_r.
      rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE. rewrite BUF_SIZE.
      apply nth_such_self. fold (trace_labels i) in H. rewrite <- H. vauto. }
    { lia. }
    { forward eapply (mr2r_later_fpga i) as LATER; vauto.
      fold (trace_labels i) in H. unfolder'; desf. } }
  { destruct (classic (chan = channel)).
    2: { apply SAME.
         { rewrite <- H0. rewrite <- H2 in AT_K. simpl in AT_K. rewrite updo in AT_K; auto. }
         rewrite <- H. unfolder'. unfold in_chan. unfold lbl_chan_opt. intuition. vauto. }
    subst chan. rewrite <- H2 in AT_K. simpl in AT_K. rewrite upds in AT_K.
    specialize (IHi (S k) l v meta). specialize_full IHi. 
    { rewrite <- H0. simpl. by rewrite DOWNSTREAM. }
    desc. exists mr.
    splits; vauto.
    { replace (count_upto (fpga_read_resp' ∩₁ in_chan channel) (S i)) with (count_upto (fpga_read_resp' ∩₁ in_chan channel) i + 1).
      { by rewrite <- NPeano.Nat.add_assoc, Nat.add_1_l. }
      rewrite count_upto_next, check1; auto.
      unfold trace_labels. by rewrite <- H. }
    apply le_lt_or_eq in PROP_AFTER. des; [done| ].

    exfalso.
    assert (fpga_mem_read' (trace_labels mr)) by (unfolder'; desf).
    unfold mem_read2read in PROP_AFTER. 
    destruct (excluded_middle_informative _).
    2: vauto.
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    assert (same_chan (trace_labels mr) = in_chan channel) as CH_REWR.
    { rewrite MREAD. ins. apply set_extensionality. 
      unfold same_chan, in_chan. simpl. red. splits; red; ins; desc; vauto. }
    rewrite CH_REWR in *. subst x.
    red in WRITE_POS. desc. lia. }
Qed.

Lemma w2p_preserves_info w (DOM: NOmega.lt_nat_l w (trace_length tr)) (W: fpga_write' (trace_labels w)):
  meta_l (trace_labels w) = meta_l (trace_labels (write2prop w)) /\
  loc_l (trace_labels w) = loc_l (trace_labels (write2prop w)) /\
  val_l (trace_labels w) = val_l (trace_labels (write2prop w)).
Proof.
  unfold write2prop.
  ex_des.
  ex_des.
  destruct (constructive_indefinite_description).
  simpl.
  desf.
  unfold meta_l.
  destruct THREAD_PROP.
  remember (TSi x P_DOM def_lbl) as STEP.
  inversion STEP; fold (trace_labels x) in *.
  all: try by (exfalso; unfolder'; desf).
  forward eapply (buffer_sources_upstream_wr x channel P_DOM 0); eauto.
  { rewrite <- H2. simpl. rewrite UPSTREAM. simpl. eauto. }
  ins.
  desf.
  assert (same_chan (EventLab e) = in_chan c) as CH_R. { desf. destruct e; desf. destruct e; desf. unfold same_chan in *. same_chan_prover. }
  rewrite CH_R in W_P_CORR.
  rewrite Nat.add_0_r in WRITE_POS.
  rewrite <- W_P_CORR in WRITE_POS.
  assert (nth_such (count_upto (fpga_write' ∩₁ in_chan c) w) (fpga_write' ∩₁ in_chan c) w).
  { apply nth_such_self. destruct (trace_labels w); desf. do 2 (destruct e; desf). rewrite <- CH_R. split; vauto.  }
  assert (w = trace_index (FpgaEvent (Fpga_write_resp c l v) ind m)) by (eapply nth_such_unique; eauto).
  rewrite H3 in Heq.
  rewrite trace_index_simpl' in Heq; vauto.
Qed.

Lemma any_ups2prop_preserves_info w (DOM: NOmega.lt_nat_l w (trace_length tr)) (W: fpga_up_prop (trace_labels w)):
  meta_l (trace_labels w) = meta_l (trace_labels (any_ups2prop w))
  /\ ((fpga_write' (trace_labels w) /\ is_fpga_prop (trace_labels (any_ups2prop w)))
    \/ (fpga_read_ups' (trace_labels w) /\ fpga_mem_read' (trace_labels (any_ups2prop w)))).
Proof.
  unfold any_ups2prop.
  ex_des.
  destruct (constructive_indefinite_description).
  simpl.
  desf.
  unfold meta_l.
  destruct THREAD_PROP.
  remember (TSi x P_DOM def_lbl) as STEP.
  inversion STEP; fold (trace_labels x) in *.
  all: try by (exfalso; unfolder'; desf).
  { forward eapply (buffer_sources_upstream_write_generalized x channel P_DOM 0); eauto.
    { rewrite <- H2. simpl. rewrite UPSTREAM. simpl. eauto. }
    ins.
    desc.
    assert (same_chan (trace_labels w) = in_chan channel) as CH_R. { desf. destruct (trace_labels w); unfolder'; desf; unfold same_chan in *; same_chan_prover. }
    rewrite CH_R in W_P_CORR.
    rewrite Nat.add_0_r in WRITE_POS.
    rewrite <- W_P_CORR in WRITE_POS.
    desf.
    all: try by (exfalso; unfolder'; desf).
    2: { replace c with c0 in *.
      2: { red in H0; unfold lbl_chan_opt in *; desf. }
      assert (nth_such (count_upto (fpga_up_prop ∩₁ in_chan c0) w) (fpga_up_prop ∩₁ in_chan c0) w).
      { apply nth_such_self. destruct (trace_labels w); desf. }

      assert (w = w0) by (eapply nth_such_unique; eauto).
      rewrite H3 in Heq.
      rewrite Heq in *; vauto. }

    destruct e; (try by unfolder'; desf).
    destruct e; (try by unfolder'; desf).
    replace c with c0 in *.
    2: { red in H0; unfold lbl_chan_opt in *; desf. }
    assert (nth_such (count_upto (fpga_up_prop ∩₁ in_chan c0) w) (fpga_up_prop ∩₁ in_chan c0) w).
    { apply nth_such_self. destruct (trace_labels w); desf. } 
      assert (w = w0) by (eapply nth_such_unique; eauto).
      rewrite H3 in Heq.
      rewrite Heq in *; vauto. }
  forward eapply (buffer_sources_upstream_read_generalized x channel P_DOM 0); eauto.
  { rewrite <- H2. simpl. rewrite UPSTREAM. simpl. eauto. }
  ins.
  desc.
  assert (same_chan (trace_labels w) = in_chan channel) as CH_R. { desf. destruct (trace_labels w); unfolder'; desf; unfold same_chan in *; same_chan_prover. }
  rewrite CH_R in W_P_CORR.
  rewrite Nat.add_0_r in WRITE_POS.
  rewrite <- W_P_CORR in WRITE_POS.
  desf.
  all: try by (exfalso; unfolder'; desf).
  { destruct e; (try by unfolder'; desf).
    destruct e; (try by unfolder'; desf).
    replace c with c0 in *.
    2: { red in H0; unfold lbl_chan_opt in *; desf. }
    assert (nth_such (count_upto (fpga_up_prop ∩₁ in_chan c0) w) (fpga_up_prop ∩₁ in_chan c0) w).
    { apply nth_such_self. destruct (trace_labels w); desf. }
    assert (w = mr) by (eapply nth_such_unique; eauto).
    rewrite H3 in Heq.
    rewrite Heq in MREAD; desf. }
  replace c with c0 in *.
  2: { red in H0; unfold lbl_chan_opt in *; desf. }
  assert (nth_such (count_upto (fpga_up_prop ∩₁ in_chan c0) w) (fpga_up_prop ∩₁ in_chan c0) w).
  { apply nth_such_self. destruct (trace_labels w); desf. }
  assert (w = mr) by (eapply nth_such_unique; eauto).
  rewrite H3 in Heq.
  split.
  { rewrite Heq in MREAD. vauto. }
  right. splits; vauto.
Qed.

Lemma read_meta_unique_aux w1 w2 (DOM1: NOmega.lt_nat_l w1 (trace_length tr)) (DOM2: NOmega.lt_nat_l w2 (trace_length tr))
  (ORDER: w1 < w2)
  (W1: fpga_read_resp' (trace_labels w1)) (W2: fpga_read_resp' (trace_labels w2))
  (META: meta_l (trace_labels w1) = meta_l (trace_labels w2)):
  False.
Proof.
  destruct WF.
  red in PAIR_UNIQUE.
  destruct (fpga_read_structure (trace_labels w1)); vauto.
  destruct (fpga_read_structure (trace_labels w2)); vauto.
  desf.
  replace meta0 with meta in *.
  2: { unfold meta_l in *; desf. } 
  specialize (PAIR_UNIQUE w1 w2 index0 index).
  specialize_full PAIR_UNIQUE  ; eauto; vauto.
Qed.

Lemma read_meta_unique w1 w2 (DOM1: NOmega.lt_nat_l w1 (trace_length tr)) (DOM2: NOmega.lt_nat_l w2 (trace_length tr))
  (W1: fpga_read_resp' (trace_labels w1)) (W2: fpga_read_resp' (trace_labels w2))
  (META: meta_l (trace_labels w1) = meta_l (trace_labels w2)):
  w1 = w2.
Proof.
  assert (w1 < w2 \/ w1 > w2 \/ w1 = w2) as OR; [lia|].
  destruct OR as [INEQ | [INEQ | EQ]]; auto.
  - exfalso. eapply (read_meta_unique_aux w1 w2); eauto.
  - exfalso. eapply (read_meta_unique_aux w2 w1); eauto.
Qed.

Lemma prop_meta_unique_aux w1 w2 (DOM1: NOmega.lt_nat_l w1 (trace_length tr)) (DOM2: NOmega.lt_nat_l w2 (trace_length tr))
  (ORDER: w1 < w2)
  (W1: is_fpga_prop (trace_labels w1)) (W2: is_fpga_prop (trace_labels w2))
  (META: meta_l (trace_labels w1) = meta_l (trace_labels w2)):
  False.
Proof.
  destruct (fpga_memflush_structure (trace_labels w1)); vauto.
  destruct (fpga_memflush_structure (trace_labels w2)); vauto.
  desf.
  forward eapply (TSi w1) with (d := def_lbl) as STEP1; vauto.
  forward eapply (TSi w2) with (d := def_lbl) as STEP2; vauto.
  inversion STEP1.
  all: (fold (trace_labels w1) in H3; rewrite <- H3 in H; desf).
  inversion STEP2.
  all: (fold (trace_labels w2) in H; rewrite <- H in H0; desf).
  forward eapply (buffer_sources_upstream_wr w1 x) with (k := 0) (l := loc0) (v := val0) (meta := meta0); eauto; vauto.
  { rewrite <- H2.
    simpl.
    rewrite UPSTREAM.
    simpl.
    vauto. }
  forward eapply (buffer_sources_upstream_wr w2 x0) with (k := 0) (l := loc) (v := val) (meta := meta); eauto; vauto.
  { rewrite <- H1.
    simpl.
    rewrite UPSTREAM0.
    simpl.
    vauto. }
  ins; desf.
  rewrite Nat.add_0_r in *.
  unfold meta_l in *; desf. 
  remember (PAIR_UNIQUE tr WF) as PAIR_UNIQUE.
  red in PAIR_UNIQUE.

  remember (trace_index (FpgaEvent (Fpga_write_resp c0 l0 v0) ind0 m)) as ir0.
  remember (trace_index (FpgaEvent (Fpga_write_resp c l v) ind m)) as ir.

  assert (ir0 < ir \/ ir0 > ir \/ ir0 = ir) as OR; [lia|].
  destruct OR as [INEQ | [INEQ | EQ]]; auto.
  3: { subst ir0 ir; forward eapply (ti_inj _ _ _ _ EQ).
       ins; desf.
       forward eapply (count_upto_more_strict w1 w2 (is_fpga_prop ∩₁ in_chan c)); eauto.
       { rewrite Heq. split; desf. }
       intro LE.
       unfold nth_such in *.
       lia.
       Unshelve.
       all: vauto.
     }
  { clear HeqPAIR_UNIQUE.
    specialize (PAIR_UNIQUE ir0 ir ind0 ind).
    specialize_full PAIR_UNIQUE; vauto.
    { apply Eninit_in_trace; vauto. }
    { rewrite trace_index_simpl; vauto. }
    { rewrite trace_index_simpl; vauto. }
    desf. }
  { clear HeqPAIR_UNIQUE.
    specialize (PAIR_UNIQUE ir ir0 ind ind0).
    specialize_full PAIR_UNIQUE; vauto.
    { apply Eninit_in_trace; vauto. }
    { rewrite trace_index_simpl; vauto. }
    { rewrite trace_index_simpl; vauto. }
    desf. }
Qed.

Lemma prop_meta_unique w1 w2 (DOM1: NOmega.lt_nat_l w1 (trace_length tr)) (DOM2: NOmega.lt_nat_l w2 (trace_length tr))
  (W1: is_fpga_prop (trace_labels w1)) (W2: is_fpga_prop (trace_labels w2))
  (META: meta_l (trace_labels w1) = meta_l (trace_labels w2)):
  w1 = w2.
Proof.
  assert (w1 = w2 \/ w1 < w2 \/ w1 > w2) as OR by lia.
  destruct OR as [EQ | [INEQ | INEQ]]; auto.
  - exfalso; eapply (prop_meta_unique_aux w1 w2); eauto. 
  - exfalso; eapply (prop_meta_unique_aux w2 w1); eauto.
Qed.


Lemma write_resp_meta_unique_aux w1 w2 (DOM1: NOmega.lt_nat_l w1 (trace_length tr)) (DOM2: NOmega.lt_nat_l w2 (trace_length tr))
  (ORDER: w1 < w2)
  (W1: fpga_write' (trace_labels w1)) (W2: fpga_write' (trace_labels w2))
  (META: meta_l (trace_labels w1) = meta_l (trace_labels w2)):
  False.
Proof.
  destruct WF.
  red in PAIR_UNIQUE.
  destruct (fpga_write_structure (trace_labels w1)); vauto.
  destruct (fpga_write_structure (trace_labels w2)); vauto.
  desf.
  replace meta0 with meta in *.
  2: { unfold meta_l in *; desf. } 
  specialize (PAIR_UNIQUE w1 w2 index0 index).
  specialize_full PAIR_UNIQUE  ; eauto; vauto.
Qed.

Lemma write_resp_meta_unique w1 w2 (DOM1: NOmega.lt_nat_l w1 (trace_length tr)) (DOM2: NOmega.lt_nat_l w2 (trace_length tr))
  (W1: fpga_write' (trace_labels w1)) (W2: fpga_write' (trace_labels w2))
  (META: meta_l (trace_labels w1) = meta_l (trace_labels w2)):
  w1 = w2.
Proof.
  assert (w1 < w2 \/ w1 > w2 \/ w1 = w2) as OR; [lia|].
  destruct OR as [INEQ | [INEQ | EQ]]; auto.
  - exfalso. eapply (write_resp_meta_unique_aux w1 w2); eauto.
  - exfalso. eapply (write_resp_meta_unique_aux w2 w1); eauto.
Qed.

Lemma read_ups2mem_read_preserves_info r (DOM: NOmega.lt_nat_l r (trace_length tr)) (R: fpga_read_ups' (trace_labels r)):
  meta_l (trace_labels r) = meta_l (trace_labels (read_ups2mem_read r)) /\
  loc_l (trace_labels r) = loc_l (trace_labels (read_ups2mem_read r)).
Proof.
  unfold read_ups2mem_read.
  ex_des.
  destruct (constructive_indefinite_description).
  simpl.
  desf.
  unfold meta_l.
  destruct R_PROP.
  remember (TSi x P_DOM def_lbl) as STEP.
  inversion STEP; fold (trace_labels x) in *.
  all: try by (exfalso; unfolder'; desf).
  forward eapply (buffer_sources_upstream_rd x channel P_DOM 0); eauto.
  { rewrite <- H2. simpl. rewrite UPSTREAM. simpl. eauto. }
  ins.
  desf.
  assert (same_chan (FpgaReadToUpstream c l m) = in_chan c) as CH_R. { same_chan_prover. }
  assert (c = c0) by ( unfold same_chan in H0; desf ).
  subst c0.
  rewrite CH_R in RS_MR_CORR.
  rewrite Nat.add_0_r in WRITE_POS.
  rewrite <- RS_MR_CORR in WRITE_POS.
  assert (nth_such (count_upto (fpga_read_ups' ∩₁ in_chan c) r) (fpga_read_ups' ∩₁ in_chan c) r).
  { apply nth_such_self. destruct (trace_labels r); desf. } 
  assert (r = mr) by (eapply nth_such_unique; eauto).
  rewrite H3 in Heq.
  rewrite MREAD in Heq.
  vauto.
Qed.

Lemma w2p_in_anyups2prop w (DOM: NOmega.lt_nat_l w (trace_length tr)) (W: fpga_write' (trace_labels w)):
  write2prop w = any_ups2prop w.
Proof.
  forward eapply (w2p_preserves_info w DOM W) as [META [LOC VAL]].
  assert (fpga_up_prop (trace_labels w)) as U by (unfold fpga_up_prop; unfolder'; desf; intuition).
  forward eapply (any_ups2prop_preserves_info w DOM U) as [META' [WR | BAD]].
  2: { destruct BAD; unfolder'; desf. }
  rewrite META in *.
  destruct WR.
  eapply prop_meta_unique; vauto.
  { unfold write2prop. ex_des. ex_des. destruct constructive_indefinite_description. simpl; desf. }
  { unfold any_ups2prop. ex_des. destruct constructive_indefinite_description. simpl; desf. }
  unfold write2prop. ex_des. ex_des. destruct constructive_indefinite_description. simpl; desf.
  destruct THREAD_PROP; vauto.
Qed.


Lemma mr2r_preserves_info mr (DOM: NOmega.lt_nat_l mr (trace_length tr)) (MR: fpga_mem_read' (trace_labels mr)):
  meta_l (trace_labels mr) = meta_l (trace_labels (mem_read2read mr)) /\
  loc_l (trace_labels mr) = loc_l (trace_labels (mem_read2read mr)) /\
  val_l (trace_labels mr) = val_l (trace_labels (mem_read2read mr)).
Proof.
  unfold mem_read2read.
  ex_des.
  destruct (constructive_indefinite_description).
  simpl.
  desf.
  unfold meta_l.
  destruct THREAD_PROP.
  remember (TSi x P_DOM def_lbl) as STEP.
  inversion STEP; fold (trace_labels x) in *.
  all: try by (exfalso; unfolder'; desf).
  forward eapply (buffer_sources_downstream x channel P_DOM 0); eauto.
  { rewrite <- H2. simpl. rewrite DOWNSTREAM. simpl. eauto. }
  ins.
  desf.
  assert (same_chan (FpgaMemRead c l v m) = in_chan c) as CH_R. { same_chan_prover. }
  rewrite CH_R in RS_MR_CORR.
  assert (c = channel) as CH_EQ. { unfold same_chan, in_chan in *; desf. }
  subst channel.
  rewrite Nat.add_0_r in WRITE_POS.
  rewrite <- RS_MR_CORR in WRITE_POS.
  assert (nth_such (count_upto (fpga_mem_read' ∩₁ in_chan c) mr) (fpga_mem_read' ∩₁ in_chan c) mr).
  { apply nth_such_self. destruct (trace_labels mr); desf. }
  assert (mr = mr0) by (eapply nth_such_unique; eauto).
  rewrite <- Heq.
  simpl.
  assert (loc = loc_l (trace_labels mr0)) as LOC0 by (unfold loc_l; desf).
  assert (val = val_l (trace_labels mr0)) as VAL0 by (unfold val_l; desf).
  assert (meta = meta_l (trace_labels mr0)) as META0 by (unfold meta_l; desf).
  rewrite LOC0, VAL0, META0.
  rewrite H3.
  unfold meta_l; desf.
Qed.

Lemma read2mem_read_preserves_info r (DOM: NOmega.lt_nat_l r (trace_length tr)) (MR: fpga_read_resp' (trace_labels r)):
  meta_l (trace_labels r) = meta_l (trace_labels (read2mem_read r)) /\
  loc_l (trace_labels r) = loc_l (trace_labels (read2mem_read r)) /\
  val_l (trace_labels r) = val_l (trace_labels (read2mem_read r)).
Proof.
  assert (exists ch, lbl_chan_opt (trace_labels r) = Some ch) as [chR CH]. { unfold lbl_chan_opt. desf. exists c; desf. }
  assert (fpga_mem_read' (trace_labels (read2mem_read r))) as MR'. { eapply (r2mr_fpga r chR); eauto. }
  forward eapply (mr2r_preserves_info (read2mem_read r)) as PRES; eauto.
  { unfold read2mem_read. ex_des. destruct constructive_indefinite_description. ins. desf. }
  assert (mem_read2read (read2mem_read r) = r) as R_SELF. { eapply read2mem2read; eauto. }
  destruct PRES as [MEQ [LEQ VEQ]].
  splits.
  - rewrite MEQ; rewrite R_SELF; auto.
  - rewrite LEQ; rewrite R_SELF; auto.
  - rewrite VEQ; rewrite R_SELF; auto.
Qed.

Lemma memread_meta_unique_aux r1 r2 (DOM1: NOmega.lt_nat_l r1 (trace_length tr)) (DOM2: NOmega.lt_nat_l r2 (trace_length tr))
  (ORDER: r1 < r2)
  (W1: fpga_mem_read' (trace_labels r1)) (W2: fpga_mem_read' (trace_labels r2))
  (META: meta_l (trace_labels r1) = meta_l (trace_labels r2)):
  False.
Proof.
  remember (mem_read2read r1) as resp1.
  remember (mem_read2read r2) as resp2.
  forward eapply (mr2r_preserves_info r1); vauto.
  forward eapply (mr2r_preserves_info r2); vauto.
  ins.
  destruct H as [MEQ1 _].
  destruct H0 as [MEQ2 _].
  unfold mem_read2read in *.
  do 2 ex_des.
  do 2 destruct constructive_indefinite_description.
  simpl in *.
  desf.
  assert (x0 = x \/ x0 < x \/ x0 > x) as OR by lia.
  destruct OR as [EQ | [INEQ | INEQ]]; auto.
  { subst.
    destruct (fpga_memread_structure (trace_labels r1)); vauto.
    destruct (fpga_memread_structure (trace_labels r2)); vauto.
    desf.
    rename x1 into c2.
    rename x0 into c1.
    destruct THREAD_PROP, THREAD_PROP0. unfold same_chan in H2, H4.
    unfold lbl_chan_opt, chan_opt in *; desf.
    rename c2 into c1.
    replace (same_chan (FpgaMemRead c1 loc val meta)) with (same_chan (FpgaMemRead c1 loc0 val0 meta0)) in *.
    2: { same_chan_prover. }
    rewrite <- RS_MR_CORR0 in RS_MR_CORR.
    forward eapply (count_upto_more_strict r1 r2 (fpga_mem_read' ∩₁ same_chan (FpgaMemRead c1 loc0 val0 meta0))); eauto.
    { rewrite Heq; desf. }
    ins. lia. }
  { remember (PAIR_UNIQUE tr WF) as PAIR_UNIQUE.
    red in PAIR_UNIQUE.
    clear HeqPAIR_UNIQUE.
    destruct (fpga_read_structure (trace_labels x0)); vauto.
    { destruct THREAD_PROP; desf. }
    destruct (fpga_read_structure (trace_labels x)); vauto.
    { destruct THREAD_PROP0; desf. }
    desf.
    replace meta0 with meta in *.
    2: { unfold meta_l in *; desf. }
    forward eapply (PAIR_UNIQUE x0 x); eauto. }
  remember (PAIR_UNIQUE tr WF) as PAIR_UNIQUE.
  red in PAIR_UNIQUE.
  clear HeqPAIR_UNIQUE.
  destruct (fpga_read_structure (trace_labels x0)); vauto.
  { destruct THREAD_PROP; desf. }
  destruct (fpga_read_structure (trace_labels x)); vauto.
  { destruct THREAD_PROP0; desf. }
  desf.
  replace meta0 with meta in *.
  2: { unfold meta_l in *; desf. }
  forward eapply (PAIR_UNIQUE x x0); eauto.
Qed.

Lemma memread_meta_unique r1 r2 (DOM1: NOmega.lt_nat_l r1 (trace_length tr)) (DOM2: NOmega.lt_nat_l r2 (trace_length tr))
  (W1: fpga_mem_read' (trace_labels r1)) (W2: fpga_mem_read' (trace_labels r2))
  (META: meta_l (trace_labels r1) = meta_l (trace_labels r2)):
  r1 = r2.
Proof.
  destruct (lt_eq_lt_dec r1 r2) as [[LT | EQ] | GT]; auto.
  { exfalso. eapply (memread_meta_unique_aux r1 r2); eauto. }
  exfalso. eapply (memread_meta_unique_aux r2 r1); eauto.
Qed.

Lemma read_ups2mem_read_in_anyups2prop r (DOM: NOmega.lt_nat_l r (trace_length tr)) (R: fpga_read_ups' (trace_labels r)):
  read_ups2mem_read r = any_ups2prop r.
Proof.
  forward eapply (read_ups2mem_read_preserves_info r DOM R) as [META LOC].
  assert (fpga_up_prop (trace_labels r)) as U by (unfold fpga_up_prop; unfolder'; desf; intuition).
  forward eapply (any_ups2prop_preserves_info r DOM U) as [META' [BAD | RD]].
  { destruct BAD; unfolder'; desf. }
  rewrite META in *.
  destruct RD.
  eapply memread_meta_unique; vauto.
  { unfold read_ups2mem_read. ex_des. destruct constructive_indefinite_description. simpl; desf. }
  { unfold any_ups2prop. ex_des. destruct constructive_indefinite_description. simpl; desf. }
  unfold read_ups2mem_read. ex_des. destruct constructive_indefinite_description. simpl; desf.
  destruct R_PROP; unfolder'; desf.
Qed.

Definition req_resp_pair' l1 l2 := match l1, l2 with
  | EventLab e1, EventLab e2 => req_resp_pair e1 e2
  | _, _ => False
  end.


Lemma readpair_exists' e 
  (ENE: Eninit e)
  (IS_REQ: is_rd_req e)
  :
  exists e', 
    ⟪LATER: (trace_index e) < (trace_index e')⟫ /\
    ⟪EN: Eninit e'⟫ /\
    ⟪PAIR: req_resp_pair e e'⟫ /\ 
    ⟪VIS_LT: vis_lt' e e'⟫.
Proof.
  forward eapply (read_buffer_prop_lem (trace_index e)).
  { rewrite trace_index_simpl'; vauto. }
  ins; desf.
  destruct UPS_PROP as [UPS_PROP CHAN].
  assert (exists chR, lbl_chan_opt (trace_labels p) = Some chR) as [chR LBLC]. { unfold lbl_chan_opt; desf. exists c; auto. }
  forward eapply (ups2mr_fpgar p); vauto.
  ins; desf.
  fold (trace_labels (read_ups2mem_read p)) in *.
  destruct H as [MEM_READ CHAN'].
  forward eapply (read_ups2mem_read_preserves_info p); vauto.
  ins.
  destruct H as [SAME_META' _].
  remember (read_ups2mem_read p) as mr.
  assert (exists chR, lbl_chan_opt (trace_labels mr) = Some chR) as [chMR LBLC']. { unfold lbl_chan_opt; desf. exists c; auto. }
  forward eapply (mr2r_fpgar mr chMR); auto.
  intro H.
  destruct H as [RESP CHAN''].
  fold (trace_labels (mem_read2read mr)) in *.
  remember (mem_read2read mr) as resp.
  forward eapply (mr2r_preserves_info mr); auto.
  { unfold read_ups2mem_read in *. ex_des. destruct constructive_indefinite_description. ins. desf. }
  ins.
  remember (trace_labels resp) as rsp_label.
  destruct (rsp_label); try by desf.
  assert (trace_index e <= resp) as TRACE_BEFORE.
  { 
    forward eapply (mr2r_later_fpga mr); auto.
    forward eapply (r_up2mem_later_fpga p); auto.
    ins; lia.
  }
  rewrite trace_index_simpl' in *; vauto.
  assert (Eninit e0) as EN0.
  { eapply (in_trace_Eninit (mem_read2read (read_ups2mem_read p)) e0); vauto.
    destruct (classic (NOmega.lt_nat_l (mem_read2read (read_ups2mem_read p)) (trace_length tr))); auto.
    forward eapply (proj2 (ge_default (mem_read2read (read_ups2mem_read p)))); ins.
    rewrite <- Heqrsp_label in H1.
    unfold def_lbl; unfolder'; desf. }
  exists e0; splits.
  {
    forward eapply (r_up2mem_later_fpga p); auto.
    forward eapply (mr2r_later_fpga (read_ups2mem_read p)); auto.
    ins. 
    cut (trace_index e0 = mem_read2read (read_ups2mem_read p)); [lia|].
    apply trace_index_label; vauto. }
  { desf. }
  { red.
    desf.
    assert (c = c0). {
      replace (same_chan (EventLab (FpgaEvent (Fpga_read_req c x) index m))) with (in_chan c) in CHAN.
      2: { same_chan_prover. }
      assert (lbl_chan_opt (trace_labels p) = Some c) as CH. { unfold in_chan in CHAN. unfold lbl_chan_opt in *. desf. }
      rewrite CH in *.
      assert (lbl_chan_opt (trace_labels (read_ups2mem_read p)) = Some c) as CH'. { unfold in_chan in *. unfold lbl_chan_opt in *. desf. }
      rewrite CH' in *.
      unfold in_chan in CHAN''.
      unfold lbl_chan_opt in *.
      desf.
    }
    assert (m = m0). { rename H into SAME_META''.
      rewrite <- SAME_META in SAME_META'.
      rewrite <- SAME_META' in SAME_META''.
      unfold meta_l in SAME_META''; desf. }
    subst m. subst c.
    vauto. }
    unfold vis_lt'; right.
    apply seq_eqv_lr; splits; auto.
    unfold vis'.
    do 6 ex_des.
    eapply Nat.lt_trans; eauto.
    replace (trace_index e0) with (mem_read2read (read_ups2mem_read p)). 
    2: { symmetry. apply trace_index_label; vauto. }
    erewrite mem2read2mem; eauto.
    eapply r_up2mem_later_fpga; vauto.
Qed.

Lemma writepair_exists' e 
  (ENE: Eninit e)
  (IS_REQ: is_wr_req e)
  :
  exists e', 
    ⟪LATER: (trace_index e) < (trace_index e')⟫ /\
    ⟪EN: Eninit e'⟫ /\
    ⟪PAIR: req_resp_pair e e'⟫ /\ 
    ⟪VIS_LT: vis_lt' e e'⟫.
Proof.
  destruct WF.
  red in WRITEPAIR_EXISTS.
  specialize (WRITEPAIR_EXISTS (trace_index e) def_lbl).
  specialize_full WRITEPAIR_EXISTS; vauto.
  { apply trace_index_simpl; vauto. }
  desf.
  assert (Eninit e2) as EN2 by (eapply in_trace_Eninit; eauto).
  exists e2; splits; vauto.
  { erewrite (trace_index_label j e2); vauto. }
  red; right.
  apply seq_eqv_lr; splits; vauto.
  unfold vis'.
  do 5 ex_des.
  forward eapply (w2p_later_fpga (trace_index e2)) as LATER; eauto.
  { rewrite trace_index_simpl'; vauto. }
  cut (trace_index e < trace_index e2); [lia|].
  erewrite (trace_index_label j e2); vauto.
Qed.

Lemma fenceonepair_exists' e 
  (ENE: Eninit e)
  (IS_REQ: is_fence_req_one e)
  :
  exists e', 
    ⟪LATER: (trace_index e) < (trace_index e')⟫ /\
    ⟪EN: Eninit e'⟫ /\
    ⟪PAIR: req_resp_pair e e'⟫ /\ 
    ⟪VIS_LT: vis_lt' e e'⟫.
Proof.
  destruct WF.
  red in FENCEONEPAIR_EXISTS.
  specialize (FENCEONEPAIR_EXISTS (trace_index e) def_lbl).
  specialize_full FENCEONEPAIR_EXISTS; vauto.
  { apply trace_index_simpl; vauto. }
  desf.
  assert (Eninit e2) as EN2 by (eapply in_trace_Eninit; eauto).
  exists e2; splits; vauto.
  { erewrite (trace_index_label j e2); vauto. }
  red; right.
  apply seq_eqv_lr; splits; vauto.
  unfold vis'.
  do 6 ex_des.
  erewrite (trace_index_label j e2); vauto.
Qed.

Lemma fenceallpair_exists' e 
  (ENE: Eninit e)
  (IS_REQ: is_fence_req_all e)
  :
  exists e', 
    ⟪LATER: (trace_index e) < (trace_index e')⟫ /\
    ⟪EN: Eninit e'⟫ /\
    ⟪PAIR: req_resp_pair e e'⟫ /\ 
    ⟪VIS_LT: vis_lt' e e'⟫.
Proof.
  destruct WF.
  red in FENCEALLPAIR_EXISTS.
  specialize (FENCEALLPAIR_EXISTS (trace_index e) def_lbl).
  specialize_full FENCEALLPAIR_EXISTS; vauto.
  { apply trace_index_simpl; vauto. }
  desf.
  assert (Eninit e2) as EN2 by (eapply in_trace_Eninit; eauto).
  exists e2; splits; vauto.
  { erewrite (trace_index_label j e2); vauto. }
  red; right.
  apply seq_eqv_lr; splits; vauto.
  unfold vis'.
  do 6 ex_des.
  erewrite (trace_index_label j e2); vauto.
Qed.

Definition read_req2resp e (ENE: Eninit e) (RD_REQ: is_rd_req e) :=
  proj1_sig (constructive_indefinite_description _ (readpair_exists' e ENE RD_REQ)).

Definition write_req2resp e (ENE: Eninit e) (RD_REQ: is_wr_req e) :=
  proj1_sig (constructive_indefinite_description _ (writepair_exists' e ENE RD_REQ)).

Definition fence_one_req2resp e (ENE: Eninit e) (RD_REQ: is_fence_req_one e) :=
  proj1_sig (constructive_indefinite_description _ (fenceonepair_exists' e ENE RD_REQ)).

Definition fence_all_req2resp e (ENE: Eninit e) (RD_REQ: is_fence_req_all e) :=
  proj1_sig (constructive_indefinite_description _ (fenceallpair_exists' e ENE RD_REQ)).

Lemma read_req2resp_readpair e (ENE: Eninit e) (RD_REQ: is_rd_req e):
  (readpair G) e (read_req2resp e ENE RD_REQ).
Proof.
  red. ins. apply seq_eqv_lr.
  unfold read_req2resp.
  splits.
  { unfold EG; split; desf. right; desf. }
  { destruct constructive_indefinite_description; splits; desf. }
  destruct constructive_indefinite_description; splits; simpl.
  split; desf.
  { unfold EG. right; desf. }
  red in a1; unfolder'; desf.
Qed.

Lemma write_req2resp_writepair e (ENE: Eninit e) (REQ: is_wr_req e):
  (writepair G) e (write_req2resp e ENE REQ).
Proof.
  red. ins. apply seq_eqv_lr.
  unfold write_req2resp.
  splits.
  { unfold EG; split; desf. right; desf. }
  { destruct constructive_indefinite_description; splits; desf. }
  destruct constructive_indefinite_description; splits; simpl.
  split; desf.
  { unfold EG. right; desf. }
  red in a1; unfolder'; desf.
Qed.

Lemma fence_one_req2resp_fenceonepair e (ENE: Eninit e) (REQ: is_fence_req_one e):
  (fenceonepair G) e (fence_one_req2resp e ENE REQ).
Proof.
  red. ins. apply seq_eqv_lr.
  unfold fence_one_req2resp.
  splits.
  { unfold EG; split; desf. right; desf. }
  { destruct constructive_indefinite_description; splits; desf. }
  destruct constructive_indefinite_description; splits; simpl.
  split; desf.
  { unfold EG. right; desf. }
  red in a1; unfolder'; desf.
Qed.

Lemma fence_all_req2resp_fenceallpair e (ENE: Eninit e) (REQ: is_fence_req_all e):
  (fenceallpair G) e (fence_all_req2resp e ENE REQ).
Proof.
  red. ins. apply seq_eqv_lr.
  unfold fence_all_req2resp.
  splits.
  { unfold EG; split; desf. right; desf. }
  { destruct constructive_indefinite_description; splits; desf. }
  destruct constructive_indefinite_description; splits; simpl.
  split; desf.
  { unfold EG. right; desf. }
  red in a1; unfolder'; desf.
Qed.

Lemma readpair_unique e e0 e1
  (RP1: readpair G e e0)
  (RP2: readpair G e e1): e0 = e1.
Proof.
  apply seq_eqv_lr in RP1, RP2.
  desf.
  destruct RP1, RP5, RP2, RP3.
  unfolder'. desf.
  destruct RP4 as [_ M1].
  destruct RP0 as [_ M2].
  subst m0. subst m1.
  destruct WF.
  red in PAIR_UNIQUE.
  remember (FpgaEvent (Fpga_read_resp c1 x1 v0) index1 m) as r1.
  remember (FpgaEvent (Fpga_read_resp c x v) index m) as r2.
  cut ((trace_index r1) = (trace_index r2) \/ (trace_index r1) < (trace_index r2) \/ (trace_index r1) > (trace_index r2)); [|lia].
  assert (NOmega.lt_nat_l (trace_index r2) (trace_length tr)).
    { destruct (classic (NOmega.lt_nat_l (trace_index r2) (trace_length tr))); auto.
      exfalso. apply ge_default in H7. rewrite trace_index_simpl' in H7; vauto. destruct H5; desf. }
  assert (NOmega.lt_nat_l (trace_index r1) (trace_length tr)).
    { destruct (classic (NOmega.lt_nat_l (trace_index r1) (trace_length tr))); auto.
      exfalso. apply ge_default in H8. rewrite trace_index_simpl' in H8; vauto. destruct H1; desf. }
  intro CASES; destruct CASES as [EQ | [LEQ | GE]].
  { destruct H1, H5; apply ti_inj; vauto; desf. }
  { red in FPGA_TR_WF. 
    forward eapply (FPGA_TR_WF (trace_index r1) (trace_index r2) def_lbl index1 index
                    (Fpga_read_resp c1 x1 v0) (Fpga_read_resp c x v) m m); 
    eauto.
    { subst r1. eapply trace_index_simpl. destruct H1; desf. }
    { subst r2. eapply trace_index_simpl. destruct H5; desf. }
    specialize PAIR_UNIQUE with (i := trace_index r1) (j := trace_index r2) (meta := m)
                      (fpgaE1 := (Fpga_read_resp c1 x1 v0)) (fpgaE2 := (Fpga_read_resp c x v))
                      (index1 := index1) (index2 := index).
    ins.
    forward eapply PAIR_UNIQUE; eauto.
    { subst r1. apply trace_index_simpl; destruct H1; desf. }
    { subst r2. apply trace_index_simpl; destruct H5; desf. }
    vauto.
   }
  { red in FPGA_TR_WF. 
    forward eapply (FPGA_TR_WF (trace_index r2) (trace_index r1) def_lbl index index1
                   (Fpga_read_resp c x v) (Fpga_read_resp c1 x1 v0) m m); 
    eauto.
    { subst r2. eapply trace_index_simpl. destruct H5; desf. }
    { subst r1. eapply trace_index_simpl. destruct H1; desf. }
    specialize PAIR_UNIQUE with (j := trace_index r1) (i := trace_index r2) (meta := m)
                      (fpgaE2 := (Fpga_read_resp c1 x1 v0)) (fpgaE1 := (Fpga_read_resp c x v))
                      (index1 := index) (index2 := index1).
    ins.
    forward eapply PAIR_UNIQUE; eauto.
    { subst r2. apply trace_index_simpl; destruct H5; desf. }
    { subst r1. apply trace_index_simpl; destruct H1; desf. }
    vauto. }
Qed.

Lemma writepair_unique_aux e e0 e1
  (ORDER: trace_index e0 < trace_index e1)
  (P1: writepair G e e0)
  (P2: writepair G e e1): e0 = e1.
Proof.
  apply seq_eqv_lr in P1, P2.
  desf.
  destruct P1, P5, P2, P3.
  unfolder'. desf.
  destruct P4 as [_ M1].
  destruct P0 as [_ M2].
  destruct M1 as [M1 _].
  destruct M2 as [M2 _].
  subst m0. subst m1.
  destruct WF.
  red in PAIR_UNIQUE.
  remember (FpgaEvent (Fpga_write_resp c1 x1 v1) index1 m) as r1.
  remember (FpgaEvent (Fpga_write_resp c x v) index m) as r2.
  assert (NOmega.lt_nat_l (trace_index r2) (trace_length tr)).
    { destruct (classic (NOmega.lt_nat_l (trace_index r2) (trace_length tr))); auto.
      exfalso. apply ge_default in H7. rewrite trace_index_simpl' in H7; vauto. destruct H5; desf. }
  assert (NOmega.lt_nat_l (trace_index r1) (trace_length tr)).
    { destruct (classic (NOmega.lt_nat_l (trace_index r1) (trace_length tr))); auto.
      exfalso. apply ge_default in H8. rewrite trace_index_simpl' in H8; vauto. destruct H1; desf. }
  red in FPGA_TR_WF. 
  forward eapply (FPGA_TR_WF (trace_index r1) (trace_index r2) def_lbl index1 index
                  (Fpga_write_resp c1 x1 v1) (Fpga_write_resp c x v) m m); 
  eauto.
  { subst r1. eapply trace_index_simpl. destruct H1; desf. }
  { subst r2. eapply trace_index_simpl. destruct H5; desf. }
  specialize PAIR_UNIQUE with (i := trace_index r1) (j := trace_index r2) (meta := m)
                    (fpgaE1 := (Fpga_write_resp c1 x1 v1)) (fpgaE2 := (Fpga_write_resp c x v))
                    (index1 := index1) (index2 := index).
  ins.
  forward eapply PAIR_UNIQUE; eauto.
  { subst r1. apply trace_index_simpl; destruct H1; desf. }
  { subst r2. apply trace_index_simpl; destruct H5; desf. }
  vauto.
Qed.

Lemma writepair_unique e e0 e1
  (P1: writepair G e e0)
  (P2: writepair G e e1): e0 = e1.
Proof.
  assert (trace_index e0 = trace_index e1 \/ trace_index e0 < trace_index e1 \/ trace_index e1 < trace_index e0); [lia|].
  destruct H as [EQ | [LE | GE]].
  - apply ti_inj; apply seq_eqv_lr in P1, P2; destruct P1, P2; desf; destruct H3, H4; unfold EG in *; unfolder'; desf.
  - apply writepair_unique_aux with (e := e) (e0 := e0) (e1 := e1); auto.
  - symmetry. apply writepair_unique_aux with (e := e) (e0 := e1) (e1 := e0); auto.
Qed.  

Lemma fenceonepair_unique_aux e e0 e1
  (ORDER: trace_index e0 < trace_index e1)
  (P1: fenceonepair G e e0)
  (P2: fenceonepair G e e1): e0 = e1.
Proof.
  apply seq_eqv_lr in P1, P2.
  desf.
  destruct P1, P5, P2, P3.
  unfolder'. desf.
  destruct P4 as [_ M1].
  destruct P0 as [_ M2].
  subst m0. subst m1.
  destruct WF.
  red in PAIR_UNIQUE.
  remember (FpgaEvent (Fpga_fence_resp_one c1) index1 m) as r1.
  remember (FpgaEvent (Fpga_fence_resp_one c) index m) as r2.
  assert (NOmega.lt_nat_l (trace_index r2) (trace_length tr)).
    { destruct (classic (NOmega.lt_nat_l (trace_index r2) (trace_length tr))); auto.
      exfalso. apply ge_default in H7. rewrite trace_index_simpl' in H7; vauto. destruct H5; desf. }
  assert (NOmega.lt_nat_l (trace_index r1) (trace_length tr)).
    { destruct (classic (NOmega.lt_nat_l (trace_index r1) (trace_length tr))); auto.
      exfalso. apply ge_default in H8. rewrite trace_index_simpl' in H8; vauto. destruct H1; desf. }
  red in FPGA_TR_WF. 
  forward eapply (FPGA_TR_WF (trace_index r1) (trace_index r2) def_lbl index1 index
                  (Fpga_fence_resp_one c1) (Fpga_fence_resp_one c) m m); 
  eauto.
  { subst r1. eapply trace_index_simpl. destruct H1; desf. }
  { subst r2. eapply trace_index_simpl. destruct H5; desf. }
  specialize PAIR_UNIQUE with (i := trace_index r1) (j := trace_index r2) (meta := m)
                    (fpgaE1 := (Fpga_fence_resp_one c1)) (fpgaE2 := (Fpga_fence_resp_one c))
                    (index1 := index1) (index2 := index).
  ins.
  forward eapply PAIR_UNIQUE; eauto.
  { subst r1. apply trace_index_simpl; destruct H1; desf. }
  { subst r2. apply trace_index_simpl; destruct H5; desf. }
  vauto.
Qed.

Lemma fenceonepair_unique e e0 e1
  (P1: fenceonepair G e e0)
  (P2: fenceonepair G e e1): e0 = e1.
Proof.
  assert (trace_index e0 = trace_index e1 \/ trace_index e0 < trace_index e1 \/ trace_index e1 < trace_index e0); [lia|].
  destruct H as [EQ | [LE | GE]].
  - apply ti_inj; apply seq_eqv_lr in P1, P2; destruct P1, P2; desf; destruct H3, H4; unfold EG in *; unfolder'; desf.
  - apply fenceonepair_unique_aux with (e := e) (e0 := e0) (e1 := e1); auto.
  - symmetry. apply fenceonepair_unique_aux with (e := e) (e0 := e1) (e1 := e0); auto.
Qed.  
   
Lemma fenceallpair_unique_aux e e0 e1
  (ORDER: trace_index e0 < trace_index e1)
  (P1: fenceallpair G e e0)
  (P2: fenceallpair G e e1): e0 = e1.
Proof.
  apply seq_eqv_lr in P1, P2.
  desf.
  destruct P1, P5, P2, P3.
  unfolder'. desf.
  rename m0 into m.
  destruct WF.
  red in PAIR_UNIQUE.
  remember (FpgaEvent (Fpga_fence_resp_all) index1 m) as r1.
  remember (FpgaEvent (Fpga_fence_resp_all) index m) as r2.
  assert (NOmega.lt_nat_l (trace_index r2) (trace_length tr)).
    { destruct (classic (NOmega.lt_nat_l (trace_index r2) (trace_length tr))); auto.
      exfalso. apply ge_default in H7. rewrite trace_index_simpl' in H7; vauto. destruct H5; desf. }
  assert (NOmega.lt_nat_l (trace_index r1) (trace_length tr)).
    { destruct (classic (NOmega.lt_nat_l (trace_index r1) (trace_length tr))); auto.
      exfalso. apply ge_default in H8. rewrite trace_index_simpl' in H8; vauto. destruct H1; desf. }
  red in FPGA_TR_WF. 
  forward eapply (FPGA_TR_WF (trace_index r1) (trace_index r2) def_lbl index1 index
                  (Fpga_fence_resp_all) (Fpga_fence_resp_all) m m); 
  eauto.
  { subst r1. eapply trace_index_simpl. destruct H1; desf. }
  { subst r2. eapply trace_index_simpl. destruct H5; desf. }
  specialize PAIR_UNIQUE with (i := trace_index r1) (j := trace_index r2) (meta := m)
                    (fpgaE1 := (Fpga_fence_resp_all)) (fpgaE2 := (Fpga_fence_resp_all))
                    (index1 := index1) (index2 := index).
  ins.
  forward eapply PAIR_UNIQUE; eauto.
  { subst r1. apply trace_index_simpl; destruct H1; desf. }
  { subst r2. apply trace_index_simpl; destruct H5; desf. }
  vauto.
Qed.

Lemma fenceallpair_unique e e0 e1
  (P1: fenceallpair G e e0)
  (P2: fenceallpair G e e1): e0 = e1.
Proof.
  assert (trace_index e0 = trace_index e1 \/ trace_index e0 < trace_index e1 \/ trace_index e1 < trace_index e0); [lia|].
  destruct H as [EQ | [LE | GE]].
  - apply ti_inj; apply seq_eqv_lr in P1, P2; destruct P1, P2; desf; destruct H3, H4; unfold EG in *; unfolder'; desf.
  - apply fenceallpair_unique_aux with (e := e) (e0 := e0) (e1 := e1); auto.
  - symmetry. apply fenceallpair_unique_aux with (e := e) (e0 := e1) (e1 := e0); auto.
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
    { arewrite (writes ⊆₁ fun e => loc e = loc r /\ vis_lt' e r /\ is_w e) by basic_solver.
      pose proof (fsupp_vis_loc r) as [findom FINDOM].
      red. exists findom. ins. desc. apply FINDOM. red. split; auto.
      split; vauto.
      split; vauto.
      unfolder'; desf. }
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
    { arewrite (writes ⊆₁ fun e => loc e = loc r /\ vis_lt' e r /\ is_w e) by basic_solver.
      pose proof (fsupp_vis_loc r) as [findom FINDOM].
      red. exists findom. ins. desc. apply FINDOM. red. split; auto.
      split; vauto.
      split; vauto.
      unfolder'; desf. }
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
      rewrite Nat.add_1_r, <- VISw, <- H2. simpl.
      forward eapply (@buffer_sources_upstream_wr (vis' w) c) with (k := 0) (l := loc) (v :=val) as [ind_w INDw].
      { destruct (trace_length tr); vauto. simpl in *. lia. }
      { rewrite <- H0. simpl. by rewrite UPSTREAM. }
      simpl in INDw. desc.
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

  remember (trace_nth ind_prev tr def_lbl) as e_prev.
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
  pose proof (r_vis_cpu r Rr) as VISr. 
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
  red. splits; vauto. ins. apply TB_LATEST0. desc. splits; vauto. congruence. 
Qed.

Lemma rf_same_value w r (RF: rf G w r): valw w = valr r.
Proof.
  simpl in RF. apply seq_eqv_lr in RF. destruct RF as [W [RF [Er Rr]]].
  do 2 red in Er. des; [by destruct (init_non_r r)| ]. 
  red in RF. unfold state_before_event in RF.
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
      red. red in RF. desc. splits; vauto.
      { do 2 red in RF1. des.
        { red in RF1. desc. by left. }
        right. apply seq_eqv_lr in RF1. desc.
        by rewrite (r_vis_cpu r) in RF4. }
      ins. desc.
      destruct (classic (is_init y)). 
      { do 2 red in RF2. destruct RF2. 
        { destruct w, y; vauto. left. f_equal. unfold loc in *. simpl in *.
          congruence. }
        red. right. red. left. split; vauto. }
      des; [done| ]. do 2 red in S'1. des; [done| ]. 
      
      apply RF0. splits; vauto. do 2 red. des; vauto. 
      right. apply seq_eqv_lr. splits; vauto.
      by rewrite (r_vis_cpu r). }
    
    inversion TSi; vauto.
    { rewrite <- Heqst in H0. inversion H0. subst.
      unfold valr, valr, SyEvents.loc in *. simpl in *. 
      cut (val = valw w).
      { ins. }
      desc. 
      eapply (@latest_buf_value_read thread w (ThreadEvent thread index (Cpu_load loc val)) val); eauto.
      simpl. rewrite <- Heqst. vauto. }
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
      { ins.
        forward eapply (read2mem_read_preserves_info (trace_index r)); vauto.
        { rewrite trace_index_simpl'; vauto. }
        ins.
        destruct H0 as [META_EQ [LOC_EQ VAL_EQ]].
        rewrite <- H.
        unfold read2mem_read in *.
        destruct (excluded_middle_informative (fpga_read_resp' (trace_labels (trace_index r)))).
        2: { rewrite trace_index_simpl' in n0; vauto. }
        destruct (constructive_indefinite_description); simpl in *.
        rewrite trace_index_simpl' in *; vauto.
        desf.
        destruct THREAD_PROP as [MEM_READ SAME_CH].
        unfold trace_labels in MEM_READ.
        rewrite <- Heqst in TSi.
        inversion TSi; vauto.
        all: try by (unfold fpga_mem_read' in MEM_READ; desf).
        fold (trace_labels x) in H7.
        rewrite <- H7 in *.
        unfolder'; unfold SyEvents.loc, val_l, loc_l, meta_l in *.
        desf.
      } 
      
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


Lemma WFG: Wf G.
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
  { eapply rf_same_value. }
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
Qed.


Lemma empty_inter_minus_same {A: Type} (X Y: A -> Prop):
  X ∩₁ Y ≡₁ ∅ <-> X \₁ Y ≡₁ X.
Proof.
  split.
  { ins. red. split; [basic_solver| ].
    red. ins.
    red in H. desc.
    red. split; auto.
    red in H. specialize (H x).
    red. ins. apply H. basic_solver. }
  { intros. rewrite <- H. basic_solver. }
Qed.

Lemma co_implies_vis_lt: co G ⊆ vis_lt'.
Proof. simpl. basic_solver. Qed.

Lemma fr_implies_vis_lt: fr G ⊆ vis_lt'.
Proof.
  red. intros r w FR. red. right.
  apply (wf_frD WFG), seq_eqv_lr in FR. destruct FR as [Rr [FR Ww]].
  apply (fr_ninit WFG), seq_eqv_r in FR. destruct FR as [FR [Ew NINITw]].
  apply (wf_frE WFG), seq_eqv_lr in FR. destruct FR as [Er [FR _]].
  simpl in *. unfold EG, set_union in *. des; vauto.
  { edestruct (init_non_r); eauto. } 
  apply seq_eqv_lr. splits; auto.
  cut (is_cpu_rd r \/ is_rd_resp r).
  2: { unfolder'; desf; try by (left; vauto); try by (right; vauto). right; auto. right; auto. }
  intro RTYPE.
  destruct RTYPE as [CPU_R | RD_RESP].

  { erewrite r_vis_cpu; eauto.
    pose proof (Nat.lt_trichotomy (trace_index r) (vis' w)). des; auto.
    { exfalso. unfold vis' in H.
      destruct (excluded_middle_informative _) as [W|W].
      {
      unfold write2prop in H. destruct (excluded_middle_informative _) as [W_|W_].
      2: { rewrite trace_index_simpl' in W_; unfolder'; desf. }
      destruct (constructive_indefinite_description _ _) as [p Pp]. simpl in *. desc.
      rewrite <- H in THREAD_PROP.
      unfold trace_labels at 2 in THREAD_PROP. rewrite trace_index_simpl in THREAD_PROP; auto.
      red in THREAD_PROP. desc. vauto. } 
      {
      destruct (excluded_middle_informative _) as [W_|W_].
      2: { unfolder'; desf. }
      unfold write2prop in H.
      ex_des. { clear H. rewrite (trace_index_simpl') in c; vauto. }
      ex_des. 2: { clear H. rewrite (trace_index_simpl') in *; vauto. }
      destruct constructive_indefinite_description; simpl in *; desc.
      rewrite <- H in THREAD_PROP.
      unfold trace_labels at 2 in THREAD_PROP. rewrite trace_index_simpl in THREAD_PROP; auto.
      red in THREAD_PROP. desc. vauto. } 
      }
    exfalso. red in FR. destruct FR as [[w' [RF CO]] NEQ]. unfold transp in RF.
    pose proof (rf_before_prop _ _ RF) as RF_PROP. 
    simpl in RF. apply seq_eqv_lr in RF. desc. red in RF0.  
    destruct (state_before_event r) as [wp rp ups downs mem bufs].
    destruct (excluded_middle_informative (is_cpu_rd r)); vauto.
    destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r) (bufs (exact_tid r))) eqn:BUF_FLT. 
    { desc. red in RF0. desc.
      specialize (RF2 w). specialize_full RF2.
      { splits; vauto.
        { apply (wf_col WFG) in CO. red in CO. congruence.  }
        red. right. apply seq_eqv_lr. splits; auto. by rewrite (r_vis_cpu r CPU_R). }
      red in RF2. des.
      { subst w'. by apply (co_irr WFG w). }
      simpl in CO. apply seq_eqv_lr in CO. destruct CO as [Ww' [[VISw'w LOCw'w] _]].
      forward eapply (strict_partial_order_antisymmetric vis_SPO w w') as EQ; auto.
      subst w'. cdes vis_SPO. eapply vis_SPO0; eauto. }
    desc.
    simpl in CO. apply seq_eqv_lr in CO. destruct CO as [Ww' [[VISw'w LOCw'w] _]].
    do 2 red in VISw'w. des.
    { red in VISw'w. desc. red in RF0. desc.
      destruct (proj1 Eninit_non_init w'). vauto. }
    apply inclusion_seq_eqv_l, inclusion_seq_eqv_r in VISw'w.
    red in RF0. desc.
    specialize_full RF_PROP; vauto.
    lia. } 
    pose proof (Nat.lt_trichotomy (vis' r) (vis' w)). des; auto.
    { exfalso. erewrite fpgar_vis in H; vauto. 
      unfold vis' in H.
      destruct (excluded_middle_informative _) as [W|W].
      {
      unfold write2prop in H. destruct (excluded_middle_informative _) as [W_|W_].
      2: { rewrite trace_index_simpl' in W_; unfolder'; desf. }
      destruct (constructive_indefinite_description _ _) as [p Pp]. simpl in *. desc.
      rewrite <- H in THREAD_PROP.
      unfold read2mem_read in *.
      ex_des. 2: { clear H. rewrite (trace_index_simpl') in *; vauto. }
      destruct constructive_indefinite_description; simpl in *; desc.
      destruct THREAD_PROP, THREAD_PROP0; unfolder'; desf. }
      {
      destruct (excluded_middle_informative _) as [W_|W_].
      2: { unfolder'; desf. }
      unfold write2prop in H.
      ex_des. { clear H. rewrite (trace_index_simpl') in c; vauto. }
      ex_des. 2: { clear H. rewrite (trace_index_simpl') in *; vauto. }
      destruct constructive_indefinite_description; simpl in *; desc.
      rewrite <- H in THREAD_PROP.
      unfold read2mem_read in *.
      ex_des. 2: { clear H. rewrite (trace_index_simpl') in *; vauto. }
      destruct constructive_indefinite_description; simpl in *; desc.
      destruct THREAD_PROP, THREAD_PROP0; unfolder'; desf. }
      }
    exfalso. red in FR. destruct FR as [[w' [RF CO]] NEQ]. unfold transp in RF.
    simpl in RF. apply seq_eqv_lr in RF. desc. red in RF0.  
    destruct (state_before_event r) as [wp rp ups downs mem bufs].
    destruct (excluded_middle_informative (is_cpu_rd r)); [unfolder'; desf|].
    { desc. red in RF0. desc.
      specialize (RF2 w). specialize_full RF2.
      { splits; vauto.
        { apply (wf_col WFG) in CO. red in CO. congruence.  }
        red. right. apply seq_eqv_lr. splits; auto. }
      red in RF2. des.
      { subst w'. by apply (co_irr WFG w). }
      simpl in CO. apply seq_eqv_lr in CO. destruct CO as [Ww' [[VISw'w LOCw'w] _]].
      forward eapply (strict_partial_order_antisymmetric vis_SPO w w') as EQ; auto.
      subst w'. cdes vis_SPO. eapply vis_SPO0; eauto. } 
Qed.

Lemma rfe_implies_vis_lt: rfe G ⊆ vis_lt'.
Proof.
  unfold rfe.
  red. intros w r [RFwr NSBwr].
  forward eapply (rfe_diff_tid w r). { basic_solver. }
  intro DIFF_TID.
  simpl in RFwr. apply seq_eqv_lr in RFwr. destruct RFwr as [Ww [RFwr Rr]]. 
  red in Ww, Rr. desc. 
  red in RFwr.
  destruct (excluded_middle_informative (is_cpu_rd r)).
  {
    remember (state_before_event r) as st. destruct st as [wp rp ups downs mem bufs].   
    destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc r) (bufs (exact_tid r))) eqn:BUF_FLT;
      [red in RFwr; by desc| ].
    desc. red in RFwr. desc.
    exfalso; apply DIFF_TID.
    unfold exact_tid, tid in *; destruct w, r; desf.
  }
    remember (state_before_event r) as st. destruct st as [wp rp ups downs mem bufs].   
    desc. red in RFwr. desc.
    vauto.
Qed.

Lemma ppoFpga_not_cpu: (ppoFpga G ∩ (is_cpu × is_cpu)) ≡ ∅₂.
Proof.
  split.
  { intro; ins.
    do 2 destruct H.
    - repeat destruct H0, H; unfold is_cpu, is_resp, is_rd_resp in *; repeat destruct H; destruct x; desf.
    - destruct H0 as [CPUX CPUY]; destruct H as [[[H | H] | H] | H]; simpl in H; apply seq_eqv_lr in H; destruct H as [H1 [H2 H3]]; destruct H1, H3; unfold is_cpu, is_resp, is_rd_resp, is_rd_req in *; destruct x; desf.
  }
  intro.
  vauto.
Qed.

Lemma nonw_vis e (NW: ~ is_w e) (CPU: is_cpu e): vis' e = trace_index e.
Proof.
  unfold vis'.
  destruct (excluded_middle_informative (is_cpu_wr e)).
  - exfalso. apply NW. red in i. unfold is_w. desf.
  - unfolder'. unfold is_w, is_cpu in *. desf. 
Qed.

Lemma ninit_vis_helper x y (E'x : Eninit x) (E'y : Eninit y) (VIS: vis_lt' x y):
  vis' x < vis' y.
Proof. 
  do 2 red in VIS. des; vauto.
  { exfalso. red in VIS. desc. by apply (proj1 Eninit_non_init x). }
  apply seq_eqv_lr in VIS. by desc.
Qed. 

Lemma vis_respects_ppo_cpu: (ppoCpu G) ⊆ vis_lt'. 
Proof.
  red. ins. red in H.
  destruct H as [H CPU].
  red in H.
  destruct H as [SB NWR].
  destruct (vis_lt_init_helper x y SB) as [| [E'x E'y]]; auto. 
  red. right. apply seq_eqv_lr. splits; auto.
  unfold cross_rel in NWR. apply not_and_or in NWR.
  red in SB. apply seq_eqv_lr in SB. destruct SB as [_ [SBxy _]]. 
  des.
  { destruct CPU. rewrite nonw_vis; vauto.
    pose proof (TI_LE_VIS y E'y).
    forward eapply (proj1 tb_respects_sb x y) as H_; [basic_solver| ].
    apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]].
    red in TB.
    assert (~is_rd_resp y) by (unfold is_cpu, is_rd_resp in *; desf).
    remember (H1 H2); lia. }
    cut (is_w x \/ ~is_w x).
    2: { destruct CPU. unfold is_cpu, is_w in *. destruct x; desf; destruct e; intuition. }
    destruct CPU as [CPU_X CPU_Y].
    intro H; destruct H as [Wx | NWx].
  2: { replace (vis' x) with (trace_index x).
       { pose proof (TI_LE_VIS y E'y).
         assert (~is_rd_resp y) by (unfold is_cpu, is_rd_resp in *; desf).
         forward eapply (proj1 tb_respects_sb x y) as H_; [basic_solver| ].
         apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]].
         red in TB. remember (H H0). lia. }
       rewrite nonw_vis; vauto. }
  cut (is_w y \/ is_cpu_fence y).
  2: { unfold is_w, is_cpu, is_cpu_fence in *; destruct x; desf; intuition. }
  ins.
  destruct H as [Wy | Fy].
  { forward eapply (@cpu_vis_respects_sb_w x y) as VIS. 
    { red. splits; vauto. red. apply seq_eqv_lr. splits; vauto. }
    by apply ninit_vis_helper. }
  { forward eapply (@cpu_vis_respects_sb_notr x y) as VIS. 
    { red. splits; vauto. red. apply seq_eqv_lr. splits; vauto.
     unfold is_r, is_w in *; desf. }
    by apply ninit_vis_helper. }
Qed.

Lemma vis_respects_ppoFpga_part2: (⦗is_rd_resp⦘ ⨾ sb G ⨾ ⦗minus_event (acts G) is_rd_resp⦘) ⊆ vis_lt'.
Proof.
  red. ins.
  rename H into PF.
    apply seq_eqv_lr in PF.
    destruct PF as [R [SBxy NR]].
    red in NR.
    destruct NR as [ACT_Y NR].
    red. right. apply seq_eqv_lr. 
    red in SBxy.
    apply seq_eqv_lr in SBxy.
    destruct SBxy as [ACT_X [SBxy _]].
    assert (Eninit x). { destruct ACT_X; vauto; unfolder'; desf. }
    assert (Eninit y). { destruct ACT_Y; vauto. red in SBxy. destruct x, y; unfolder'; desf. }
    splits; vauto.
    Search (vis' _).
    forward eapply (TI_LE_VIS y); vauto.
    forward eapply (r_vis x); vauto.
    { unfolder'. unfold is_r; desf. }
    ins.
    remember (proj1 tb_respects_sb) as SB_TB.
    red in SB_TB.
    forward eapply (SB_TB x y).
    { basic_solver. }
    intro TB.
    apply seq_eqv_lr in TB.
    destruct TB as [_ [[TB TID] _]].
    red in TB.
    lia.
Qed.

Lemma vislt_closed: vis_lt'⁺ ≡ vis_lt'.
Proof.
  split.
  red.
  ins.
  induction H; vauto.
  remember vis_SPO as SPO.
  red in SPO.
  destruct SPO.
  basic_solver.
  red.
  ins.
  induction H; vauto.
Qed.

Lemma fence_fpga_respects_vislt: fenceFpga G ⊆ vis_lt'.
Proof.
  unfold fenceFpga.
  unfold fenceFpga.
  red; ins.
  destruct H as[x0 [[EQX WRX] [x' [POFN [y' [SB [EQY MINUS]]]]]]].
  subst x0.
  subst y'.
    assert (vis_lt' x' y) as VIS2. {
      destruct (vis_lt_init_helper x' y SB); vauto.
      destruct H as [ENX ENY].
      red. red. right.
      apply seq_eqv_lr; splits; vauto.
      forward eapply (TI_GE_VIS x'); vauto.
      { destruct POFN as [F | F]; destruct F as [x0 [H [EQ H']]]; subst x0; unfolder'; desf. }
      destruct MINUS.
      forward eapply (TI_LE_VIS y); vauto.
      ins.
      cut (trace_index x' < trace_index y); [lia|].
      red in SB.
      apply seq_eqv_lr in SB; desf.
      remember ((proj1 tb_respects_sb)) as SB_TB.
      forward eapply (SB_TB x' y); [apply seq_eqv_lr; splits; vauto|].
      intro TB; apply seq_eqv_lr in TB; desf.
      destruct TB0.
      vauto.
    }
  destruct POFN as [F_ONE | F_ALL].
  { assert (is_fence_resp_one x') as MID_FENCE. { destruct F_ONE. destruct H. destruct H0. subst x0; vauto. }
    assert (vis_lt' x x'). {
      destruct F_ONE as [x0 [POCH [XEQ F_ONE]]].
      subst x0.
      eapply (fpga_resp_vis_respects_sb_notr x x').
      apply seq_eqv_lr.
      unfold minus_event.
      splits; vauto; unfolder'; desf.
    }
    destruct (vis_SPO).
    basic_solver.
   }   
  { assert (is_fence_resp_all x') as MID_FENCE. { destruct F_ALL. destruct H. destruct H0. subst x0; vauto. }
    assert (vis_lt' x x'). {
      eapply (fpga_all_fence_sb_respects_vis x x'); vauto.
    }
    destruct (vis_SPO).
    basic_solver.
   }   
Qed.

Lemma fence_cpu_respect_vislt: fenceCpu G ⊆ vis_lt'.
Proof.
  red; ins.
  red in H.
  destruct H as [x0 [SB [x' [[EQ FENCE] SB']]]].
  subst x0.
  cut (vis_lt' x x' /\ vis_lt' x' y).
  { destruct (vis_SPO); basic_solver. }
  splits.
  {
    destruct (vis_lt_init_helper x x' SB); vauto.
    destruct H as [ENX ENY].
    assert (~is_init x) as NINX. { intro. forward eapply (proj1 Eninit_non_init x); vauto. }
    assert (~is_init x') as NINY. { intro. forward eapply (proj1 Eninit_non_init x'); vauto. }
    cut (is_r x \/ ~is_r x); [|unfolder'; desf; intuition].
    intro H; destruct H as [R | NR].
    2: { apply (cpu_vis_respects_sb_notr x x'); red in ENX; red; splits; vauto; apply seq_eqv_lr in SB; desf; red in SB0; unfolder'; desf. }
      red. red. right.
      apply seq_eqv_lr; splits; vauto.
      forward eapply (TI_GE_VIS x); vauto.
      { unfolder'; desf. }
      forward eapply (TI_LE_VIS x'); vauto.
      { unfolder'; desf. }
      ins.
      cut (trace_index x < trace_index x'); [lia|].
      red in SB.
      apply seq_eqv_lr in SB; desf.
      remember ((proj1 tb_respects_sb)) as SB_TB.
      forward eapply (SB_TB x x'); [apply seq_eqv_lr; splits; vauto|].
      intro TB; apply seq_eqv_lr in TB; desf.
      destruct TB0.
      vauto.   
  }
    destruct (vis_lt_init_helper x' y SB'); vauto.
    destruct H as [ENX ENY].
    assert (~is_init x') as NINX. { intro. forward eapply (proj1 Eninit_non_init x'); vauto. }
    assert (~is_init y) as NINY. { intro. forward eapply (proj1 Eninit_non_init y); vauto. }
      forward eapply (sb_same_tid x' y); vauto.
      ins.
      red. red. right.
      apply seq_eqv_lr; splits; vauto.
      forward eapply (TI_GE_VIS x'); vauto.
      { unfolder'; desf. }
      forward eapply (TI_LE_VIS y); vauto.
      { unfolder'; desf. }
      ins.
      cut (trace_index x' < trace_index y); [lia|].
      red in SB.
      apply seq_eqv_lr in SB'; desf.
      remember ((proj1 tb_respects_sb)) as SB_TB.
      forward eapply (SB_TB x' y); [apply seq_eqv_lr; splits; vauto|].
      intro TB; apply seq_eqv_lr in TB; desf.
      destruct TB0.
      vauto.   
Qed.

Lemma fence_respects_vislt: fence G ⊆ vis_lt'.
Proof.
  unfold fence.
  red; ins.
  destruct H.
  - apply fence_cpu_respect_vislt; vauto.
  - apply fence_fpga_respects_vislt; vauto.
Qed.


Lemma init_or_Eninit x (ACTS: acts G x): is_init x \/ Eninit x.
Proof.
  generalize Eninit_non_init; ins.
Qed.

Lemma acyclic_vis_lt: acyclic vis_lt'.
Proof.
    cdes vis_SPO. apply trans_irr_acyclic; auto.
Qed.

Lemma poch_trans: transitive (poch G).
Proof.
  unfold poch.
  apply transitiveI.
  red; ins.
  destruct H as [x0 [[SB0 SCH0] [SB1 SCH1]]].
  split.
  - eapply sb_trans; eauto.
  - unfold same_ch, chan_opt, fpga_chan_opt in *; desf.  
Qed.

Lemma poch_acyclic: acyclic (poch G).
  unfold poch.
  arewrite (sb G ∩ same_ch ⊆ sb G).
  apply sb_acyclic.
Qed.

Lemma readpair_in_poch: readpair G ⊆ poch G.
Proof. 
  red; intros x y RP.
  assert (Eninit x /\ is_rd_req x) as H.
  { apply seq_eqv_lr in RP. desf. destruct RP, RP1. destruct H, H1; unfolder'; desf. }
  destruct H as [EN REQ].
  remember (read_req2resp x EN REQ) as y'.
  replace y with y'.
  2: { apply (readpair_unique x y' y); auto.
    subst y'.
    eapply read_req2resp_readpair. }
  unfold read_req2resp in *.
  destruct (constructive_indefinite_description); simpl in *; desf.
  unfold poch. split.
  { forward eapply (proj2 tb_respects_sb x x0); eauto.
  2: { red; desf. ins. apply seq_eqv_lr. apply seq_eqv_lr in H. unfold EG; splits; desf; right; desf. }
  apply seq_eqv_lr; splits; desf.
  split; desf.
  unfold same_tid; unfolder'; desf. }
  red in PAIR.
  unfold same_ch, lbl_chan_opt, chan_opt, fpga_chan_opt in *.
  splits; desf.
  destruct PAIR; vauto.
Qed.

Lemma writepair_in_poch: writepair G ⊆ poch G.
Proof.
  red; intros x y P.
  assert (Eninit x /\ is_wr_req x) as H.
  { apply seq_eqv_lr in P. desf. destruct P, P1. destruct H, H1; unfolder'; desf. }
  destruct H as [EN REQ].
  remember (write_req2resp x EN REQ) as y'.
  replace y with y'.
  2: { apply (writepair_unique x y' y); auto.
    subst y'.
    eapply write_req2resp_writepair. }
  unfold write_req2resp in *.
  destruct (constructive_indefinite_description); simpl in *; desf.
  unfold poch. split.
  { forward eapply (proj2 tb_respects_sb x x0); eauto.
  2: { red; desf. ins. apply seq_eqv_lr. apply seq_eqv_lr in H. unfold EG; splits; desf; right; desf. }
  apply seq_eqv_lr; splits; desf.
  split; desf.
  unfold same_tid; unfolder'; desf. }
  red in PAIR.
  unfold same_ch, lbl_chan_opt, chan_opt, fpga_chan_opt in *.
  splits; desf.
  destruct PAIR; vauto.
Qed.
  

Lemma fenceonepair_in_poch: fenceonepair G ⊆ poch G.
Proof.
  red; intros x y P.
  assert (Eninit x /\ is_fence_req_one x) as H.
  { apply seq_eqv_lr in P. desf. destruct P, P1. destruct H, H1; unfolder'; desf. }
  destruct H as [EN REQ].
  remember (fence_one_req2resp x EN REQ) as y'.
  replace y with y'.
  2: { apply (fenceonepair_unique x y' y); auto.
    subst y'.
    eapply fence_one_req2resp_fenceonepair. }
  unfold fence_one_req2resp in *.
  destruct (constructive_indefinite_description); simpl in *; desf.
  unfold poch. split.
  { forward eapply (proj2 tb_respects_sb x x0); eauto.
  2: { red; desf. ins. apply seq_eqv_lr. apply seq_eqv_lr in H. unfold EG; splits; desf; right; desf. }
  apply seq_eqv_lr; splits; desf.
  split; desf.
  unfold same_tid; unfolder'; desf. }
  red in PAIR.
  unfold same_ch, lbl_chan_opt, chan_opt, fpga_chan_opt in *.
  splits; desf.
  destruct PAIR; vauto.
Qed.

Lemma fenceallpair_in_sb: fenceallpair G ⊆ sb G.
Proof. 
  red; intros x y P.
  assert (Eninit x /\ is_fence_req_all x) as H.
  { apply seq_eqv_lr in P. desf. destruct P, P1. destruct H, H1; unfolder'; desf. }
  destruct H as [EN REQ].
  remember (fence_all_req2resp x EN REQ) as y'.
  replace y with y'.
  2: { apply (fenceallpair_unique x y' y); auto.
    subst y'.
    eapply fence_all_req2resp_fenceallpair. }
  unfold fence_all_req2resp in *.
  destruct (constructive_indefinite_description); simpl in *; desf.
  forward eapply (proj2 tb_respects_sb x x0); eauto.
  2: { red; desf. ins. apply seq_eqv_lr. apply seq_eqv_lr in H. unfold EG; splits; desf; right; desf. }
  apply seq_eqv_lr; splits; desf.
  split; desf.
  unfold same_tid; unfolder'; desf.
Qed.


Lemma readpair_in_vis_lt: readpair G ⊆ vis_lt'.
Proof.
  red.
  intros x y RP.
  assert (Eninit x /\ is_rd_req x) as H.
  { apply seq_eqv_lr in RP. desf. destruct RP, RP1. destruct H, H1; unfolder'; desf. }
  destruct H as [EN REQ].
  remember (read_req2resp x EN REQ) as y'.
  replace y with y'.
  2: { apply (readpair_unique x y' y); auto.
    subst y'.
    eapply read_req2resp_readpair. }
  unfold read_req2resp in *.
  destruct constructive_indefinite_description; simpl in *.
  desf.
Qed.

Lemma sb_in_tb e1 e2 (EN1: Eninit e1) (EN2: Eninit e2): 
  sb G e1 e2 -> trace_index e1 < trace_index e2.
Proof.
  intro sb; red in sb.
  apply seq_eqv_lr in sb.
  destruct sb as [_ [sb _]].
  forward eapply (proj1 tb_respects_sb e1 e2).
  { apply seq_eqv_lr; splits; vauto. }
  intro TB; apply seq_eqv_lr in TB.
  destruct TB as [_ [[TB _] _]].
  red in TB; auto.
Qed.

Lemma pair_in_vis_lt: (allpair G) ⊆ vis_lt'.
Proof.
  red; ins.
  red in H.
  destruct H as [[[P | P] | P] | P].
  { apply readpair_in_vis_lt; auto. }
  { forward eapply (writepair_in_poch x y) as POCH; eauto.
    apply seq_eqv_lr in P.
    destruct P as [[EGX REQ] [P [EGY RESP]]].
    assert (Eninit x) as ENX by (unfold EG in *; unfolder'; desf).
    assert (Eninit y) as ENY by (unfold EG in *; unfolder'; desf).
    destruct POCH.
    red; right; apply seq_eqv_lr; splits; vauto.
    unfold vis'.
    repeat ex_des.
    forward eapply (w2p_later_fpga (trace_index y)); eauto.
    { rewrite trace_index_simpl'; vauto; unfolder'; unfold same_ch, chan_opt, fpga_chan_opt in *; desf. }
    forward eapply (sb_in_tb x y); vauto.
    ins; lia. }
  { forward eapply (fenceonepair_in_poch x y) as POCH; eauto.
    apply seq_eqv_lr in P.
    destruct P as [[EGX REQ] [P [EGY RESP]]].
    assert (Eninit x) as ENX by (unfold EG in *; unfolder'; desf).
    assert (Eninit y) as ENY by (unfold EG in *; unfolder'; desf).
    destruct POCH.
    red; right; apply seq_eqv_lr; splits; vauto.
    unfold vis'.
    repeat ex_des.
    forward eapply (sb_in_tb x y); vauto. }
  forward eapply (fenceallpair_in_sb x y) as SB; eauto.
  apply seq_eqv_lr in P.
  destruct P as [[EGX REQ] [P [EGY RESP]]].
  assert (Eninit x) as ENX by (unfold EG in *; unfolder'; desf).
  assert (Eninit y) as ENY by (unfold EG in *; unfolder'; desf).
  red; right; apply seq_eqv_lr; splits; vauto.
  unfold vis'.
  repeat ex_des.
  forward eapply (sb_in_tb x y); vauto.
Qed. 

Lemma poch_in_sb: poch G ⊆ sb G.
Proof.
  unfold poch.
  basic_solver.
Qed.

Lemma poch_fpga x y: poch G x y -> is_fpga x /\ is_fpga y.
Proof.
  ins.
  red in H.
  red in H;
  desf.
  red in H0.
  unfold chan_opt, fpga_chan_opt, is_fpga in *.
  desf.
Qed.

Lemma upstream_writeread_lemma w r
  (DOM_W: NOmega.lt_nat_l w (trace_length tr))
  (DOM_R: NOmega.lt_nat_l r (trace_length tr))
  (W: fpga_write' (trace_labels w))
  (RUPS: fpga_read_ups' (trace_labels r))
  (SAME_CH: lbl_chan_opt (trace_labels w) = lbl_chan_opt (trace_labels r))
  (ORDER: w < r):
  write2prop w < read_ups2mem_read r.
Proof.
  rewrite w2p_in_anyups2prop; vauto.
  rewrite read_ups2mem_read_in_anyups2prop; vauto.
  assert (fpga_up_prop (trace_labels w)) by (unfolder'; desf; intuition).
  assert (fpga_up_prop (trace_labels r)) by (unfolder'; desf; intuition).
  unfold any_ups2prop in *.
  do 2 ex_des.
  do 2 destruct constructive_indefinite_description.
  simpl.
  desf.
  assert (same_chan (trace_labels w) = same_chan (trace_labels r)) as CH.
  { unfold same_chan. rewrite SAME_CH. same_chan_prover. }
  rewrite CH in *.
  forward eapply (count_upto_more_strict w r (fpga_up_prop ∩₁ same_chan (trace_labels r))).
  { lia. }
  { rewrite <- CH. split; vauto. unfold same_chan; split; auto. unfold lbl_chan_opt; desf. }
  ins.
  cut (x < x0 \/ x0 <= x); [|lia].
  intro H'; destruct H' as [GOAL | BAD]; vauto.
  forward eapply (count_upto_more x0 x (fpga_any_mem_prop ∩₁ same_chan (trace_labels r))); [lia|].
  ins. lia.
Qed. 

Lemma read_ups_position req resp (EN1: Eninit req) (EN2: Eninit resp)
  (PAIR: req_resp_pair req resp)
  (REQ: is_rd_req req)
  (RESP: is_rd_resp resp) :
  exists ups_ind,
  ⟪RUPS: (fpga_read_ups' (trace_labels ups_ind))⟫ /\
  ⟪AFTER_REQ: ups_ind > (trace_index req)⟫ /\
  ⟪BEFORE_PROP: ups_ind < (read2mem_read (trace_index resp))⟫ /\
  ⟪SAME_CHAN: lbl_chan_opt (trace_labels ups_ind) = lbl_chan_opt (EventLab req)⟫ /\
  ⟪MEMREAD_WF: read_ups2mem_read ups_ind = read2mem_read (trace_index resp)⟫.
Proof.
  forward eapply (read_buffer_prop_lem (trace_index req)).
  { rewrite trace_index_simpl'; vauto. }
  ins; desf.
  exists p.
  destruct UPS_PROP as [UPS_PROP CHAN].
  split; [vauto|].
  split; [vauto|].
  assert (exists chR, lbl_chan_opt (trace_labels p) = Some chR) as [chR LBLC]. { unfold lbl_chan_opt; desf. exists c0; auto. }
  forward eapply (ups2mr_fpgar p); vauto.
  ins; desf.
  fold (trace_labels (read_ups2mem_read p)) in *.
  destruct H as [MEM_READ CHAN'].
  forward eapply (read_ups2mem_read_preserves_info p); vauto.
  ins.
  destruct H as [SAME_META' _].
  remember (read_ups2mem_read p) as mr.
  assert (exists chR, lbl_chan_opt (trace_labels mr) = Some chR) as [chMR LBLC']. { unfold lbl_chan_opt; desf. exists c; auto. }
  forward eapply (mr2r_fpgar mr chMR); auto.
  intro H.
  destruct H as [RESP' CHAN''].
  fold (trace_labels (mem_read2read mr)) in *.
  remember (mem_read2read mr) as resp.
  forward eapply (mr2r_preserves_info mr); auto.
  { unfold read_ups2mem_read in *. ex_des. destruct constructive_indefinite_description. ins. desf. }
  ins.
  assert (resp = trace_index (FpgaEvent (Fpga_read_resp c0 x0 v) index0 m0)) as RESP_EQUAL.
  { apply read_meta_unique; vauto.
    { unfold read_ups2mem_read, mem_read2read. 
      do 2 ex_des. do 2 (destruct constructive_indefinite_description).
      simpl in *; desf. }
    { destruct (classic (NOmega.lt_nat_l (trace_index (FpgaEvent (Fpga_read_resp c0 x0 v) index0 m0)) (trace_length tr))); auto.
      exfalso. apply ge_default in H0. rewrite trace_index_simpl' in H0; vauto; desf. }
    { rewrite trace_index_simpl'; vauto. }
    rewrite trace_index_simpl'; vauto.
    rewrite trace_index_simpl' in SAME_META; vauto.
    destruct PAIR; subst m0.
    simpl in *.
    destruct H as [MEQ _].
    lia. }
  rewrite RESP_EQUAL in *; clear RESP_EQUAL.
  destruct PAIR as [CP_EQ MP_EQ].
  subst m0.
  splits.
  { cut (read2mem_read (trace_index (FpgaEvent (Fpga_read_resp c0 x0 v) index0 m)) = mr).
    { ins. rewrite H0. 
      rewrite Heqmr.
      apply r_up2mem_later_fpga; vauto. }
    rewrite Heqresp.
    apply mem2read2mem; vauto. }
  2: { 
    rewrite Heqresp.
    rewrite mem2read2mem; vauto.
   }
  subst c0.
  unfold in_chan, lbl_chan_opt in *. desf.
  rewrite trace_index_simpl' in Heq0; vauto.
Qed.

Lemma write_poch_readpair_in_vislt w req resp
  (EN_W: Eninit w)
  (EN_REQ: Eninit req)
  (EN_RESP: Eninit resp)
  (W: is_wr_resp w)
  (RD_REQ: is_rd_req req)
  (RD_RESP: is_rd_resp resp)
  (PAIR: req_resp_pair req resp)
  (POCH: poch G w req):
vis' w < vis' resp.
Proof.
  unfold vis'.
  do 5 ex_des.
  forward eapply (read_ups_position req resp); vauto.
  ins. desc.
  rewrite <- MEMREAD_WF.
  forward eapply (upstream_writeread_lemma (trace_index w) ups_ind); vauto.
  { destruct (classic (NOmega.lt_nat_l (trace_index w) (trace_length tr))); auto.
    exfalso. apply ge_default in H. rewrite trace_index_simpl' in H; vauto; unfolder'; desf. }
  assert (NOmega.lt_nat_l (trace_index resp) (trace_length tr)).
  { destruct (classic (NOmega.lt_nat_l (trace_index resp) (trace_length tr))); auto.
    exfalso. apply ge_default in H. rewrite trace_index_simpl' in H; auto; unfolder'; desf. }
  { eapply NOmega.lt_lt_nat; eauto. 
    forward eapply (rd_resp_after_memread resp); vauto. ins.
    eapply NOmega.lt_lt_nat; eauto. }
  { rewrite trace_index_simpl'; auto. }
  { rewrite trace_index_simpl'; auto.
    red in PAIR.
    rewrite SAME_CHAN in *.
    destruct POCH as [_ CH'].
    unfold same_ch, chan_opt, fpga_chan_opt, lbl_chan_opt in *; desf. }
  assert (sb G w req) by (eapply poch_in_sb; eauto).
  red in H.
  forward eapply (proj1 tb_respects_sb w req).
  { apply seq_eqv_lr. apply seq_eqv_lr in H. splits; desf. }
  intro TB; apply seq_eqv_lr in TB.
  destruct TB as [_ [[TB _] _]].
  red in TB.
  lia.
Qed.


Lemma ppo_fpga_readpair_in_vis_lt: (⦗is_resp⦘ ⨾ poch G ⨾ ⦗minus_event (acts G) is_rd_resp⦘) ⨾ (readpair G) ⊆ vis_lt'.
Proof.
  red; ins.
  destruct H as [x0 [TO_REQ PAIR]].
  assert ((poch G) x0 y) as POCH'. { apply readpair_in_poch. do 2 red; vauto. }
  apply seq_eqv_lr in TO_REQ.
  destruct TO_REQ as [RSX [POCH NRX0]].
  assert ((poch G) x y) as POCH_MAIN. { apply (poch_trans x x0 y POCH POCH'). }
  apply seq_eqv_lr in PAIR.
  destruct PAIR as [[EGX0 RD_REQ] [PAIR [EGY RD_RESP]]].
  cut (is_wr_resp x \/ ~is_wr_resp x); [|tauto].
  intro H.
  destruct H as [WRX | NWRX].
  2: {
     destruct (vis_lt_init_helper x y); vauto.
     { apply poch_in_sb; vauto. }
     destruct H as [ENX ENY].
     eapply (proj2 vis_SPO x x0 y).
     { unfold vis_lt'; right.
       assert (Eninit x0) as ENX0 by (destruct (init_or_Eninit x0); eauto; unfolder'; desf).
       apply seq_eqv_lr; splits; vauto.
       forward eapply (TI_GE_VIS x); vauto.
       { unfolder'; desf. }
       forward eapply (TI_LE_VIS x0); vauto.
       { unfolder'; desf. }
       ins.
       apply poch_in_sb in POCH.
       red in POCH.
       forward eapply (proj1 tb_respects_sb x x0) as H'.
        { apply seq_eqv_lr; apply seq_eqv_lr in POCH; desf. }
       apply seq_eqv_lr in H'.
       destruct H' as [_ [[TB _] A]].
       red in TB.
       lia.
      }
      apply readpair_in_vis_lt.
      apply seq_eqv_lr; splits; vauto.
  }
  destruct (vis_lt_init_helper x y); vauto.
  { eapply poch_in_sb; eauto. }
  red; right. apply seq_eqv_lr; destruct H; splits; vauto.
  eapply write_poch_readpair_in_vislt with (w := x) (req := x0) (resp := y); eauto.
  unfold EG in *. destruct EGX0; auto. unfolder'; desf.
Qed.

Lemma ppo_fpga_pair_in_vis_lt: (⦗is_resp⦘ ⨾ poch G ⨾ ⦗minus_event (acts G) is_rd_resp⦘) ⨾ (allpair G) ⊆ vis_lt'.
Proof.
  red; ins.
  destruct H as [x0 [TO_REQ PAIR]].
  apply seq_eqv_lr in TO_REQ.
  destruct TO_REQ as [RSX [POCH NRX0]].
  destruct (poch_fpga x x0 POCH) as [FPGA_X _].
  destruct PAIR as [[[RP | WP] | FOP] | FAP].
  4: { apply fpga_all_fence_sb_respects_vis.
    apply seq_eqv_r.
    splits.
    { apply poch_in_sb in POCH. 
      apply fenceallpair_in_sb in FAP.
      remember (@sb_trans G) as T.
      red in T.
      exact (T x x0 y POCH FAP). }
    do 2 red in FAP.
    apply seq_eqv_lr in FAP.
    destruct FAP as [_ [_ [_ RES]]]; auto. }
  2: { apply fpga_resp_vis_respects_sb_notr.
    apply seq_eqv_lr.
    splits; desf.
    2: { do 2 red in WP.
       apply seq_eqv_lr in WP.
       destruct WP as [[EGX0 REQ_X0] [RRPAIR [EGY RSP_Y]]].
       red. unfolder'; desf; intuition. }
    apply writepair_in_poch in WP.
    apply (poch_trans x x0 y POCH WP). }
  2: { apply fpga_resp_vis_respects_sb_notr.
    apply seq_eqv_lr.
    splits; desf.
    2: { do 2 red in FOP.
       apply seq_eqv_lr in FOP.
       destruct FOP as [[EGX0 REQ_X0] [RRPAIR [EGY RSP_Y]]].
       red. unfolder'; desf; intuition. }
    apply fenceonepair_in_poch in FOP.
    apply (poch_trans x x0 y POCH FOP). }
  apply ppo_fpga_readpair_in_vis_lt.
  red; ins.
  exists x0; splits; vauto.
  basic_solver.
Qed.
  

Lemma propagation': acyclic (ppo G ∪ fence G ∪ rfe G ∪ fre G ∪ co G).
Proof.
  set (r := ⦗is_resp⦘ ⨾ poch G ⨾ ⦗minus_event (acts G) is_rd_resp⦘).
  apply acyclic_mori with (x := <| set_compl (is_req ∩₁ (acts G)) |> ;; vis_lt' ∪ allpair G ∪ r).
  { red. 
    apply inclusion_union_l.
    2: { left. left.
      apply seq_eqv_l.
      splits.
      2: apply co_implies_vis_lt; vauto.
      apply seq_eqv_lr in H.
      destruct H as [[_ W] _].
      apply set_compl_inter; left.
      red; unfold is_w, is_req in *; desf. }
    apply inclusion_union_l.
    2: { arewrite (fre G ⊆ fr G).
      left. left.
      apply seq_eqv_l.
      splits.
      2: apply fr_implies_vis_lt; vauto.
      remember (wf_frD WFG).
      apply s in H.
      apply seq_eqv_lr in H.
      apply set_compl_inter; left.
      red; unfold is_r, is_req in *; desf. }
    apply inclusion_union_l.
    2: { left. left.
      apply seq_eqv_l.
      splits.
      2: apply rfe_implies_vis_lt; vauto.
      remember (wf_rfeD WFG).
      apply s in H.
      apply seq_eqv_lr in H.
      apply set_compl_inter; left.
      red; unfold is_w, is_req in *; desf. }
    apply inclusion_union_l.
    2: { 
      apply inclusion_union_l.
      { left. left.
        apply seq_eqv_l.
        splits.
        2: apply fence_cpu_respect_vislt; vauto.
        red in H.
        destruct H as [x' [SB P]].
        assert (acts G x) as ACT by (apply seq_eqv_lr in SB; desf).
        destruct (init_or_Eninit x ACT).
        { apply set_compl_inter; left. unfolder'; desf. }
        apply seq_eqv_l in P; destruct P as [FN _].
        forward eapply (sb_same_tid x x' SB) as TID; vauto.
        apply set_compl_inter; left.
        unfolder'; desf. } 
      left. left.
      apply seq_eqv_l.
      splits.
      2: apply fence_fpga_respects_vislt; vauto.
      apply seq_eqv_l in H.
      apply set_compl_inter; left.
      unfolder'; desf. } 
    apply inclusion_union_l.
    { left. left.
      apply seq_eqv_l.
      splits.
      2: apply vis_respects_ppo_cpu; vauto.
      destruct H as [_ [CPU _]].
      apply set_compl_inter; left.
      unfolder'; unfold is_cpu in *; desf. }
    apply inclusion_union_l.
    2: { left. right. vauto. }
    apply inclusion_union_l.
    { ins. }
    left. left.
    apply seq_eqv_l.
    splits.
    2: apply vis_respects_ppoFpga_part2; vauto.
    apply seq_eqv_lr in H.
    apply set_compl_inter; left.
    unfolder'; unfold is_cpu in *; desf. }
  apply acyclic_union1.
  { arewrite (<| set_compl (is_req ∩₁ (acts G)) |> ;; vis_lt' ⊆ vis_lt').
    arewrite (allpair G ⊆ vis_lt').
    { exact pair_in_vis_lt. }
    rewrite unionK.
    exact acyclic_vis_lt. }
  { arewrite (r ⊆ poch G); [|apply poch_acyclic].
    Search eqv_rel inclusion.
    red; ins.
    apply seq_eqv_lr in H.
    desf. }
  rewrite ct_of_trans with (r := r).
  2: { red; ins.
    apply seq_eqv_lr in H, H0.
    apply seq_eqv_lr.
    splits; desf.
    forward eapply (poch_trans); ins; basic_solver.
  }
  apply acyclic_seqC.
  arewrite (r ⊆ r ;; <|(is_req ∩₁ (acts G))|> ∪ r ;; <| set_compl (is_req ∩₁ (acts G)) |>).
  { clear. unfolder. ins. desf. tauto. }
  arewrite (r ;; <| set_compl (is_req ∩₁ (acts G)) |> ⊆ vis_lt').
  {  unfold r.
    do 2 (rewrite seqA).
    rewrite <- AuxRel.id_inter.
    red; ins.
    eapply fpga_resp_vis_respects_sb_notr.
    apply seq_eqv_lr in H.
    apply seq_eqv_lr.
    desf.
    red in H1; desf.
    red in H1; desf.
    splits; desf.
    { unfolder'. unfold is_fpga; desf. }
    apply set_compl_inter in H2.
    destruct H2 as [NREQ | NEG]; [|vauto].
    destruct (poch_fpga x y H0). red. splits; vauto. unfolder'. unfold is_fpga in *; desf.
  }
  rewrite ct_begin.
  arewrite ((r ⨾ ⦗(is_req∩₁ (acts G))⦘ ∪ vis_lt')
   ⨾ (⦗set_compl (is_req ∩₁ (acts G))⦘ ⨾ vis_lt' ∪ allpair G) ⊆ vis_lt').
  2: { arewrite (<| set_compl (is_req ∩₁ (acts G)) |> ;; vis_lt' ⊆ vis_lt'). 
       arewrite (allpair G ⊆ vis_lt'); [exact pair_in_vis_lt|].
       rewrite unionK.
       arewrite (vis_lt' ;; clos_refl_trans vis_lt' ⊆ vis_lt').
       2: exact acyclic_vis_lt.
       rewrite <- ct_begin.
       apply ct_of_trans.
       destruct (vis_SPO); vauto. }
  rewrite !seq_union_l.
  rewrite !seq_union_r.
  unionL.
  { clear. remember (is_req ∩₁ (acts G)) as k. basic_solver. }
  { arewrite ((is_req ∩₁ (acts G)) ⊆₁ minus_event (acts G) is_rd_resp). 
    2: { unfold r. rewrite <- seqA.
      rewrite seqA.
      rewrite seqA.
      rewrite seqA.
      assert (⦗is_resp⦘ ⨾ poch G ⨾ ⦗minus_event (acts G) is_rd_resp⦘ ⨾ ⦗minus_event (acts G) is_rd_resp⦘ ;; (allpair G) ≡ (⦗is_resp⦘ ⨾ poch G ⨾ ⦗minus_event (acts G) is_rd_resp⦘ ⨾ ⦗minus_event (acts G) is_rd_resp⦘) ;; (allpair G)) by basic_solver.
      rewrite H.
      rewrite seq_eqvK.
    apply ppo_fpga_pair_in_vis_lt. }
    red; ins.
    red.
  destruct H; splits; unfolder'; desf. }
  { rewrite inclusion_seq_eqv_l.
    apply rewrite_trans.
    destruct (vis_SPO); vauto. }
  arewrite (allpair G ⊆ vis_lt'); [exact pair_in_vis_lt|].
    apply rewrite_trans.
    destruct (vis_SPO); vauto.
Qed.


Lemma fpga_read_read_poch_in_vis_lt: (⦗is_rd_resp⦘ ⨾ poch G ⨾ ⦗is_rd_resp⦘ ) ⊆ vis_lt'.
Proof.
  red; ins.
  apply seq_eqv_lr in H.
  destruct H as [RX [POCH RY]].
  destruct POCH as [SB CH].
  destruct (vis_lt_init_helper x y); auto.
  destruct H as [ENX ENY].
  unfold vis_lt'.
  right.
  apply seq_eqv_lr; splits; vauto.
  unfold vis'.
  do 6 ex_des.
  unfold read2mem_read.
  destruct excluded_middle_informative as [Z | Z].
  2: { rewrite trace_index_simpl' in Z; unfolder'; desf. }
  destruct excluded_middle_informative as [Z' | Z'].
  2: { rewrite trace_index_simpl' in Z'; unfolder'; desf. }
  destruct constructive_indefinite_description; simpl in *.
  destruct constructive_indefinite_description; simpl in *.
  desf.
  rewrite trace_index_simpl' in *; vauto.
  assert (same_chan (EventLab x) = same_chan (EventLab y)) as CH_EQ.
  { destruct CH. unfold chan_opt. same_chan_prover; destruct x, x2, y; desf. }

  assert (count_upto (fpga_read_resp' ∩₁ same_chan (EventLab x)) (trace_index x) < count_upto (fpga_read_resp' ∩₁ same_chan (EventLab y)) (trace_index y)).
  {  forward eapply (proj1 tb_respects_sb x y) as H'; [apply seq_eqv_lr; apply seq_eqv_lr in SB; desf |].
     apply seq_eqv_lr in H'.
     destruct H' as [_ [[TB _] _]].
     red in TB.
     remember (fpga_read_resp' ∩₁ same_chan (EventLab y)) as F.
     remember (count_upto_next (trace_index x) F) as DEC.
     clear HeqDEC.
     rewrite check1 in DEC.
     2: { rewrite trace_index_simpl'; desf. rewrite <- CH_EQ; split; unfold same_chan, lbl_chan_opt; desf. }
     rewrite <- CH_EQ in *.
     forward eapply (count_upto_more (S (trace_index x)) (trace_index y) F); [lia|].
     ins.
     subst F.
     lia. }
    rewrite CH_EQ in *.

  rewrite RS_MR_CORR0 in H.
  rewrite RS_MR_CORR in H.
  cut (x0 < x1 \/ x1 <= x0); [|lia].
  intro H0; destruct H0 as [l | GEQ]; [auto|].
  forward eapply (count_upto_more x1 x0 (fpga_mem_read' ∩₁ same_chan (EventLab y))); vauto.
  ins. lia.
Qed. 
  

Lemma observe_same_channel': irreflexive (fre G ⨾ rfe G ⨾ poch G).
arewrite (fre G ⊆ fr G).
arewrite (fr G ⊆ vis_lt').
{ apply fr_implies_vis_lt. }
arewrite (rfe G ;; poch G ⊆ vis_lt').
2: { destruct vis_SPO. basic_solver. }
arewrite (rfe G ⊆ ⦗is_w⦘ ⨾ rfe G ⨾ ⦗is_r⦘).
{ exact (proj1 (wf_rfeD WFG)). }
rewrite <- seqA.
rewrite <- seqA.
red; ins.
destruct H as [z [RFE POCH]].
apply seqA in RFE.
apply seq_eqv_lr in RFE.
destruct RFE as [WX [RFE RZ]].
assert (vis_lt' x z) as VIS1 by (eapply (rfe_implies_vis_lt x z); auto).
cut (vis_lt' z y).
{ ins. destruct vis_SPO. basic_solver. }
cut (is_resp y \/ ~is_resp y).
2: { destruct (poch_fpga z y POCH); unfolder'; unfold is_fpga in *; desf; intuition. }
intro OR; destruct OR as [RSP | NRSP].
{ cut ((minus_event is_resp is_rd_resp) y \/ is_rd_resp y).
  { intro OR; destruct OR as [NR | R].
    { apply (fpga_resp_vis_respects_sb_notr z y).
      destruct (poch_fpga z y POCH).
      apply seq_eqv_lr; splits; vauto. }
    apply (fpga_read_read_poch_in_vis_lt z y).
    apply seq_eqv_lr; splits; vauto. 
    destruct (poch_fpga z y POCH).
    unfold is_r, is_fpga; unfolder'; desf. }
  unfold minus_event.
  destruct (poch_fpga z y POCH).
  unfolder'; unfold is_fpga, is_r in *; desf; intuition. }
destruct (poch_fpga z y POCH) as [FZ FY].
destruct POCH as [SB CH].
destruct (vis_lt_init_helper z y); vauto.
destruct H as [ENZ ENY].
unfold vis_lt'; right.
apply seq_eqv_lr; splits; vauto.
assert (is_rd_resp z) by (unfolder'; unfold is_fpga; desf ).
forward eapply (TI_GE_VIS z); vauto.
{ unfolder'; desf. }
forward eapply (TI_LE_VIS y); vauto.
{ unfolder'; desf. }
forward eapply (proj1 tb_respects_sb z y) as H'; [apply seq_eqv_lr; apply seq_eqv_lr in SB; desf |].
apply seq_eqv_lr in H'.
destruct H' as [_ [[TB _] _]].
red in TB.
ins; lia.
Qed.


Lemma read_after_write': irreflexive (fr G ⨾ poch G ⨾ readpair G).
Proof.
  destruct (vis_SPO) as [IRR TRANS].
  red; ins.
  destruct H as [x0 [FR [x' [POCH PAIR]]]].
  desf.
  forward eapply (fr_implies_vis_lt x x0 FR).
  cut (vis_lt' x0 x).
  { ins. basic_solver. }
  assert (poch G x0 x) as POCH'.
  { forward eapply (readpair_in_poch x' x); auto.
    ins.
    eapply poch_trans; vauto. }
  destruct (vis_lt_init_helper x0 x); auto.
  { eapply poch_in_sb; auto. }
  red. right. apply seq_eqv_lr.
  destruct H.
  splits; vauto.
  red in FR.
  destruct FR as [[x00 [_ CO]] _].
  apply wf_coD in CO; [|exact WFG].
  apply seq_eqv_lr in CO.
  destruct CO as [_ [_ W0]].
  assert (fpga_write' (trace_labels (trace_index x0))).
  { destruct POCH as [SB SAME_CH]. red in SAME_CH.
    rewrite trace_index_simpl'; auto.
    unfold chan_opt, fpga_chan_opt, is_w, fpga_write' in *; desf. }
  assert (is_wr_resp x0) by (rewrite trace_index_simpl' in H1; vauto).
  apply seq_eqv_lr in PAIR.
  destruct PAIR as [[EGX' RD_REQ] [PAIR [_ RD_RESP]]].
  eapply write_poch_readpair_in_vislt with (w := x0) (req := x') (resp := x); eauto.
  unfold EG in *. destruct EGX'; auto. unfolder'; desf.
Qed.


Lemma read_after_fence': irreflexive (fr G ⨾ poFnRsp G ⨾ sb G ⨾ readpair G).
Proof.
  destruct (vis_SPO) as [IRR TRANS].
  red; ins.
  destruct H as [x0 [FR [x' [POFN [x1 [SB PAIR]]]]]].
  forward eapply (fr_implies_vis_lt x x0 FR).
  cut (vis_lt' x0 x).
  { ins. basic_solver. }
  destruct FR as [[w_old [RF CO]] _].
  red in RF.
  apply (wf_coD WFG) in CO.
  apply seq_eqv_lr in CO.
  destruct CO as [W_OLD [CO WX0]].
  destruct POFN as [F_ONE | F_ALL].
  { 
    apply seq_eqv_r in F_ONE.
    destruct F_ONE as [POCH FENCE].
    cut (vis_lt' x0 x1).
    { intro. forward eapply (readpair_in_vis_lt x1 x); vauto; intro. basic_solver. }
    cut (vis_lt' x0 x').
    { intro.
      forward eapply (readpair_in_vis_lt x1 x); vauto; ins.
      cut (vis_lt' x' x1); [intro; basic_solver|].
      destruct (vis_lt_init_helper x' x1); vauto.
      destruct H1 as [ENX' ENX1].
      red; right.
      apply seq_eqv_lr; splits; vauto.
      apply seq_eqv_lr in PAIR.
      destruct PAIR as [[_ REQ_X1] _].
      unfold vis'.
      do 6 ex_des.
      apply sb_in_tb; vauto. }
    apply fpga_resp_vis_respects_sb_notr.
    red. exists x0.
    split; auto.
    { red; splits; vauto. 
      red in POCH.
        destruct POCH as [_ SCH].
        red in SCH.
        destruct SCH as [_ CH_OPT].
        unfold chan_opt in *.
        desf. }
    red. exists x'.
    split; auto.
    red; splits; vauto.
    red; splits; unfolder'; desf. }
  apply seq_eqv_r in F_ALL.
  destruct F_ALL as [SB' FENCE].
  cut (vis_lt' x0 x1).
  { intro. forward eapply (readpair_in_vis_lt x1 x); vauto; intro. basic_solver. }
  cut (vis_lt' x0 x').
  { intro.
    forward eapply (readpair_in_vis_lt x1 x); vauto; ins.
    cut (vis_lt' x' x1); [intro; basic_solver|].
    destruct (vis_lt_init_helper x' x1); vauto.
    destruct H1 as [ENX' ENX1].
    red; right.
    apply seq_eqv_lr; splits; vauto.
    apply seq_eqv_lr in PAIR.
    destruct PAIR as [[_ REQ_X1] _].
    unfold vis'.
    do 6 ex_des.
    apply sb_in_tb; vauto. }
  apply fpga_all_fence_sb_respects_vis.
  red. exists x'.
  split; auto.
  red; splits; vauto.
Qed.


Lemma in_app_mid [A: Type] (head tail: list A) e e'
  (IN: In e (head ++ tail)):
  In e (head ++ e' :: tail).
Proof.
  apply in_app_or in IN.
  destruct IN as [L | R].
  { apply in_app_l; auto. }
  { apply in_app_r; red; auto. }
Qed.

Definition get_wp_generating_req (wp_entry: WritePoolEntry) :=
  match wp_entry with
    | store_wp c l v => Fpga_write_req c l v
    | fence_ch_wp c => Fpga_fence_req_one c
    | fence_all_wp => Fpga_fence_req_all
  end.

Lemma write_pool_sources wp_entry meta i (DOM: NOmega.lt_nat_l i (trace_length tr))
  (IN: In (wp_entry, meta) (w_pool (states i))):
  exists j event_ind,
    ⟪BEFORE: j < i⟫ /\
    trace_nth j tr def_lbl = (EventLab (FpgaEvent (get_wp_generating_req wp_entry) event_ind meta)).
Proof.
  induction i.
  { rewrite <- TS0 in *; simpl; vauto. }
  assert (NOmega.lt_nat_l i (trace_length tr) ).
  { destruct (trace_length tr); desf; simpl in *; lia. }
  forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
  inversion TSi.
  all: try by (rewrite <- H1, <- H3 in *; simpl in *; destruct (IHi H IN) as [j [event_ind [LE EQ]]]; exists j, event_ind; vauto).
  all: destruct wp_entry.
  all: try by ( rewrite <- H1, <- H3 in *; simpl in *;
    apply in_app_or in IN;
    destruct IN as [IN | NEW]; 
      [ destruct (IHi H IN) as [j [event_ind [LE EQ]]];
        exists j, event_ind; vauto |];
    red in NEW; destruct NEW as [NEW | FALSE]; [|vauto];
    exists i, index; vauto).
  all: try by ( rewrite <- H1, <- H3 in *; simpl in *;
    destruct (IHi H) as [j [event_ind [LE EQ]]]; [rewrite WRITE_POOL; apply in_app_mid; vauto |];
    exists j, event_ind; vauto ).
  all: try by ( rewrite <- H1, <- H3 in *; simpl in *;
    destruct (IHi H) as [j [event_ind [LE EQ]]]; [rewrite WRITE_POOL; simpl; auto |];
    exists j, event_ind; vauto ).
Qed.


Lemma write_pool_nodup i (DOM: NOmega.lt_nat_l i (trace_length tr)):
  NoDup (w_pool (states i)).
Proof.
  induction i.
  { destruct TS0; simpl. auto. }
  assert (NOmega.lt_nat_l i (trace_length tr)) by (destruct (trace_length tr); simpl in *; lia).
  forward eapply (TSi i) with (d := def_lbl) as TSi; eauto. 
  remember H as DOM'; clear HeqDOM'.
  apply IHi in H.
  inversion TSi.
  all: try by (rewrite <- H1, <- H3 in *; simpl; vauto).

  { rewrite <- H1, <- H3 in *; simpl in *.
    apply (proj2 (nodup_app w_pool ((store_wp channel loc val, meta) :: nil))).
    splits; vauto.
    red; ins.
    destruct IN2 as [IN2 | FALSE]; auto.
    forward eapply (write_pool_sources (store_wp channel loc val) meta i) as SOURCE; vauto.
    { rewrite <- H1; simpl; auto. }
    desc.
    simpl in SOURCE0.
    destruct WF.
    red in PAIR_UNIQUE.
    forward eapply (PAIR_UNIQUE j i event_ind index _ _ meta BEFORE); eauto. }

  { rewrite <- H1, <- H3 in *; simpl in *.
    apply (proj2 (nodup_app w_pool ((fence_ch_wp channel, meta) :: nil))).
    splits; vauto.
    red; ins.
    destruct IN2 as [IN2 | FALSE]; auto.
    forward eapply (write_pool_sources (fence_ch_wp channel) meta i) as SOURCE; vauto.
    { rewrite <- H1; simpl; auto. }
    desc.
    simpl in SOURCE0.
    destruct WF.
    red in PAIR_UNIQUE.
    forward eapply (PAIR_UNIQUE j i event_ind index _ _ meta BEFORE); eauto. }

  { rewrite <- H1, <- H3 in *; simpl in *.
    apply (proj2 (nodup_app w_pool ((fence_all_wp, meta) :: nil))).
    splits; vauto.
    red; ins.
    destruct IN2 as [IN2 | FALSE]; auto.
    forward eapply (write_pool_sources (fence_all_wp) meta i) as SOURCE; vauto.
    { rewrite <- H1; simpl; auto. }
    desc.
    simpl in SOURCE0.
    destruct WF.
    red in PAIR_UNIQUE.
    forward eapply (PAIR_UNIQUE j i event_ind index _ _ meta BEFORE); eauto. }
  { forward eapply IHi as NODUP; vauto.
    rewrite <- H1 in NODUP.
    simpl in *.
    eapply NoDup_remove_1; eauto. }
  { forward eapply IHi as NODUP; vauto.
    rewrite <- H1 in NODUP.
    simpl in *.
    inversion NODUP; auto. }
  { forward eapply IHi as NODUP; vauto.
    rewrite <- H1 in NODUP.
    simpl in *.
    inversion NODUP; auto. }
Qed.

Lemma list_double_structure_lemma [A: Type]
(l head mid tail head2 tail2 : list A) e0 e1 e2
(NODUP : NoDup l)
(EQ1: l = head ++ e0 :: mid ++ e1 :: tail)
(EQ2: l = head2 ++ e2 :: tail2)
(ELEM_DIFF0: e0 <> e2)
(ELEM_DIFF1: e1 <> e2) :
exists head' mid' tail',
  head2 ++ tail2 = head' ++ e0 :: mid' ++ e1 :: tail'.
Proof using.
  set (f := fun x => x <> e2).
  assert (forall tl (NN : ~ In e2 tl), tl = filterP f tl) as BB.
  { ins.
    Search filterP eq.
    erewrite filterP_ext with (f := f) (f' := fun _ => True).
    2: { ins; split; ins; auto. red. intro. subst x; vauto. }
    clear -tl.
    induction tl; vauto; simpl; desf.
    rewrite <- IHtl; auto. }
  enough (head2 ++ tail2 = filterP f l) as AA.
  { rewrite EQ1 in AA.
    rewrite filterP_app in AA. ins. desf.
    rewrite filterP_app in AA. ins. desf; eauto. }
  rewrite EQ2. rewrite filterP_app. ins. desf.
  rewrite EQ2 in NODUP.
  apply NoDup_remove_2 in NODUP.
  assert (~ In e2 head2 /\ ~ In e2 tail2) as [INH2 INT2].
  { split; intros AA; apply NODUP.
    all: auto using in_app_l, in_app_r. }
  rewrite <- BB with (tl:=head2); auto.
  rewrite <- BB with (tl:=tail2); auto.
Qed.

Lemma list_single_structure_lemma [A: Type]
(l head tail head2 tail2 : list A) e0 e2
(NODUP : NoDup l)
(EQ1: l = head ++ e0 :: tail)
(EQ2: l = head2 ++ e2 :: tail2)
(ELEM_DIFF0: e0 <> e2):
exists head' tail',
  head2 ++ tail2 = head' ++ e0 :: tail'.
Proof using.
  set (f := fun x => x <> e2).
  assert (forall tl (NN : ~ In e2 tl), tl = filterP f tl) as BB.
  { ins.
    Search filterP eq.
    erewrite filterP_ext with (f := f) (f' := fun _ => True).
    2: { ins; split; ins; auto. red. intro. subst x; vauto. }
    clear -tl.
    induction tl; vauto; simpl; desf.
    rewrite <- IHtl; auto. }
  enough (head2 ++ tail2 = filterP f l) as AA.
  { rewrite EQ1 in AA.
    rewrite filterP_app in AA. ins. desf. eauto. }
  rewrite EQ2. rewrite filterP_app. ins. desf.
  rewrite EQ2 in NODUP.
  apply NoDup_remove_2 in NODUP.
  assert (~ In e2 head2 /\ ~ In e2 tail2) as [INH2 INT2].
  { split; intros AA; apply NODUP.
    all: auto using in_app_l, in_app_r. }
  rewrite <- BB with (tl:=head2); auto.
  rewrite <- BB with (tl:=tail2); auto.
Qed.

Lemma list_last_elem_lemma [A: Type] head e1 tail (l: list A) e2
  (EQ1: head ++ e1 :: tail = l ++ e2 :: nil)
  (DIFF_ELEMS: e1 <> e2):
  exists tail', 
 ⟪ALT_STRUCTURE: l = head ++ e1 :: tail'⟫.
Proof.
  Search app cons nil eq.
  exists (removelast (tail)).
  destruct tail.
  { exfalso. apply DIFF_ELEMS. vauto. 
    forward eapply app_inj_tail; eauto; ins; desf. }
  replace (head ++ e1 :: removelast (a :: tail)) with (removelast (head ++ e1 :: a :: tail)).
  2: { rewrite removelast_app; vauto. }
  rewrite EQ1.
  rewrite removelast_last.
  auto.
Qed.


Lemma write_fence_order_lemma i j ch meta_w meta_f (DOM_i: NOmega.lt_nat_l i (trace_length tr))
  (DOM_j: NOmega.lt_nat_l j (trace_length tr)) (TIMELINE: i <= j):
  let wpool_i := w_pool (states i) in
  let wpool_j := w_pool (states j) in
  forall l v head mid tail head2 tail2
    (STRUCTURE_I: wpool_i = head ++ (store_wp ch l v, meta_w) :: mid ++ (fence_ch_wp ch, meta_f) :: tail)
    (STRUCTURE_J: wpool_j = head2 ++ (store_wp ch l v, meta_w) :: tail2),
  exists head2' mid2 tail2',
    ⟪STRUCTURE_J': wpool_j = head2' ++ (store_wp ch l v, meta_w) :: mid2 ++ (fence_ch_wp ch, meta_f) :: tail2'⟫.
Proof.
  induction j.
  { replace i with 0 in * by lia. destruct TS0; ins. destruct head; desf. }
  ins.
  assert (NOmega.lt_nat_l j (trace_length tr)) as DOM'.
  { eapply (@NOmega.lt_lt_nat j (S j)); eauto. }
  assert (i = (S j) \/ i = j \/ i < j) as H by lia.
  destruct H as [LESS | [EQ | NEQ]].
  { rewrite <- LESS in *. exists head, mid, tail; vauto.  }
  { subst j.
    assert (NoDup (TSOFPGA.w_pool (states i))) as NODUP.
    { apply write_pool_nodup; vauto. }
    forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
    inversion TSi.
    all: (rewrite <- H2 in *; rewrite <- H0 in *; simpl in *).
    all: try by (exists head, mid; vauto ).
    { exists head, mid, (tail ++ (store_wp channel loc val, meta) :: nil).
      rewrite STRUCTURE_I. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }
    { exists head, mid, (tail ++ (fence_ch_wp channel, meta) :: nil).
      rewrite STRUCTURE_I. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }
    { rewrite STRUCTURE_I in *.
      exists head, mid, (tail ++ (fence_all_wp, meta) :: nil).
      rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }
    { simpl in *. rewrite WRITE_POOL in *.
      eapply list_double_structure_lemma; eauto.
      2: desf.
      intro EQ; rewrite EQ in *; clear EQ.
      forward eapply (NoDup_remove_2 head0 tail0 (store_wp channel loc val, meta)).
      { vauto. }
      intro NIN; apply NIN.
      rewrite STRUCTURE_J.
      apply in_app_r.
      simpl; left; auto.
    }
    { rewrite STRUCTURE_I in *.
      destruct head; [desf|].
      rewrite <- app_comm_cons in WRITE_POOL.
      exists head, mid, tail; desf. }
    rewrite STRUCTURE_I in *.
    destruct head; [desf|].
    rewrite <- app_comm_cons in WRITE_POOL.
    exists head, mid, tail; desf. }

    assert (NoDup (TSOFPGA.w_pool (states j))) as NODUP.
    { apply write_pool_nodup; vauto. }
    assert (NoDup (TSOFPGA.w_pool (states (S j)))) as NODUP'.
    { apply write_pool_nodup; vauto. }
    forward eapply (TSi j) with (d := def_lbl) as TSi; auto.
    inversion TSi.
    all: try by (specialize IHj with (head2 := head2) (tail2 := tail2);
      specialize_full IHj; eauto; vauto; [lia | rewrite <- STRUCTURE_J, <- H0, <- H2; vauto|];
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, t2; simpl in *; vauto).
    { destruct (classic ((store_wp channel loc val, meta) = (store_wp ch l v, meta_w))) as [EQ | NEQ'].
      { 
        rewrite <- EQ in *; clear EQ.
        rewrite <- H0, <- H2 in *; simpl in *; vauto. 
        forward eapply (NoDup_eq_simpl w_pool (store_wp channel loc val, meta) nil head2 tail2); vauto.
        ins; desf.
        forward eapply (write_pool_sources (store_wp channel loc val) meta i); vauto.
        { rewrite STRUCTURE_I. apply in_app_r. simpl; left; auto. }
        ins; desc.
        destruct WF; red in PAIR_UNIQUE.
        exfalso; enough (req_resp_pair (FpgaEvent (Fpga_write_req channel loc val) event_ind meta) (FpgaEvent (Fpga_write_req channel loc val) index meta)).
        { red in H1; desf. }
        eapply PAIR_UNIQUE with (i := j0) (j := j); eauto.
        lia. }
    
      forward eapply (list_last_elem_lemma head2 ((store_wp ch l v, meta_w)) tail2 w_pool (store_wp channel loc val, meta)).
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      { auto. }
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto. 
      { lia. }
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *.
      exists h2, m2, (t2 ++ (store_wp channel loc val, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }

     {
      forward eapply (list_last_elem_lemma head2 (store_wp ch l v, meta_w) tail2 w_pool (fence_ch_wp channel, meta)); auto.
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      { desf. }
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto.
      { lia. } 
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, (t2 ++ (fence_ch_wp channel, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }
    { forward eapply (list_last_elem_lemma head2 (store_wp ch l v, meta_w) tail2 w_pool (fence_all_wp, meta)).
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      ins; desc.
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto.
      { lia. } 
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, (t2 ++ (fence_all_wp, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }
    { assert ((store_wp channel loc val, meta) <> (store_wp ch l v, meta_w)).
      { intro EQ.
        rewrite EQ in *.
        forward eapply (NoDup_remove_2 head0 tail0 (store_wp ch l v, meta_w)); eauto.
        { rewrite <- H0 in *; simpl in *. vauto. }
        intro NIN; apply NIN.
        rewrite <- H2 in STRUCTURE_J; simpl in *; rewrite STRUCTURE_J.
        apply in_app_r; simpl; left; auto. }

      assert (In (store_wp ch l v, meta_w) head0 \/ In (store_wp ch l v, meta_w) tail0) as OR.
      { cut (In (store_wp ch l v, meta_w) (TSOFPGA.w_pool (states (S j)))).
        2: { rewrite STRUCTURE_J; apply in_app_r. simpl; left; auto. }
        intro IN; rewrite <- H2 in IN; simpl in *.
        apply in_app_or; auto. }
      destruct OR as [L | R].
      { forward eapply in_split as SPLIT; eauto.
        destruct SPLIT as [l1 [l2 SPLIT]].
        rewrite SPLIT in WRITE_POOL.
        specialize IHj with (head2 := l1) (tail2 := l2 ++ ((store_wp channel loc val, meta)) :: tail0).
        specialize_full IHj; eauto.
        { lia. }
        { rewrite <- H0; simpl in *; vauto. rewrite appA. rewrite app_comm_cons; auto. }
        desc.
        forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' head0 tail0 (store_wp ch l v, meta_w) (fence_ch_wp ch, meta_f) (store_wp channel loc val, meta)); eauto.
        { rewrite <- H0 in NODUP; simpl in *; auto. }
        { rewrite <- H0 in STRUCTURE_J'; desf. }
        { desf. }
        desf. }

      forward eapply in_split as SPLIT; eauto.
      destruct SPLIT as [l1 [l2 SPLIT]].
      rewrite SPLIT in WRITE_POOL.
      specialize IHj with (head2 := head0 ++ (store_wp channel loc val, meta) :: l1) (tail2 := l2).
      specialize_full IHj; eauto.
      { lia. }
      { rewrite <- H0; simpl in *; vauto. rewrite appA. rewrite app_comm_cons; auto. }
      desc.
      forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' head0 tail0 (store_wp ch l v, meta_w) (fence_ch_wp ch, meta_f) (store_wp channel loc val, meta)); eauto.
      { rewrite <- H0 in NODUP; simpl in *; auto. }
      { rewrite <- H0 in STRUCTURE_J'; desf. }
      { desf. }
      desf. }

    (* These goals change in the future, when fence propagation is relaxed *)
    {
      assert (In (store_wp ch l v, meta_w) w_pool').
      { rewrite <- H2 in STRUCTURE_J; simpl in *. rewrite STRUCTURE_J. apply in_app_r. simpl. left. auto. }

      forward eapply in_split as SPLIT; eauto.
      destruct SPLIT as [l1 [l2 SPLIT]].
      rewrite SPLIT in WRITE_POOL.
      specialize IHj with (head2 := (fence_ch_wp channel, meta) :: l1) (tail2 := l2).
      specialize_full IHj; eauto.
      { lia. }
      { rewrite <- H0; simpl in *; vauto. }
      desc.
      forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' (nil) w_pool' (store_wp ch l v, meta_w) (fence_ch_wp ch, meta_f) (fence_ch_wp channel, meta)); eauto.
      { rewrite <- H0 in NODUP; simpl in *; auto. }
      { rewrite <- H0 in STRUCTURE_J'; desf. }
      { desf. }
      { desf. }
      intro EQ; rewrite EQ in *.
      forward eapply (NoDup_remove_2 nil w_pool' (fence_ch_wp channel, meta)); eauto.
      { simpl. rewrite <- H0 in NODUP; simpl in *; desf. }
      intro NIN; apply NIN.
      rewrite <- H0 in STRUCTURE_J'.
      simpl in *.
      rewrite WRITE_POOL in STRUCTURE_J'.
      desf.
      rewrite <- H2 in STRUCTURE_J; simpl in *.
      destruct head2'; desf.
      rewrite <- app_comm_cons in STRUCTURE_J'.
      replace (l1 ++ (store_wp channel l v, meta_w) :: l2) with (head2' ++ (store_wp channel l v, meta_w) :: mid2 ++ (fence_ch_wp channel, meta) :: tail2') in * by desf.
      apply in_app_r.
      simpl; right.
      apply in_app_r.
      simpl; left; auto. }

    assert (In (store_wp ch l v, meta_w) w_pool').
    { rewrite <- H2 in STRUCTURE_J; simpl in *. rewrite STRUCTURE_J. apply in_app_r. simpl. left. auto. }

    forward eapply in_split as SPLIT; eauto.
    destruct SPLIT as [l1 [l2 SPLIT]].
    rewrite SPLIT in WRITE_POOL.
    specialize IHj with (head2 := (fence_all_wp, meta) :: l1) (tail2 := l2).
    specialize_full IHj; eauto.
    { lia. }
    { rewrite <- H0; simpl in *; vauto. }
    desc.
    forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' (nil) w_pool' (store_wp ch l v, meta_w) (fence_ch_wp ch, meta_f) (fence_all_wp, meta)); eauto.
    { rewrite <- H0 in NODUP; simpl in *; auto. }
    { rewrite <- H0 in STRUCTURE_J'; desf. }
    { desf. }
    { desf. }
    desf.
Qed.



Definition wp_entry_by_req req := match req with
  | FpgaEvent (Fpga_write_req ch l v) _ meta => ((store_wp ch l v), meta)
  | FpgaEvent (Fpga_fence_req_one ch) _ meta => ((fence_ch_wp ch), meta)
  | FpgaEvent (Fpga_fence_req_all) _ meta => ((fence_all_wp), meta)
  | _ => ((store_wp 0 0 0), 0)
  end.

Lemma req_in_write_buffer_until_resp req resp
  (NOT_READ: ~is_rd_req req)
  (EG1: EG req)
  (EG2: EG resp)
  (WREQ: is_req req)
  (WRESP: is_resp resp)
  (PAIR: req_resp_pair req resp):
  forall trace_pos
  (AFTER_REQ: trace_pos > trace_index req)
  (BEFORE_RESP: trace_pos <= trace_index resp),
  exists head tail, w_pool (states trace_pos) = head ++ (wp_entry_by_req req) :: tail.
Proof.
  ins.
  induction trace_pos; [lia|].
  assert (NOmega.lt_nat_l (trace_index resp) (trace_length tr)) as DOM.
  { apply Eninit_in_trace; destruct EG2; unfolder'; desf. }
  assert (trace_pos > trace_index req \/ trace_pos = trace_index req) as OR by lia.
  destruct OR as [GE | EQ].
  { forward eapply (TSi trace_pos) with (d := def_lbl) as TSi.
    { eapply NOmega.lt_lt_nat; eauto. }
    specialize_full IHtrace_pos; try lia.
    desf.
    inversion TSi.
    all: try by (exists head, tail; rewrite <- H0, <- H2 in *; simpl in *; vauto).
    { rewrite <- H0, <- H2 in *; simpl in *.
      rewrite IHtrace_pos.
      exists head, (tail ++ ((store_wp channel loc val, meta) :: nil)).
      rewrite appA; auto. }
    { rewrite <- H0, <- H2 in *; simpl in *.
      rewrite IHtrace_pos.
      exists head, (tail ++ (fence_ch_wp channel, meta) :: nil).
      rewrite appA; auto. }
    { rewrite <- H0, <- H2 in *; simpl in *.
      rewrite IHtrace_pos.
      exists head, (tail ++ (fence_all_wp, meta) :: nil).
      rewrite appA; auto. }
    2: { rewrite <- H0, <- H2 in *; simpl in *.
      rewrite IHtrace_pos in WRITE_POOL.
      destruct (classic ((fence_ch_wp channel, meta) = (wp_entry_by_req req))).
      { destruct req; desf.
        destruct e; desf.
        destruct resp; desf.
        destruct e; desf.
        red in PAIR; desc; desf.
        destruct head.
        2: { rewrite <- app_comm_cons in WRITE_POOL.
             vauto. }
        simpl in *; desf. 
        exfalso.
        enough (req_resp_pair 
          (FpgaEvent (Fpga_fence_resp_one c0) index m0)
          (FpgaEvent (Fpga_fence_resp_one c0) index1 m0)); vauto.
        destruct WF.
        red in PAIR_UNIQUE.
        eapply PAIR_UNIQUE with (i := trace_pos) (j := trace_index ((FpgaEvent (Fpga_fence_resp_one c0) index1 m0))); eauto.
        rewrite trace_index_simpl; vauto.
        destruct EG2; desf. }
      destruct head; vauto.
      { simpl in *; desf. symmetry in H5; vauto. }
      exists head, tail.
      rewrite <- app_comm_cons in WRITE_POOL.
      vauto. }

    2: { rewrite <- H0, <- H2 in *; simpl in *.
      rewrite IHtrace_pos in WRITE_POOL.
      destruct (classic ((fence_all_wp, meta) = (wp_entry_by_req req))).
      { destruct req; desf.
        destruct e; desf.
        destruct resp; desf.
        destruct e; desf.
        red in PAIR; desc; desf.
        destruct head.
        2: { rewrite <- app_comm_cons in WRITE_POOL.
             vauto. }
        simpl in *; desf. 
        exfalso.
        enough (req_resp_pair 
          (FpgaEvent (Fpga_fence_resp_all) index m0)
          (FpgaEvent (Fpga_fence_resp_all) index1 m0)); vauto.
        destruct WF.
        red in PAIR_UNIQUE.
        eapply PAIR_UNIQUE with (i := trace_pos) (j := trace_index ((FpgaEvent (Fpga_fence_resp_all) index1 m0))); eauto.
        rewrite trace_index_simpl; vauto.
        destruct EG2; desf. }
      destruct head; vauto.
      { simpl in *; desf. symmetry in H5; vauto. }
      exists head, tail.
      rewrite <- app_comm_cons in WRITE_POOL.
      vauto. }
    assert (NoDup (TSOFPGA.w_pool (states trace_pos))). { eapply write_pool_nodup; eapply NOmega.lt_lt_nat; eauto. } 
    rewrite <- H0, <- H2 in *; simpl in *.
    assert ((store_wp channel loc val, meta) <> (wp_entry_by_req req) ) as NEQ.
    { intro.
      destruct req; desf; simpl in *.
      destruct e; desf; simpl in *.
      desc; desf.
      enough (req_resp_pair (FpgaEvent (Fpga_write_resp c0 x0 v0) index m0) (FpgaEvent (Fpga_write_resp c0 x0 v0) index1 m0)); vauto.
      destruct WF.
      red in PAIR_UNIQUE.
      eapply PAIR_UNIQUE with (i := trace_pos) (j := trace_index (FpgaEvent (Fpga_write_resp c0 x0 v0) index1 m0)); eauto.
      eapply trace_index_simpl; vauto.
      destruct EG2; desf. }
      eapply list_single_structure_lemma; eauto. }
  rewrite EQ in *; clear EQ.
  forward eapply (TSi (trace_index req)) with (d := def_lbl) as TSi.
  { eapply NOmega.lt_lt_nat; eauto. }
  inversion TSi.
  all: try by (rewrite trace_index_simpl in *; destruct EG1; unfolder'; desf ).
  { exists w_pool, nil; simpl.
    rewrite trace_index_simpl in H.
    2: { destruct EG1; unfolder'; desf. }
    destruct req; desf. }
  { exists w_pool, nil; simpl.
    rewrite trace_index_simpl in H.
    2: { destruct EG1; unfolder'; desf. }
    destruct req; desf. }
  exists w_pool, nil; simpl.
  rewrite trace_index_simpl in H.
  2: { destruct EG1; unfolder'; desf. }
  destruct req; desf.
Qed.

Lemma write_in_buffer w_req w_resp ch
  (CHAN: chan_opt w_req = Some ch)
  (EG1: EG w_req)
  (EG2: EG w_resp)
  (WREQ: is_wr_req w_req)
  (WRESP: is_wr_resp w_resp)
  (PAIR: req_resp_pair w_req w_resp):
  forall trace_pos
  (AFTER_REQ: trace_pos > trace_index w_req)
  (BEFORE_RESP: trace_pos <= trace_index w_resp),
  exists head tail, w_pool (states trace_pos) = head ++ (store_wp ch (loc w_req) (valw w_req), (meta w_req)) :: tail.
Proof.
  replace (store_wp ch (loc w_req) (valw w_req), meta w_req) with (wp_entry_by_req w_req) in *.
  2: { destruct w_req; desf. destruct e; desf. simpl; unfold chan_opt, fpga_chan_opt in *; desf. }
  eapply req_in_write_buffer_until_resp; eauto.
  all: try (unfolder'; desf).
Qed.

Lemma fence_one_response': irreflexive (poch G ⨾ fenceonepair G ⨾ sb G ⨾ (writepair G)⁻¹ ).
  red; ins.
  destruct H as [x0 [POCH [x1 [FENCE [x2 [SB PAIR]]]]]].
  assert (sb G x0 x1) as SBF by (eapply fenceonepair_in_poch; eauto).
  apply seq_eqv_lr in FENCE.
  apply seq_eqv_lr in PAIR.
  destruct FENCE as [[EG0 FREQ] [PAIR01 [EG1 FRSP]]].
  destruct PAIR as [[EGX WREQ] [PAIR2 [EG2 WRSP]]].
  assert (exists ch, chan_opt x = Some ch) as [ch CHAN] by (unfolder'; desf; exists c0; desf).
  forward eapply (write_in_buffer x x2 ch) with (trace_pos := trace_index x0) as WP_STRUCTURE_1; vauto.
  { forward eapply (sb_in_tb x x0); unfold EG in *; destruct EG0, EGX; unfolder'; desf. apply poch_in_sb; auto.  }
  { assert (sb G x0 x2) by (eapply sb_trans; eauto).
    forward eapply (sb_in_tb x0 x2); unfold EG in *; destruct EG0, EG2; unfolder'; desf.
    lia. }
    
  forward eapply (write_in_buffer x x2 ch) with (trace_pos := trace_index x1) as WP_STRUCTURE_2; vauto.
  { forward eapply (sb_in_tb x x1); unfold EG in *; destruct EG1, EGX; unfolder'; desf. eapply sb_trans; eauto. eapply poch_in_sb; eauto. }
  { forward eapply (sb_in_tb x1 x2); unfold EG in *; destruct EG1, EG2; unfolder'; desf. lia. } 

  ins; desc.
  assert (Eninit x0). { destruct EG0; unfolder'; desf. }
  assert (Eninit x1) as EN1. { destruct EG1; unfolder'; desf. }
  assert (Eninit x) as ENX. { destruct EGX; unfolder'; desf. }
  forward eapply (TSi (trace_index x)) with (d := def_lbl) as TSi_wr_req.
  { apply Eninit_in_trace; vauto. }
  inversion TSi_wr_req.
  all: try by (rewrite trace_index_simpl in H2; desf).
  assert (NOmega.lt_nat_l (trace_index x1) (trace_length tr)) as DOM1.
  { eapply Eninit_in_trace; destruct EG1; unfolder'; desf. }
  assert (S (trace_index x0) <= trace_index x1).
  { forward eapply (sb_in_tb x0 x1) as LE; vauto. }
  rewrite trace_index_simpl in *; auto.
  replace channel with ch in *.
  2: { destruct POCH; unfold same_ch, chan_opt, fpga_chan_opt in *; unfolder'; desf. }
  
  assert (Eninit x1). { destruct EG1; unfolder'; desf. }
  forward eapply (SyLemmas.TSi (trace_index x1)) with (d := def_lbl) as TSi_fence.
  { apply Eninit_in_trace; vauto. }
  inversion TSi_fence.
  all: try by (rewrite trace_index_simpl in H7; desf).
  rewrite trace_index_simpl in H7; auto.
  simpl in *.
  replace channel0 with ch in *.
  2: { destruct POCH. red in PAIR2; unfold same_ch, chan_opt, fpga_chan_opt in *; unfolder'; desf; desc; auto. }

  assert (Eninit x2). { destruct EG2; unfolder'; desf. }
  forward eapply (SyLemmas.TSi (trace_index x2)) with (d := def_lbl) as TSi_write.
  { apply Eninit_in_trace; vauto. }
  inversion TSi_write.
  all: try by (rewrite trace_index_simpl in H11; desf).
  rewrite trace_index_simpl in H11; auto.
  simpl in *.
  replace channel1 with ch in *.
  2: { red in PAIR2; unfold same_ch, chan_opt, fpga_chan_opt in *; unfolder'; desf; desc; auto. }
  replace meta1 with meta in *.
  2: { red in PAIR2; unfolder'; desf. }


  forward eapply (SyLemmas.TSi (trace_index x0)) with (d := def_lbl) as TSi_fence_req.
  { apply Eninit_in_trace; vauto. }
  inversion TSi_fence_req.
  all: try by (rewrite trace_index_simpl in H14; desf).
  rewrite trace_index_simpl in H14; auto.
  simpl in *.
  replace channel2 with ch in *.
  2: { red in PAIR01; unfold same_ch, chan_opt, fpga_chan_opt in *; unfolder'; desf; desc; auto. }
  replace meta2 with meta0 in *.
  2: { red in PAIR01; unfolder'; desf. }

  forward eapply (write_fence_order_lemma (S (trace_index x0)) (trace_index x1)) with
    (head := head0) (mid := tail0) (tail := nil) (ch := ch)
    (l := loc) (v := val) (meta_w := meta) (meta_f := meta0)
    (head2 := head) (tail2 := tail).
  { 
    eapply (NOmega.le_lt_nat) with (m := trace_index x1).
    enough ((trace_index x0) < (trace_index x1)); try lia.
    eapply Eninit_in_trace; eauto. }
  { apply Eninit_in_trace; auto. }
  { vauto. }
  { rewrite <- H13, <- H15 in *; simpl in *. rewrite WP_STRUCTURE_1.
    desf; simpl.
    rewrite app_comm_cons.
    repeat rewrite <- app_assoc.
    auto. }
  { rewrite WP_STRUCTURE_2.
    simpl in *.
    vauto. }
  ins; desc.
  forward eapply (write_pool_nodup (trace_index x1)) as NODUP; vauto.
  rewrite <- H6 in STRUCTURE_J', NODUP.
  simpl in *.
  destruct head2'; desf.
  rewrite <- app_comm_cons in STRUCTURE_J'.
  replace p with (fence_ch_wp ch, meta0) in * by desf.
  rewrite STRUCTURE_J' in NODUP.
  inversion NODUP.
  apply H9.
  apply in_app_r; simpl; right; apply in_app_r; simpl; left; vauto.
Qed.

Lemma write_fence_all_order_lemma i j ch meta_w meta_f (DOM_i: NOmega.lt_nat_l i (trace_length tr))
  (DOM_j: NOmega.lt_nat_l j (trace_length tr)) (TIMELINE: i <= j):
  let wpool_i := w_pool (states i) in
  let wpool_j := w_pool (states j) in
  forall l v head mid tail head2 tail2
    (STRUCTURE_I: wpool_i = head ++ (store_wp ch l v, meta_w) :: mid ++ (fence_all_wp, meta_f) :: tail)
    (STRUCTURE_J: wpool_j = head2 ++ (store_wp ch l v, meta_w) :: tail2),
  exists head2' mid2 tail2',
    ⟪STRUCTURE_J': wpool_j = head2' ++ (store_wp ch l v, meta_w) :: mid2 ++ (fence_all_wp, meta_f) :: tail2'⟫.
Proof.
  induction j.
  { replace i with 0 in * by lia. destruct TS0; ins. destruct head; desf. }
  ins.
  assert (NOmega.lt_nat_l j (trace_length tr)) as DOM'.
  { eapply (@NOmega.lt_lt_nat j (S j)); eauto. }
  assert (i = (S j) \/ i = j \/ i < j) as H by lia.
  destruct H as [LESS | [EQ | NEQ]].
  { rewrite <- LESS in *. exists head, mid, tail; vauto.  }
  { subst j.
    assert (NoDup (TSOFPGA.w_pool (states i))) as NODUP.
    { apply write_pool_nodup; vauto. }
    forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
    inversion TSi.
    all: (rewrite <- H2 in *; rewrite <- H0 in *; simpl in *).
    all: try by (exists head, mid; vauto ).
    { exists head, mid, (tail ++ (store_wp channel loc val, meta) :: nil).
      rewrite STRUCTURE_I. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }
    { exists head, mid, (tail ++ (fence_ch_wp channel, meta) :: nil).
      rewrite STRUCTURE_I. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }
    { rewrite STRUCTURE_I in *.
      exists head, mid, (tail ++ (fence_all_wp, meta) :: nil).
      rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }
    { simpl in *. rewrite WRITE_POOL in *.
      eapply list_double_structure_lemma; eauto.
      2: desf.
      intro EQ; rewrite EQ in *; clear EQ.
      forward eapply (NoDup_remove_2 head0 tail0 (store_wp channel loc val, meta)).
      { vauto. }
      intro NIN; apply NIN.
      rewrite STRUCTURE_J.
      apply in_app_r.
      simpl; left; auto.
    }
    { rewrite STRUCTURE_I in *.
      destruct head; [desf|].
      rewrite <- app_comm_cons in WRITE_POOL.
      exists head, mid, tail; desf. }
    rewrite STRUCTURE_I in *.
    destruct head; [desf|].
    rewrite <- app_comm_cons in WRITE_POOL.
    exists head, mid, tail; desf. }

    assert (NoDup (TSOFPGA.w_pool (states j))) as NODUP.
    { apply write_pool_nodup; vauto. }
    assert (NoDup (TSOFPGA.w_pool (states (S j)))) as NODUP'.
    { apply write_pool_nodup; vauto. }
    forward eapply (TSi j) with (d := def_lbl) as TSi; auto.
    inversion TSi.
    all: try by (specialize IHj with (head2 := head2) (tail2 := tail2);
      specialize_full IHj; eauto; vauto; [lia | rewrite <- STRUCTURE_J, <- H0, <- H2; vauto|];
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, t2; simpl in *; vauto).
    { destruct (classic ((store_wp channel loc val, meta) = (store_wp ch l v, meta_w))) as [EQ | NEQ'].
      { 
        rewrite <- EQ in *; clear EQ.
        rewrite <- H0, <- H2 in *; simpl in *; vauto. 
        forward eapply (NoDup_eq_simpl w_pool (store_wp channel loc val, meta) nil head2 tail2); vauto.
        ins; desf.
        forward eapply (write_pool_sources (store_wp channel loc val) meta i); vauto.
        { rewrite STRUCTURE_I. apply in_app_r. simpl; left; auto. }
        ins; desc.
        destruct WF; red in PAIR_UNIQUE.
        exfalso; enough (req_resp_pair (FpgaEvent (Fpga_write_req channel loc val) event_ind meta) (FpgaEvent (Fpga_write_req channel loc val) index meta)).
        { red in H1; desf. }
        eapply PAIR_UNIQUE with (i := j0) (j := j); eauto.
        lia. }
    
      forward eapply (list_last_elem_lemma head2 ((store_wp ch l v, meta_w)) tail2 w_pool (store_wp channel loc val, meta)).
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      { auto. }
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto. 
      { lia. }
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, (t2 ++ (store_wp channel loc val, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }

     {
      forward eapply (list_last_elem_lemma head2 (store_wp ch l v, meta_w) tail2 w_pool (fence_ch_wp channel, meta)); auto.
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      { desf. }
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto.
      { lia. } 
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, (t2 ++ (fence_ch_wp channel, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }
    { forward eapply (list_last_elem_lemma head2 (store_wp ch l v, meta_w) tail2 w_pool (fence_all_wp, meta)).
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      ins; desc.
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto.
      { lia. } 
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, (t2 ++ (fence_all_wp, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }
    { assert ((store_wp channel loc val, meta) <> (store_wp ch l v, meta_w)).
      { intro EQ.
        rewrite EQ in *.
        forward eapply (NoDup_remove_2 head0 tail0 (store_wp ch l v, meta_w)); eauto.
        { rewrite <- H0 in *; simpl in *. vauto. }
        intro NIN; apply NIN.
        rewrite <- H2 in STRUCTURE_J; simpl in *; rewrite STRUCTURE_J.
        apply in_app_r; simpl; left; auto. }

      assert (In (store_wp ch l v, meta_w) head0 \/ In (store_wp ch l v, meta_w) tail0) as OR.
      { cut (In (store_wp ch l v, meta_w) (TSOFPGA.w_pool (states (S j)))).
        2: { rewrite STRUCTURE_J; apply in_app_r. simpl; left; auto. }
        intro IN; rewrite <- H2 in IN; simpl in *.
        apply in_app_or; auto. }
      destruct OR as [L | R].
      { forward eapply in_split as SPLIT; eauto.
        destruct SPLIT as [l1 [l2 SPLIT]].
        rewrite SPLIT in WRITE_POOL.
        specialize IHj with (head2 := l1) (tail2 := l2 ++ ((store_wp channel loc val, meta)) :: tail0).
        specialize_full IHj; eauto.
        { lia. }
        { rewrite <- H0; simpl in *; vauto. rewrite appA. rewrite app_comm_cons; auto. }
        desc.
        forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' head0 tail0 (store_wp ch l v, meta_w) (fence_all_wp, meta_f) (store_wp channel loc val, meta)); eauto.
        { rewrite <- H0 in NODUP; simpl in *; auto. }
        { rewrite <- H0 in STRUCTURE_J'; desf. }
        { desf. }
        desf. }

      forward eapply in_split as SPLIT; eauto.
      destruct SPLIT as [l1 [l2 SPLIT]].
      rewrite SPLIT in WRITE_POOL.
      specialize IHj with (head2 := head0 ++ (store_wp channel loc val, meta) :: l1) (tail2 := l2).
      specialize_full IHj; eauto.
      { lia. }
      { rewrite <- H0; simpl in *; vauto. rewrite appA. rewrite app_comm_cons; auto. }
      desc.
      forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' head0 tail0 (store_wp ch l v, meta_w) (fence_all_wp, meta_f) (store_wp channel loc val, meta)); eauto.
      { rewrite <- H0 in NODUP; simpl in *; auto. }
      { rewrite <- H0 in STRUCTURE_J'; desf. }
      { desf. }
      desf. }

    {
      assert (In (store_wp ch l v, meta_w) w_pool').
      { rewrite <- H2 in STRUCTURE_J; simpl in *. rewrite STRUCTURE_J. apply in_app_r. simpl. left. auto. }

      forward eapply in_split as SPLIT; eauto.
      destruct SPLIT as [l1 [l2 SPLIT]].
      rewrite SPLIT in WRITE_POOL.
      specialize IHj with (head2 := (fence_ch_wp channel, meta) :: l1) (tail2 := l2).
      specialize_full IHj; eauto.
      { lia. }
      { rewrite <- H0; simpl in *; vauto. }
      desc.
      forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' (nil) w_pool' (store_wp ch l v, meta_w) (fence_all_wp, meta_f) (fence_ch_wp channel, meta)); eauto.
      { rewrite <- H0 in NODUP; simpl in *; auto. }
      { rewrite <- H0 in STRUCTURE_J'; desf. }
      { desf. }
      { desf. }
      desf. }

    assert (In (store_wp ch l v, meta_w) w_pool').
    { rewrite <- H2 in STRUCTURE_J; simpl in *. rewrite STRUCTURE_J. apply in_app_r. simpl. left. auto. }

    forward eapply in_split as SPLIT; eauto.
    destruct SPLIT as [l1 [l2 SPLIT]].
    rewrite SPLIT in WRITE_POOL.
    specialize IHj with (head2 := (fence_all_wp, meta) :: l1) (tail2 := l2).
    specialize_full IHj; eauto.
    { lia. }
    { rewrite <- H0; simpl in *; vauto. }
    desc.
    forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' (nil) w_pool' (store_wp ch l v, meta_w) (fence_all_wp, meta_f) (fence_all_wp, meta)); eauto.
    { rewrite <- H0 in NODUP; simpl in *; auto. }
    { rewrite <- H0 in STRUCTURE_J'; desf. }
    { desf. }
    { desf. }
    intro EQ; rewrite EQ in *.
    forward eapply (NoDup_remove_2 nil w_pool' (fence_all_wp, meta)); eauto.
    { simpl. rewrite <- H0 in NODUP; simpl in *; desf. }
    intro NIN; apply NIN.
    rewrite <- H0 in STRUCTURE_J'.
    simpl in *.
    rewrite WRITE_POOL in STRUCTURE_J'.
    desf. 
    rewrite <- H2 in STRUCTURE_J; simpl in *.
    destruct head2'; desf.
    rewrite <- app_comm_cons in STRUCTURE_J'.
    replace (l1 ++ (store_wp ch l v, meta_w) :: l2) with (head2' ++ (store_wp ch l v, meta_w) :: mid2 ++ (fence_all_wp, meta) :: tail2') in * by desf.
    apply in_app_r.
    simpl; right.
    apply in_app_r.
    simpl; left; auto.
Qed.

Lemma fence_all_response': irreflexive (sb G ⨾ fenceallpair G ⨾ sb G ⨾ (writepair G)⁻¹ ).
  red; ins.
  destruct H as [x0 [SB' [x1 [FENCE [x2 [SB PAIR]]]]]].
  assert (sb G x0 x1) as SBF by (eapply fenceallpair_in_sb; eauto).
  apply seq_eqv_lr in FENCE.
  apply seq_eqv_lr in PAIR.
  destruct FENCE as [[EG0 FREQ] [PAIR01 [EG1 FRSP]]].
  destruct PAIR as [[EGX WREQ] [PAIR2 [EG2 WRSP]]].
  assert (exists ch, chan_opt x = Some ch) as [ch CHAN] by (unfolder'; desf; exists c0; desf).
  forward eapply (write_in_buffer x x2 ch) with (trace_pos := trace_index x0) as WP_STRUCTURE_1; vauto.
  { forward eapply (sb_in_tb x x0); unfold EG in *; destruct EG0, EGX; unfolder'; desf.  }
  { assert (sb G x0 x2) by (eapply sb_trans; eauto).
    forward eapply (sb_in_tb x0 x2); unfold EG in *; destruct EG0, EG2; unfolder'; desf.
    lia. }
    
  forward eapply (write_in_buffer x x2 ch) with (trace_pos := trace_index x1) as WP_STRUCTURE_2; vauto.
  { forward eapply (sb_in_tb x x1); unfold EG in *; destruct EG1, EGX; unfolder'; desf. eapply sb_trans; eauto. }
  { forward eapply (sb_in_tb x1 x2); unfold EG in *; destruct EG1, EG2; unfolder'; desf. lia. } 

  ins; desc.
  assert (Eninit x0). { destruct EG0; unfolder'; desf. }
  assert (Eninit x1) as EN1. { destruct EG1; unfolder'; desf. }
  assert (Eninit x) as ENX. { destruct EGX; unfolder'; desf. }
  forward eapply (TSi (trace_index x)) with (d := def_lbl) as TSi_wr_req.
  { apply Eninit_in_trace; vauto. }
  inversion TSi_wr_req.
  all: try by (rewrite trace_index_simpl in H2; desf).
  assert (NOmega.lt_nat_l (trace_index x1) (trace_length tr)) as DOM1.
  { eapply Eninit_in_trace; destruct EG1; unfolder'; desf. }
  assert (S (trace_index x0) <= trace_index x1).
  { forward eapply (sb_in_tb x0 x1) as LE; vauto. }
  rewrite trace_index_simpl in *; auto.
  replace channel with ch in *.
  2: { unfold same_ch, chan_opt, fpga_chan_opt in *; unfolder'; desf. }
  
  assert (Eninit x1). { destruct EG1; unfolder'; desf. }
  forward eapply (SyLemmas.TSi (trace_index x1)) with (d := def_lbl) as TSi_fence.
  { apply Eninit_in_trace; vauto. }
  inversion TSi_fence.
  all: try by (rewrite trace_index_simpl in H7; desf).
  rewrite trace_index_simpl in H7; auto.
  simpl in *.

  assert (Eninit x2). { destruct EG2; unfolder'; desf. }
  forward eapply (SyLemmas.TSi (trace_index x2)) with (d := def_lbl) as TSi_write.
  { apply Eninit_in_trace; vauto. }
  inversion TSi_write.
  all: try by (rewrite trace_index_simpl in H11; desf).
  rewrite trace_index_simpl in H11; auto.
  simpl in *.
  replace channel0 with ch in *.
  2: { red in PAIR2; unfold same_ch, chan_opt, fpga_chan_opt in *; unfolder'; desf; desc; auto. }
  replace meta1 with meta in *.
  2: { red in PAIR2; unfolder'; desf. }


  forward eapply (SyLemmas.TSi (trace_index x0)) with (d := def_lbl) as TSi_fence_req.
  { apply Eninit_in_trace; vauto. }
  inversion TSi_fence_req.
  all: try by (rewrite trace_index_simpl in H14; desf).
  rewrite trace_index_simpl in H14; auto.
  simpl in *.
  replace meta2 with meta0 in *.
  2: { red in PAIR01; unfolder'; desf. }

  forward eapply (write_fence_all_order_lemma (S (trace_index x0)) (trace_index x1)) with
    (head := head0) (mid := tail0) (tail := nil) (ch := ch)
    (l := loc) (v := val) (meta_w := meta) (meta_f := meta0)
    (head2 := head) (tail2 := tail).
  { 
    eapply (NOmega.le_lt_nat) with (m := trace_index x1).
    enough ((trace_index x0) < (trace_index x1)); try lia.
    eapply Eninit_in_trace; eauto. }
  { apply Eninit_in_trace; auto. }
  { vauto. }
  { rewrite <- H13, <- H15 in *; simpl in *. rewrite WP_STRUCTURE_1.
    desf; simpl.
    rewrite app_comm_cons.
    repeat rewrite <- app_assoc.
    auto. }
  { rewrite WP_STRUCTURE_2.
    simpl in *.
    vauto. }
  ins; desc.
  forward eapply (write_pool_nodup (trace_index x1)) as NODUP; vauto.
  rewrite <- H6 in STRUCTURE_J', NODUP.
  simpl in *.
  destruct head2'; desf.
  rewrite <- app_comm_cons in STRUCTURE_J'.
  replace p with (fence_all_wp, meta0) in * by desf.
  rewrite STRUCTURE_J' in NODUP.
  inversion NODUP.
  apply H9.
  apply in_app_r; simpl; right; apply in_app_r; simpl; left; vauto.
Qed.

Lemma fence_write_order_lemma i j ch meta_w meta_f (DOM_i: NOmega.lt_nat_l i (trace_length tr))
  (DOM_j: NOmega.lt_nat_l j (trace_length tr)) (TIMELINE: i <= j):
  let wpool_i := w_pool (states i) in
  let wpool_j := w_pool (states j) in
  forall l v head mid tail head2 tail2
    (STRUCTURE_I: wpool_i = head ++ (fence_ch_wp ch, meta_f) :: mid ++ (store_wp ch l v, meta_w) :: tail)
    (STRUCTURE_J: wpool_j = head2 ++ (fence_ch_wp ch, meta_f) :: tail2),
  exists head2' mid2 tail2',
    ⟪STRUCTURE_J': wpool_j = head2' ++ (fence_ch_wp ch, meta_f) :: mid2 ++ (store_wp ch l v, meta_w) :: tail2'⟫.
Proof.
  induction j.
  { replace i with 0 in * by lia. destruct TS0; ins. destruct head; desf. }
  ins.
  assert (NOmega.lt_nat_l j (trace_length tr)) as DOM'.
  { eapply (@NOmega.lt_lt_nat j (S j)); eauto. }
  assert (i = (S j) \/ i = j \/ i < j) as H by lia.
  destruct H as [LESS | [EQ | NEQ]].
  { rewrite <- LESS in *. exists head, mid, tail; vauto.  }
  { subst j.
    assert (NoDup (TSOFPGA.w_pool (states i))) as NODUP.
    { apply write_pool_nodup; vauto. }
    forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
    inversion TSi.
    all: (rewrite <- H2 in *; rewrite <- H0 in *; simpl in *).
    all: try by (exists head, mid; vauto ).
    { exists head, mid, (tail ++ (store_wp channel loc val, meta) :: nil).
      rewrite STRUCTURE_I. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }
    { exists head, mid, (tail ++ (fence_ch_wp channel, meta) :: nil).
      rewrite STRUCTURE_I. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }
    { rewrite STRUCTURE_I in *.
      exists head, mid, (tail ++ (fence_all_wp, meta) :: nil).
      rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }

    { simpl in *. rewrite WRITE_POOL in *.
      eapply list_double_structure_lemma; eauto.
      desf.
      intro EQ; rewrite <- EQ in *.
      replace channel with ch in * by desf.
      apply (NO_FENCE_ONE meta_f).
      forward eapply NoDup_eq_simpl with (l1 := head0) (l2 := (head ++ (fence_ch_wp ch, meta_f) :: mid)) (l2' := tail); eauto.
      { rewrite appA. rewrite <- app_comm_cons. vauto. }
      intro HEQ. destruct HEQ as [HEQ _]; rewrite HEQ in *.
      apply in_app_r; simpl; left; auto. }
    { cut ((fence_ch_wp channel, meta) <> (fence_ch_wp ch, meta_f)).
      { intro NEQ.
        rewrite STRUCTURE_I in *.
        destruct head.
        { simpl in *; desf. }
        replace p with (fence_ch_wp channel, meta) in *.
        2: { rewrite <- app_comm_cons in WRITE_POOL; desf. }
        exists head, mid, tail.
        rewrite <- app_comm_cons in WRITE_POOL.
        desf. }
      intro EQ.
      rewrite EQ in *.
      rewrite STRUCTURE_J in *.
      rewrite WRITE_POOL in NODUP.
      inversion NODUP; desf.
      apply H4.
      apply in_app_r; simpl; left; auto. }

      rewrite STRUCTURE_I in *.
      destruct head.
      { simpl in *; desf. }
      replace p with (fence_all_wp, meta) in *.
      2: { rewrite <- app_comm_cons in WRITE_POOL; desf. }
      exists head, mid, tail.
      rewrite <- app_comm_cons in WRITE_POOL.
      desf. }

    assert (NoDup (TSOFPGA.w_pool (states j))) as NODUP.
    { apply write_pool_nodup; vauto. }
    assert (NoDup (TSOFPGA.w_pool (states (S j)))) as NODUP'.
    { apply write_pool_nodup; vauto. }
    forward eapply (TSi j) with (d := def_lbl) as TSi; auto.
    inversion TSi.
    all: try by (specialize IHj with (head2 := head2) (tail2 := tail2);
      specialize_full IHj; eauto; vauto; [lia | rewrite <- STRUCTURE_J, <- H0, <- H2; vauto|];
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, t2; simpl in *; vauto).
    { 
      forward eapply (list_last_elem_lemma head2 (fence_ch_wp ch, meta_f) tail2 w_pool (store_wp channel loc val, meta)); auto.
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      { desf. }
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto.
      { lia. } 
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, (t2 ++ (store_wp channel loc val, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }
     {
      forward eapply (list_last_elem_lemma head2 (fence_ch_wp ch, meta_f) tail2 w_pool (fence_ch_wp channel, meta)); auto.
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      { intro EQ; rewrite EQ in *.
        forward eapply (write_pool_sources (fence_ch_wp channel) meta i); vauto.
        { rewrite STRUCTURE_I. apply in_app_r. simpl; left; auto. }
        ins; desc.
        destruct WF; red in PAIR_UNIQUE.
        exfalso; enough (req_resp_pair (FpgaEvent (Fpga_fence_req_one channel) event_ind meta) (FpgaEvent (Fpga_fence_req_one channel) index meta)).
        { red in H1; desf. }
        eapply PAIR_UNIQUE with (i := j0) (j := j); eauto.
        lia. }
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto.
      { lia. } 
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, (t2 ++ (fence_ch_wp channel, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }
    { forward eapply (list_last_elem_lemma head2 (fence_ch_wp ch, meta_f) tail2 w_pool (fence_all_wp, meta)).
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      ins; desc.
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto.
      { lia. } 
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, (t2 ++ (fence_all_wp, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }
    
    {  assert (In (fence_ch_wp ch, meta_f) head0 \/ In (fence_ch_wp ch, meta_f) tail0) as OR.
      { cut (In (fence_ch_wp ch, meta_f) (TSOFPGA.w_pool (states (S j)))).
        2: { rewrite STRUCTURE_J; apply in_app_r. simpl; left; auto. }
        intro IN; rewrite <- H2 in IN; simpl in *.
        apply in_app_or; auto. }
      destruct OR as [L | R].
      { forward eapply in_split as SPLIT; eauto.
        destruct SPLIT as [l1 [l2 SPLIT]].
        rewrite SPLIT in WRITE_POOL.
        specialize IHj with (head2 := l1) (tail2 := l2 ++ ((store_wp channel loc val, meta)) :: tail0).
        specialize_full IHj; eauto.
        { lia. }
        { rewrite <- H0; simpl in *; vauto. rewrite appA. rewrite app_comm_cons; auto. }
        desc.
        forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' head0 tail0 (fence_ch_wp ch, meta_f) (store_wp ch l v, meta_w) (store_wp channel loc val, meta)); eauto.
        { rewrite <- H0 in NODUP; simpl in *; auto. }
        { rewrite <- H0 in STRUCTURE_J'; desf. }
        { desf. }
        desf. 
        intro EQ; rewrite EQ in *.
        forward eapply (NoDup_eq_simpl head0 (store_wp channel loc val, meta) tail0 (head2' ++ (fence_ch_wp ch, meta_f) :: mid2) tail2').
        { rewrite <- H0 in NODUP; vauto. }
        { rewrite <- H0 in STRUCTURE_J'. simpl in *.
          rewrite appA.
          vauto. }
        ins; desc.
        rewrite H1 in *.
        apply (NO_FENCE_ONE meta_f).
        apply in_app_r; simpl; left; desf. }

      forward eapply in_split as SPLIT; eauto.
      destruct SPLIT as [l1 [l2 SPLIT]].
      rewrite SPLIT in WRITE_POOL.
      specialize IHj with (head2 := head0 ++ (store_wp channel loc val, meta) :: l1) (tail2 := l2).
      specialize_full IHj; eauto.
      { lia. }
      { rewrite <- H0; simpl in *; vauto. rewrite appA. rewrite app_comm_cons; auto. }
      desc.
      forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' head0 tail0 (fence_ch_wp ch, meta_f) (store_wp ch l v, meta_w) (store_wp channel loc val, meta)); eauto.
      { rewrite <- H0 in NODUP; simpl in *; auto. }
      { rewrite <- H0 in STRUCTURE_J'; desf. }
      { desf. }
      desf. 
      intro EQ; rewrite EQ in *.
      forward eapply (NoDup_eq_simpl head0 (store_wp channel loc val, meta) tail0 (head2' ++ (fence_ch_wp ch, meta_f) :: mid2) tail2').
      { rewrite <- H0 in NODUP; vauto. }
      { rewrite <- H0 in STRUCTURE_J'. simpl in *.
        rewrite appA.
        vauto. }
      ins; desc.
      rewrite H1 in *.
      apply (NO_FENCE_ONE meta_f).
      apply in_app_r; simpl; left; desf. }

    {
      assert (In (fence_ch_wp ch, meta_f) w_pool').
      { rewrite <- H2 in STRUCTURE_J; simpl in *. rewrite STRUCTURE_J. apply in_app_r. simpl. left. auto. }

      forward eapply in_split as SPLIT; eauto.
      destruct SPLIT as [l1 [l2 SPLIT]].
      rewrite SPLIT in WRITE_POOL.
      specialize IHj with (head2 := (fence_ch_wp channel, meta) :: l1) (tail2 := l2).
      specialize_full IHj; eauto.
      { lia. }
      { rewrite <- H0; simpl in *; vauto. }
      desc.
      forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' (nil) w_pool' (fence_ch_wp ch, meta_f) (store_wp ch l v, meta_w) (fence_ch_wp channel, meta)); eauto.
      { rewrite <- H0 in NODUP; simpl in *; auto. }
      { rewrite <- H0 in STRUCTURE_J'; desf. }
      { desf. }
      2: desf.
      intro EQ; rewrite EQ in *.
      forward eapply (NoDup_remove_2 nil w_pool' (fence_ch_wp channel, meta)); eauto.
      simpl. rewrite <- H0 in NODUP; simpl in *; desf. }

    assert (In (fence_ch_wp ch, meta_f) w_pool').
    { rewrite <- H2 in STRUCTURE_J; simpl in *. rewrite STRUCTURE_J. apply in_app_r. simpl. left. auto. }

    forward eapply in_split as SPLIT; eauto.
    destruct SPLIT as [l1 [l2 SPLIT]].
    rewrite SPLIT in WRITE_POOL.
    specialize IHj with (head2 := (fence_all_wp, meta) :: l1) (tail2 := l2).
    specialize_full IHj; eauto.
    { lia. }
    { rewrite <- H0; simpl in *; vauto. }
    desc.
    forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' (nil) w_pool' (fence_ch_wp ch, meta_f) (store_wp ch l v, meta_w) (fence_all_wp, meta)); eauto.
    { rewrite <- H0 in NODUP; simpl in *; auto. }
    { rewrite <- H0 in STRUCTURE_J'; desf. }
    { desf. }
    2: desf.
    intro EQ; rewrite EQ in *.
    forward eapply (NoDup_remove_2 nil w_pool' (fence_all_wp, meta)); eauto.
    simpl. rewrite <- H0 in NODUP; simpl in *; desf.
Qed.


Lemma fence_all_write_order_lemma i j ch meta_w meta_f (DOM_i: NOmega.lt_nat_l i (trace_length tr))
  (DOM_j: NOmega.lt_nat_l j (trace_length tr)) (TIMELINE: i <= j):
  let wpool_i := w_pool (states i) in
  let wpool_j := w_pool (states j) in
  forall l v head mid tail head2 tail2
    (STRUCTURE_I: wpool_i = head ++ (fence_all_wp, meta_f) :: mid ++ (store_wp ch l v, meta_w) :: tail)
    (STRUCTURE_J: wpool_j = head2 ++ (fence_all_wp, meta_f) :: tail2),
  exists head2' mid2 tail2',
    ⟪STRUCTURE_J': wpool_j = head2' ++ (fence_all_wp, meta_f) :: mid2 ++ (store_wp ch l v, meta_w) :: tail2'⟫.
Proof.
  induction j.
  { replace i with 0 in * by lia. destruct TS0; ins. destruct head; desf. }
  ins.
  assert (NOmega.lt_nat_l j (trace_length tr)) as DOM'.
  { eapply (@NOmega.lt_lt_nat j (S j)); eauto. }
  assert (i = (S j) \/ i = j \/ i < j) as H by lia.
  destruct H as [LESS | [EQ | NEQ]].
  { rewrite <- LESS in *. exists head, mid, tail; vauto.  }
  { subst j.
    assert (NoDup (TSOFPGA.w_pool (states i))) as NODUP.
    { apply write_pool_nodup; vauto. }
    forward eapply (TSi i) with (d := def_lbl) as TSi; auto.
    inversion TSi.
    all: (rewrite <- H2 in *; rewrite <- H0 in *; simpl in *).
    all: try by (exists head, mid; vauto ).
    { exists head, mid, (tail ++ (store_wp channel loc val, meta) :: nil).
      rewrite STRUCTURE_I. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }
    { exists head, mid, (tail ++ (fence_ch_wp channel, meta) :: nil).
      rewrite STRUCTURE_I. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }
    { rewrite STRUCTURE_I in *.
      exists head, mid, (tail ++ (fence_all_wp, meta) :: nil).
      rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. auto. }

    { simpl in *. rewrite WRITE_POOL in *.
      eapply list_double_structure_lemma; eauto.
      desf.
      intro EQ; rewrite <- EQ in *.
      replace channel with ch in * by desf.
      apply (NO_FENCE_ALL meta_f).
      forward eapply NoDup_eq_simpl with (l1 := head0) (l2 := (head ++ (fence_all_wp, meta_f) :: mid)) (l2' := tail); eauto.
      { rewrite appA. rewrite <- app_comm_cons. vauto. }
      intro HEQ. destruct HEQ as [HEQ _]; rewrite HEQ in *.
      apply in_app_r; simpl; left; auto. }
    2: { cut ((fence_all_wp, meta) <> (fence_all_wp, meta_f)).
      { intro NEQ.
        rewrite STRUCTURE_I in *.
        destruct head.
        { simpl in *; desf. }
        replace p with (fence_all_wp, meta) in *.
        2: { rewrite <- app_comm_cons in WRITE_POOL; desf. }
        exists head, mid, tail.
        rewrite <- app_comm_cons in WRITE_POOL.
        desf. }
      intro EQ.
      rewrite EQ in *.
      rewrite STRUCTURE_J in *.
      rewrite WRITE_POOL in NODUP.
      inversion NODUP; desf.
      apply H4.
      apply in_app_r; simpl; left; auto. }

      rewrite STRUCTURE_I in *.
      destruct head.
      { simpl in *; desf. }
      replace p with (fence_ch_wp channel, meta) in *.
      2: { rewrite <- app_comm_cons in WRITE_POOL; desf. }
      exists head, mid, tail.
      rewrite <- app_comm_cons in WRITE_POOL.
      desf. }

    assert (NoDup (TSOFPGA.w_pool (states j))) as NODUP.
    { apply write_pool_nodup; vauto. }
    assert (NoDup (TSOFPGA.w_pool (states (S j)))) as NODUP'.
    { apply write_pool_nodup; vauto. }
    forward eapply (TSi j) with (d := def_lbl) as TSi; auto.
    inversion TSi.
    all: try by (specialize IHj with (head2 := head2) (tail2 := tail2);
      specialize_full IHj; eauto; vauto; [lia | rewrite <- STRUCTURE_J, <- H0, <- H2; vauto|];
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, t2; simpl in *; vauto).
    { 
      forward eapply (list_last_elem_lemma head2 (fence_all_wp, meta_f) tail2 w_pool (store_wp channel loc val, meta)); auto.
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      { desf. }
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto.
      { lia. } 
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, (t2 ++ (store_wp channel loc val, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }
     2: {
      forward eapply (list_last_elem_lemma head2 (fence_all_wp, meta_f) tail2 w_pool (fence_all_wp, meta)); auto.
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      { intro EQ; rewrite EQ in *.
        forward eapply (write_pool_sources (fence_all_wp) meta i); vauto.
        { rewrite STRUCTURE_I. apply in_app_r. simpl; left; auto. }
        ins; desc.
        destruct WF; red in PAIR_UNIQUE.
        exfalso; enough (req_resp_pair (FpgaEvent (Fpga_fence_req_all) event_ind meta) (FpgaEvent (Fpga_fence_req_all) index meta)).
        { red in H1; desf. }
        eapply PAIR_UNIQUE with (i := j0) (j := j); eauto.
        lia. }
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto.
      { lia. } 
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, (t2 ++ (fence_all_wp, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }
    { forward eapply (list_last_elem_lemma head2 (fence_all_wp, meta_f) tail2 w_pool (fence_ch_wp channel, meta)).
      { rewrite <- H0, <- H2 in *; simpl in *. vauto. }
      ins; desc.
      ins; desc.
      specialize IHj with (head2 := head2) (tail2 := tail').
      specialize_full IHj; eauto; vauto.
      { lia. } 
      { rewrite <- H0; simpl in *; vauto. }
      destruct IHj as [h2 [m2 [t2 res]]];
      rewrite <- H0 in *;
      exists h2, m2, (t2 ++ (fence_ch_wp channel, meta) :: nil); simpl in *.
      vauto.
      rewrite res.
      repeat rewrite app_comm_cons.
      repeat rewrite appA. auto. }
    
    {  assert (In (fence_all_wp, meta_f) head0 \/ In (fence_all_wp, meta_f) tail0) as OR.
      { cut (In (fence_all_wp, meta_f) (TSOFPGA.w_pool (states (S j)))).
        2: { rewrite STRUCTURE_J; apply in_app_r. simpl; left; auto. }
        intro IN; rewrite <- H2 in IN; simpl in *.
        apply in_app_or; auto. }
      destruct OR as [L | R].
      { forward eapply in_split as SPLIT; eauto.
        destruct SPLIT as [l1 [l2 SPLIT]].
        rewrite SPLIT in WRITE_POOL.
        specialize IHj with (head2 := l1) (tail2 := l2 ++ ((store_wp channel loc val, meta)) :: tail0).
        specialize_full IHj; eauto.
        { lia. }
        { rewrite <- H0; simpl in *; vauto. rewrite appA. rewrite app_comm_cons; auto. }
        desc.
        forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' head0 tail0 (fence_all_wp, meta_f) (store_wp ch l v, meta_w) (store_wp channel loc val, meta)); eauto.
        { rewrite <- H0 in NODUP; simpl in *; auto. }
        { rewrite <- H0 in STRUCTURE_J'; desf. }
        { desf. }
        desf. 
        intro EQ; rewrite EQ in *.
        forward eapply (NoDup_eq_simpl head0 (store_wp channel loc val, meta) tail0 (head2' ++ (fence_all_wp, meta_f) :: mid2) tail2').
        { rewrite <- H0 in NODUP; vauto. }
        { rewrite <- H0 in STRUCTURE_J'. simpl in *.
          rewrite appA.
          vauto. }
        ins; desc.
        rewrite H1 in *.
        apply (NO_FENCE_ALL meta_f).
        apply in_app_r; simpl; left; desf. }

      forward eapply in_split as SPLIT; eauto.
      destruct SPLIT as [l1 [l2 SPLIT]].
      rewrite SPLIT in WRITE_POOL.
      specialize IHj with (head2 := head0 ++ (store_wp channel loc val, meta) :: l1) (tail2 := l2).
      specialize_full IHj; eauto.
      { lia. }
      { rewrite <- H0; simpl in *; vauto. rewrite appA. rewrite app_comm_cons; auto. }
      desc.
      forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' head0 tail0 (fence_all_wp, meta_f) (store_wp ch l v, meta_w) (store_wp channel loc val, meta)); eauto.
      { rewrite <- H0 in NODUP; simpl in *; auto. }
      { rewrite <- H0 in STRUCTURE_J'; desf. }
      { desf. }
      desf. 
      intro EQ; rewrite EQ in *.
      forward eapply (NoDup_eq_simpl head0 (store_wp channel loc val, meta) tail0 (head2' ++ (fence_all_wp, meta_f) :: mid2) tail2').
      { rewrite <- H0 in NODUP; vauto. }
      { rewrite <- H0 in STRUCTURE_J'. simpl in *.
        rewrite appA.
        vauto. }
      ins; desc.
      rewrite H1 in *.
      apply (NO_FENCE_ALL meta_f).
      apply in_app_r; simpl; left; desf. }

    2: {
      assert (In (fence_all_wp, meta_f) w_pool').
      { rewrite <- H2 in STRUCTURE_J; simpl in *. rewrite STRUCTURE_J. apply in_app_r. simpl. left. auto. }

      forward eapply in_split as SPLIT; eauto.
      destruct SPLIT as [l1 [l2 SPLIT]].
      rewrite SPLIT in WRITE_POOL.
      specialize IHj with (head2 := (fence_all_wp, meta) :: l1) (tail2 := l2).
      specialize_full IHj; eauto.
      { lia. }
      { rewrite <- H0; simpl in *; vauto. }
      desc.
      forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' (nil) w_pool' (fence_all_wp, meta_f) (store_wp ch l v, meta_w) (fence_all_wp, meta)); eauto.
      { rewrite <- H0 in NODUP; simpl in *; auto. }
      { rewrite <- H0 in STRUCTURE_J'; desf. }
      { desf. }
      2: desf.
      intro EQ; rewrite EQ in *.
      forward eapply (NoDup_remove_2 nil w_pool' (fence_all_wp, meta)); eauto.
      simpl. rewrite <- H0 in NODUP; simpl in *; desf. }

    assert (In (fence_all_wp, meta_f) w_pool').
    { rewrite <- H2 in STRUCTURE_J; simpl in *. rewrite STRUCTURE_J. apply in_app_r. simpl. left. auto. }

    forward eapply in_split as SPLIT; eauto.
    destruct SPLIT as [l1 [l2 SPLIT]].
    rewrite SPLIT in WRITE_POOL.
    specialize IHj with (head2 := (fence_ch_wp channel, meta) :: l1) (tail2 := l2).
    specialize_full IHj; eauto.
    { lia. }
    { rewrite <- H0; simpl in *; vauto. }
    desc.
    forward eapply (list_double_structure_lemma w_pool head2' mid2 tail2' (nil) w_pool' (fence_all_wp, meta_f) (store_wp ch l v, meta_w) (fence_ch_wp channel, meta)); eauto.
    { rewrite <- H0 in NODUP; simpl in *; auto. }
    { rewrite <- H0 in STRUCTURE_J'; desf. }
    { desf. }
    2: desf.
    intro EQ; rewrite EQ in *.
    forward eapply (NoDup_remove_2 nil w_pool' (fence_ch_wp channel, meta)); eauto.
    simpl. rewrite <- H0 in NODUP; simpl in *; desf.
Qed.

Lemma fence_one_block': irreflexive (poch G ⨾ writepair G ⨾ sb G ⨾ (fenceonepair G)⁻¹).
Proof.
  red; ins.
  destruct H as [x0 [POCH [x1 [PAIR [x2 [SB FENCE]]]]]].
  assert (sb G x0 x1) as SBW by (eapply writepair_in_poch; eauto).
  apply seq_eqv_lr in FENCE.
  apply seq_eqv_lr in PAIR.
  destruct FENCE as [[EGX FREQ] [PAIR01 [EG2 FRSP]]].
  destruct PAIR as [[EG0 WREQ] [PAIR2 [EG1 WRSP]]].
  forward eapply (req_in_write_buffer_until_resp x x2) with (trace_pos := trace_index x0); eauto.
  all: try by (unfolder'; desf).
  { forward eapply (sb_in_tb x x0); unfold EG in *; destruct EG0, EGX; unfolder'; desf. apply poch_in_sb; auto.  }
  { assert (sb G x0 x2) by (eapply sb_trans; eauto).
    forward eapply (sb_in_tb x0 x2); unfold EG in *; destruct EG0, EG2; unfolder'; desf.
    lia. } 

  forward eapply (req_in_write_buffer_until_resp x x2) with (trace_pos := trace_index x1); vauto.
  all: try by (unfolder'; desf).
  { forward eapply (sb_in_tb x x1); unfold EG in *; destruct EG1, EGX; unfolder'; desf. eapply sb_trans; eauto. eapply poch_in_sb; eauto. }
  { forward eapply (sb_in_tb x1 x2); unfold EG in *; destruct EG1, EG2; unfolder'; desf. lia. } 

  ins; desc.
  
  forward eapply (TSi (trace_index x0)) with (d := def_lbl) as TSi_write_req.
  { apply Eninit_in_trace; destruct EG0; unfolder'; desf. }
  forward eapply (TSi (trace_index x1)) with (d := def_lbl) as TSi_write_resp.
  { apply Eninit_in_trace; destruct EG1; unfolder'; desf. }
  inversion TSi_write_req.
  all: try by (rewrite trace_index_simpl in H3; unfold EG in *; destruct EG0; unfolder'; desf).
  inversion TSi_write_resp.
  all: try by (rewrite trace_index_simpl in H6; unfold EG in *; destruct EG1; unfolder'; desf).
  rewrite <- H2 in H0.
  rewrite <- H5 in H.
  simpl in *.
  rewrite trace_index_simpl in *.
  all: try by unfold EG in *; unfolder'; desf.
  destruct x.
  all: try by desf.
  destruct e.
  all: try by desf.
  replace c with channel in *.
  2: { red in POCH. destruct POCH; unfold same_ch in *; unfolder'; desf. }
  forward eapply (fence_write_order_lemma (S (trace_index x0)) (trace_index x1)) with
    (head := head) (mid := tail) (tail := nil)
    (ch := channel) (meta_f := m) (meta_w := meta) (l := loc) (v := val).
  { apply (NOmega.le_lt_nat) with (m := (trace_index x1)).  
    - enough ((trace_index x0) < (trace_index x1)); try lia. apply sb_in_tb; vauto; unfold EG in *; unfolder'; desf.
    - apply Eninit_in_trace; unfold EG in *; unfolder'; desf. }
  { apply Eninit_in_trace; unfold EG in *; unfolder'; desf. }
  { enough ((trace_index x0) < (trace_index x1)); try lia. apply sb_in_tb; vauto; unfold EG in *; unfolder'; desf. }
  { rewrite <- H4; simpl. rewrite H0. rewrite appA. rewrite <- !app_comm_cons. simpl. auto. }
  { rewrite <- H5; simpl; vauto. }
  ins; desc.
  assert (NoDup (TSOFPGA.w_pool (states (trace_index x1)))) as NODUP.
  { apply write_pool_nodup. apply Eninit_in_trace; unfold EG in *; unfolder'; desf. }
  rewrite <- H5 in *; simpl in *.
  rewrite H in *.
  forward eapply (NoDup_eq_simpl) with (a := (fence_ch_wp channel, m)); eauto.
  ins; desc.
  rewrite H1, H8 in *.
  destruct x0; desf.
  red in PAIR2; desc; desf.
  forward eapply (write_pool_nodup (trace_index (FpgaEvent (Fpga_write_resp c0 loc0 val0) index0 meta0))).
  { apply Eninit_in_trace; unfold EG in *; destruct EG1; desf. }
  intro NODUP'.
  rewrite <- H5 in NODUP'.
  simpl in NODUP'.
  forward eapply (NoDup_eq_simpl) with 
    (a := (store_wp c0 loc0 val0, meta0)) (l1 := head2' ++ (fence_ch_wp c0, m1) :: mid2) (l1' := tail2')
    (l2 := head1) (l2' := tail1); eauto.
  { rewrite appA. rewrite <- app_comm_cons. auto. }
  { rewrite appA. rewrite <- app_comm_cons. auto. }
  intro H; destruct H as [EQ _].
  rewrite <- EQ in NO_FENCE_ONE.
  apply (NO_FENCE_ONE m1).
  apply in_app_r.
  simpl; left; auto.
Qed.

Lemma fence_all_block': irreflexive (sb G ⨾ writepair G ⨾ sb G ⨾ (fenceallpair G)⁻¹).
Proof.
  red; ins.
  destruct H as [x0 [SB' [x1 [PAIR [x2 [SB FENCE]]]]]].
  assert (sb G x0 x1) as SBW by (eapply writepair_in_poch; eauto).
  apply seq_eqv_lr in FENCE.
  apply seq_eqv_lr in PAIR.
  destruct FENCE as [[EGX FREQ] [PAIR01 [EG2 FRSP]]].
  destruct PAIR as [[EG0 WREQ] [PAIR2 [EG1 WRSP]]].
  forward eapply (req_in_write_buffer_until_resp x x2) with (trace_pos := trace_index x0); eauto.
  all: try by (unfolder'; desf).
  { forward eapply (sb_in_tb x x0); unfold EG in *; destruct EG0, EGX; unfolder'; desf. }
  { assert (sb G x0 x2) by (eapply sb_trans; eauto).
    forward eapply (sb_in_tb x0 x2); unfold EG in *; destruct EG0, EG2; unfolder'; desf.
    lia. } 

  forward eapply (req_in_write_buffer_until_resp x x2) with (trace_pos := trace_index x1); vauto.
  all: try by (unfolder'; desf).
  { forward eapply (sb_in_tb x x1); unfold EG in *; destruct EG1, EGX; unfolder'; desf. eapply sb_trans; eauto. }
  { forward eapply (sb_in_tb x1 x2); unfold EG in *; destruct EG1, EG2; unfolder'; desf. lia. } 

  ins; desc.
  
  forward eapply (TSi (trace_index x0)) with (d := def_lbl) as TSi_write_req.
  { apply Eninit_in_trace; destruct EG0; unfolder'; desf. }
  forward eapply (TSi (trace_index x1)) with (d := def_lbl) as TSi_write_resp.
  { apply Eninit_in_trace; destruct EG1; unfolder'; desf. }
  inversion TSi_write_req.
  all: try by (rewrite trace_index_simpl in H3; unfold EG in *; destruct EG0; unfolder'; desf).
  inversion TSi_write_resp.
  all: try by (rewrite trace_index_simpl in H6; unfold EG in *; destruct EG1; unfolder'; desf).
  rewrite <- H2 in H0.
  rewrite <- H5 in H.
  simpl in *.
  rewrite trace_index_simpl in *.
  all: try by unfold EG in *; unfolder'; desf.
  destruct x.
  all: try by desf.
  destruct e.
  all: try by desf.
  forward eapply (fence_all_write_order_lemma (S (trace_index x0)) (trace_index x1)) with
    (head := head) (mid := tail) (tail := nil)
    (ch := channel) (meta_f := m) (meta_w := meta) (l := loc) (v := val).
  { apply (NOmega.le_lt_nat) with (m := (trace_index x1)).  
    - enough ((trace_index x0) < (trace_index x1)); try lia. apply sb_in_tb; vauto; unfold EG in *; unfolder'; desf.
    - apply Eninit_in_trace; unfold EG in *; unfolder'; desf. }
  { apply Eninit_in_trace; unfold EG in *; unfolder'; desf. }
  { enough ((trace_index x0) < (trace_index x1)); try lia. apply sb_in_tb; vauto; unfold EG in *; unfolder'; desf. }
  { rewrite <- H4; simpl. rewrite H0. rewrite appA. rewrite <- !app_comm_cons. simpl. auto. }
  { rewrite <- H5; simpl; vauto. }
  ins; desc.
  assert (NoDup (TSOFPGA.w_pool (states (trace_index x1)))) as NODUP.
  { apply write_pool_nodup. apply Eninit_in_trace; unfold EG in *; unfolder'; desf. }
  rewrite <- H5 in *; simpl in *.
  rewrite H in *.
  forward eapply (NoDup_eq_simpl) with (a := (fence_all_wp, m)); eauto.
  ins; desc.
  rewrite H1, H8 in *.
  destruct x0; desf.
  red in PAIR2; desc; desf.
  forward eapply (write_pool_nodup (trace_index (FpgaEvent (Fpga_write_resp channel0 loc0 val0) index0 meta0))).
  { apply Eninit_in_trace; unfold EG in *; destruct EG1; desf. }
  intro NODUP'.
  rewrite <- H5 in NODUP'.
  simpl in NODUP'.
  forward eapply (NoDup_eq_simpl) with 
    (a := (store_wp channel0 loc0 val0, meta0)) (l1 := head2' ++ (fence_all_wp, m1) :: mid2) (l1' := tail2')
    (l2 := head1) (l2' := tail1); eauto.
  { rewrite appA. rewrite <- app_comm_cons. auto. }
  { rewrite appA. rewrite <- app_comm_cons. auto. }
  intro H; destruct H as [EQ _].
  rewrite <- EQ in NO_FENCE_ALL.
  apply (NO_FENCE_ALL m1).
  apply in_app_r.
  simpl; left; auto.
Qed.

Lemma ppo_cpu_constraint: (ppo G ∩ (is_cpu × is_cpu)) ≡ ppoCpu G.
Proof.
  red; ins; split.
  { red; ins.
    destruct H as [PPO CPU2].
    destruct PPO; auto.
    red in H.
    destruct CPU2.
    destruct H as [[E | E] | E].
    - apply seq_eqv_lr in E; unfolder'; desf.
    - apply seq_eqv_lr in E; unfolder'; desf.
    - red in E. destruct E as [[[P | P] | P] | P].
      all: (apply seq_eqv_lr in P; desf; unfolder'; desf). }
  unfold ppo.
  red; ins.
  apply inter_union_l.
  left.
  unfold ppoCpu in *.
  apply interA.
  destruct H; split; auto.
  split; auto.
Qed.

Lemma rel_helper: rf G ∪ co G ∪ fr G ⊆ poloc G ∪ (rfe G ∪ coe G ∪ fre G).
Proof.
  rewrite fri_union_fre, (fri_in_sbloc' WFG).
  rewrite coi_union_coe, (coi_in_sbloc' WFG).
  rewrite rfi_union_rfe, (rfi_in_sbloc' WFG).
  unfold poloc, same_loc.
  repeat (apply inclusion_union_l; [| basic_solver]). basic_solver.  
Qed.

Lemma buffer_shift thread i j (LE: i <= j) (DOM: NOmega.lt_nat_l j (trace_length tr)):
  let pi := count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) i in
  let pj := count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) j in
  let buf_i := cpu_bufs (states i) thread in
  let buf_j := cpu_bufs (states j) thread in
  forall item k (ITEM: Some item = nth_error buf_i (k + (pj - pi))),
    Some item = nth_error buf_j k.
Proof.
  simpl. apply le_diff in LE. desc. subst j. induction d.
  { rewrite Nat.add_0_r, Nat.sub_diag. ins. by rewrite Nat.add_0_r in ITEM. }
  ins. replace (i + S d) with (S (i + d)) in * by lia. 
  assert (NOmega.lt_nat_l (i + d) (trace_length tr)) as DOM'.
  { destruct (trace_length tr); vauto. simpl in *. lia. }
  specialize (IHd DOM'). 
  remember (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) i) as Pi.
  remember (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) (S (i + d))) as Pcur. 
  remember (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) (i + d)) as Pprev.
  assert (Pcur = Pprev + check (is_cpu_prop ∩₁ in_cpu_thread thread) (trace_nth (i + d) tr def_lbl)) as CUR.
  { subst. by rewrite count_upto_next. }
  forward eapply (TSi (i + d)) with (d := def_lbl) as TSi; auto.  
  inversion TSi.
  all: try by (rewrite check0 in CUR;
    [|rewrite <- H; unfolder'; intuition];
    rewrite Nat.add_0_r in CUR; rewrite CUR in ITEM;
    erewrite IHd; eauto; by rewrite <- H0).
  { rewrite check0 in CUR.
    2: { rewrite <- H. unfolder'. intuition. }
    rewrite Nat.add_0_r in CUR. rewrite CUR in ITEM.
    specialize (IHd item k ITEM). 
    rewrite IHd. 
    rewrite <- H0. simpl.
    destruct (classic (thread0 = thread)).
    2: { rewrite updo; auto. }
    subst thread0. rewrite upds. rewrite nth_error_app1; auto.
    apply nth_error_Some. apply opt_val. exists item. by rewrite <- H0 in IHd. }
  { simpl. destruct (classic (thread0 = thread)).
    2: { rewrite updo; auto. 
         rewrite check0 in CUR.
         2: { rewrite <- H. unfolder'.
              intuition. desf. }
         rewrite Nat.add_0_r in CUR. rewrite CUR in ITEM.
         erewrite IHd; eauto. by rewrite <- H0. }
    subst thread0. rewrite upds.
    rewrite check1 in CUR.
    2: { rewrite <- H. unfolder'. vauto. }
    rewrite CUR in ITEM.
    specialize (IHd item (k + 1)). specialize_full IHd.
    { rewrite ITEM. f_equal.
      assert (Pi <= Pprev) as MORE. 
      { subst. apply count_upto_more. lia. }
      do 2 (rewrite Nat.add_sub_assoc; [| lia]). lia. }
    rewrite IHd, <- H0. simpl. rewrite CPU_BUF. by rewrite Nat.add_1_r. }
Qed. 

Lemma buf_between w p thread ind loc val (W2P: p = write2prop w)
      (EVENT: trace_nth w tr def_lbl = EventLab (ThreadEvent thread ind (Cpu_store loc val))):
  forall i (BETWEEN: w < i /\ i <= p),
    let bufs := cpu_bufs (states i) in
    (filter (fun loc_val : nat * Val => fst loc_val =? loc) (bufs thread)) <> nil.
Proof.
  ins.
  remember (states w) as st0. destruct st0 as [wp0 rp0 ups0 downs0 sh_mem0 bufs0].
  remember (states i) as st. destruct st as [wp rp ups downs sh_mem bufs].
  cut (exists n, nth_error (bufs thread) n = Some (loc, val)).
  { ins. desc. cut (In (loc, val) (filter (fun loc_val : nat * Val => fst loc_val =? loc) (bufs thread))).
    { ins. by destruct (filter _ _). }
    apply in_filter_iff. split.
    { eapply nth_error_In. eauto. }
    apply Nat.eqb_refl. }
  remember (states (w + 1)) as st1. destruct st1 as [wp1 rp1 ups1 downs1 sh_mem1 bufs1].
  remember (length (bufs0 thread)) as l0.
  assert (Some (loc, val) = nth_error (bufs1 thread) l0) as W_LAST.
  { forward eapply (TSi w) with (d := def_lbl) as TSi.
    { apply lt_nondefault. unfold trace_labels. unfolder'. by rewrite EVENT. }
    unfold def_lbl in TSi. unfold def_lbl in *. rewrite EVENT in TSi. inversion TSi.
    rewrite <- Heqst0 in H0. inversion H0.
    subst thread0 index loc0 val0 sh_mem2 cpu_bufs.
    rewrite NPeano.Nat.add_1_r in Heqst1. rewrite <- Heqst1 in H5. inversion H5.
    rewrite upds. rewrite nth_error_app2; [| lia].
    by rewrite Heql0, Nat.sub_diag. }

  remember (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) (w + 1)) as p1.
  remember (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) i) as pi.
  remember (count_upto (is_cpu_prop ∩₁ in_cpu_thread thread) w) as p0.
  forward eapply (@count_upto_more (w + 1) i (is_cpu_prop ∩₁ in_cpu_thread thread)) as MORE_PROPS; [lia|].
  rewrite <- Heqp1, <- Heqpi in MORE_PROPS. apply le_diff in MORE_PROPS. desc.
  apply plus_minus in MORE_PROPS. 
  assert (exists k, l0 = k + d) as [k BUF_SHIFT]. 
  { destruct (le_lt_dec d l0).
    { apply le_diff in l. desc. exists d0. lia. }
    exfalso.
    rewrite Nat.add_1_r, count_upto_next, check0, Nat.add_0_r in Heqp1.
    2: { unfold trace_labels, def_lbl. fold def_lbl. rewrite EVENT. unfolder'. intuition. }
    assert (p1 = p0) by congruence. subst p1. clear H. try rewrite <- Heqp0 in *.
    assert (pi > p0 + l0) as OVER_PROPS by lia.

    forward eapply (@buffer_size_cpu thread w) as WRITE_NTH.
    { apply NOmega.lt_le_incl. apply lt_nondefault.
      unfold trace_labels, def_lbl. fold def_lbl. by rewrite EVENT. }
    
    simpl in WRITE_NTH. rewrite <- Heqp0, <- Heqst0 in WRITE_NTH.
    simpl in WRITE_NTH. rewrite <- Heql0 in WRITE_NTH.  
    
    unfold write2prop in W2P.
    destruct (excluded_middle_informative _).
    2: { fold (trace_labels w) in *. rewrite EVENT in *. unfolder'. intuition. }
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    replace (same_thread (trace_labels w)) with (in_cpu_thread thread) in *. 
    2: { unfold trace_labels, def_lbl in *. rewrite EVENT. symmetry. apply RESTR_EQUIV. }
    rewrite W_P_CORR in WRITE_NTH. subst x.
    forward eapply (@count_upto_more i p (is_cpu_prop ∩₁ in_cpu_thread thread)) as MORE; [lia| ].
    lia. }
  rewrite BUF_SHIFT, MORE_PROPS in W_LAST.

  exists k. 
  forward eapply (@buffer_shift thread (w + 1) i) with (k := k) (item := (loc, val)); eauto. 
  { lia. }
  { eapply NOmega.le_lt_nat; eauto. 
    apply lt_nondefault.
    replace (trace_labels p) with (CpuFlush thread); [done| ]. 
    subst p.
    forward eapply (@w2p_regw (ThreadEvent thread ind (Cpu_store loc val)) thread) as W2P_PROP; try (by vauto).
    { red. rewrite <- EVENT. apply trace_nth_in. apply lt_nondefault.
      unfold trace_labels. rewrite EVENT. intuition. vauto. }
    rewrite (ti_infer w) in W2P_PROP; [| done].
    unfold trace_labels.
    generalize W2P_PROP. remember (trace_nth (write2prop w) tr def_lbl) as lbl. 
    unfolder'. destruct lbl; intuition; vauto. unfolder'; desf. }
  { by rewrite <- Heqst1, <- Heqp1, <- Heqpi. }
  by rewrite <- Heqst. 
Qed.



Lemma sb_fr_irr: irreflexive ((<|is_cpu|> ⨾ sb G ⨾ <|is_cpu|>) ⨾ fr G).
Proof.
  red. intros w [r [SBwr FRrw]].
  apply seq_eqv_lr in SBwr.
  destruct SBwr as [CPU_W [SBwr CPU_R]].
  pose proof (fr_implies_vis_lt _ _ FRrw) as VISrw. do 2 red in VISrw.
  des.
  { red in VISrw. desc. apply (wf_frD WFG), seq_eqv_lr in FRrw. desc. 
    destruct r; vauto. }
  apply seq_eqv_lr in VISrw. desc. 
  apply (wf_frD WFG), seq_eqv_lr in FRrw. destruct FRrw as [Rr [FRrw Ww]].
  rewrite r_vis_cpu in VISrw0; auto. 
  2: { unfolder'; unfold is_cpu in *; desf. }
  unfold vis' in VISrw0.
  ex_des.
  rename i into WREGw.
  assert (trace_index w < trace_index r) as TBwr.
  { forward eapply (proj1 tb_respects_sb w r) as H_. 
    { apply seq_eqv_lr. splits; auto. red in SBwr. apply seq_eqv_lr in SBwr. basic_solver. }
    apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]]. by red in TB. }
  forward eapply (reg_write_structure (EventLab w)); vauto. ins. desc. inversion H.
  assert (tid w = tid r).
  { apply sb_tid_init in SBwr. des; vauto. }
  assert (thread = exact_tid r).
  { ins. subst.  simpl in *. unfold tid, exact_tid in *. desf. }
  
  forward eapply (@buf_between (trace_index w) (write2prop (trace_index w)) thread index loc val) as IN_BUF; auto.
  { by rewrite trace_index_simpl, H1. }
  { split; eauto. lia. }  
  remember (states (trace_index r)) as st_r. destruct st_r as [mem bufs].
  simpl in IN_BUF.


  pose proof FRrw as FRrw_. 
  red in FRrw. destruct FRrw as [[w' [RFw'r COw'w]] NEQrw]. unfold transp in RFw'r.
  pose proof RFw'r as RFw'r_.
  simpl in RFw'r. apply seq_eqv_lr in RFw'r. desc.
  red in RFw'r0. 
  unfold state_before_event in RFw'r0.
  rewrite <- Heqst_r in RFw'r0.
  ex_des.
  desc. rewrite <- H2 in RFw'r0.
  assert (SyEvents.loc r = loc) as LOC.
  { replace loc with (SyEvents.loc w); [| vauto].
    apply (wf_frl WFG) in FRrw_. vauto. }
  rewrite LOC in RFw'r0. 

  destruct (filter (fun loc_val : Loc * Val => fst loc_val =? loc) (cpu_bufs thread)) eqn:BUF_FLT; [done| ].  
  desc. red in RFw'r0. desc.
  specialize (RFw'r2 w). specialize_full RFw'r2.
  { splits; vauto. }
  red in RFw'r2. des.
  { subst w'. by apply (co_irr WFG w). }
  forward eapply (SyExecution.same_thread WFG w' w) as SBW; try (by vauto).
  { red. ins. by apply (proj1 Eninit_non_init w'). }
  { unfold tid, exact_tid in *; desf. }
  des.
  { red in SBW. des.
    { subst w'. by apply (co_irr WFG w). }
    red in SBW. apply seq_eqv_lr in SBW. desc.
    forward eapply (proj1 tb_respects_sb w' w) as H_; [basic_solver| ].
    apply seq_eqv_lr in H_. destruct H_ as [_ [[TB TID] _]]. 
    unfold trace_before in *. lia. }
  forward eapply (@cpu_vis_respects_sb_w w w') as VIS. 
  { red. splits; vauto. split; unfolder'; desf. }
  do 2 red in VIS. des.
  { red in VIS. desc. vauto. }
  simpl in COw'w. apply seq_eqv_lr in COw'w.
  apply seq_eqv_lr in VIS. desc.
  red in COw'w0. desc. do 2 red in COw'w0. des.
  { red in COw'w0. desc. apply (proj1 Eninit_non_init w'). vauto. }
  apply seq_eqv_lr in COw'w0. desc. lia.
Qed. 

Lemma w_sbloc_fr_implies_co: ⦗is_w⦘ ⨾ poloc G ∩ is_cpu × is_cpu ⨾ fre G ⊆ co G.
Proof.
  rewrite seq_eqv_l. unfold seq. red. intros w1 w2 [Wx [r [[[SBw1r LOCw1r] [CPUW CPUR]] FRErw2]]]. 
  apply seq_eqv_lr. apply (wf_freD WFG) in FRErw2. apply seq_eqv_lr in FRErw2.
  destruct FRErw2 as [Rr [FRErw2 Ww2]].
  apply (wf_freE WFG) in FRErw2. apply seq_eqv_lr in FRErw2. desc.
  assert (EG w1) as Ew1. 
  { red in SBw1r. apply seq_eqv_lr in SBw1r. by desc. }
  splits; vauto.
  assert (loc r = loc w2) as LOCrw2. 
  1: { apply eq_Transitive with (y := loc r); auto.
       pose proof (proj2 (fri_union_fre G)). rewrite (wf_frl WFG) in H.
       apply H. vauto. }
  red. split; [| congruence]. 
  destruct (classic (w1 = w2)) as [EQ|NEQ].
  { subst w2. exfalso. apply (@sb_fr_irr w1). 
    red. exists r. split; auto. 
    - apply seq_eqv_lr; splits; vauto.
    - apply fri_union_fre; right; auto. }
  forward eapply (@wf_co_total G WFG (loc r) w1) as TOTAL; eauto. 
  1,2: done.
  des.
  { simpl in TOTAL. apply seq_eqv_lr in TOTAL. desc. red in TOTAL0. by desc. }
  exfalso. 
  cut (fr G r w1).
  { ins. exfalso. apply (@sb_fr_irr w1). 
    red.
    exists r.
    splits; vauto.
    apply seq_eqv_lr. splits; vauto. }
  red. red. split.
  2: { red. ins. red in H. desc. subst. eapply sb_irr. eauto. }
  red. do 2 (do 2 red in FRErw0; desc).
  red in FRErw0. destruct FRErw0 as [w' [RFw'r COw'w2]].
  exists w'. split; auto. apply (co_trans WFG) with (y := w2); auto.
Qed.

Lemma minus_inter_union {A: Type} (r r': relation A) : r ≡ r ∩ r' ∪ r \ r'.
Proof. unfolder; split; ins; desf; tauto. Qed.

Lemma sb_ppo_ext G: (sb G ∩ is_cpu × is_cpu) ≡ ppoCpu G ∪ (⦗is_w⦘ ⨾ sb G ⨾ ⦗is_r⦘) ∩ is_cpu × is_cpu.
Proof.
  rewrite (minus_inter_union (sb G) ((is_w) × (is_r))) at 1.
  unfold ppo. rewrite unionC. 
  rewrite inter_union_l.
  apply union_more; [auto| basic_solver].
Qed.

Lemma SCPL: acyclic ((poloc G ∪ rf G ∪ co G ∪ fr G) ∩ (is_cpu × is_cpu)).
Proof.
    assert (rfe G ∪ coe G ∪ fre G ⊆ vis_lt') as EXT_ORDER.
    { arewrite (coe G ⊆ co G). arewrite (fre G ⊆ fr G). 
      rewrite rfe_implies_vis_lt, co_implies_vis_lt, fr_implies_vis_lt.
      by rewrite !unionK. }
    assert (acyclic (TSO_hb G)) as TSO_HB_ACYC.  
    { red. unfold TSO_hb. rewrite ct_of_ct. 
      assert ((ppo G ∪ rfe G ∪ co G ∪ fr G) ≡ (rfe G ∪ co G ∪ fr G ∪ ppo G)) as REW by basic_solver.
      rewrite REW.
      rewrite inter_union_l.
      rewrite ppo_cpu_constraint.
      rewrite vis_respects_ppo_cpu, rfe_implies_vis_lt, co_implies_vis_lt, fr_implies_vis_lt. rewrite !unionK.
      cdes vis_SPO. apply trans_irr_acyclic; auto; basic_solver. }
      
    arewrite (poloc G ∪ rf G ∪ co G ∪ fr G ⊆ rf G ∪ co G ∪ fr G ∪ poloc G).
    { basic_solver. }
    rewrite inter_union_l.
    rewrite rel_helper. 
    rewrite <- inter_union_l.
    arewrite ((poloc G ∪ (rfe G ∪ coe G ∪ fre G) ∪ poloc G) ⊆ (poloc G ∪ (rfe G ∪ coe G ∪ fre G))).
    rewrite !inter_union_l.
    apply acyclic_union1.
    { unfold poloc. rewrite !inclusion_inter_l1. apply sb_acyclic. }
    { apply inclusion_acyclic with (r' := TSO_hb G); auto.
      unfold TSO_hb. rewrite <- ct_step. 
      rewrite coi_union_coe, fri_union_fre. basic_solver. }
    rewrite ct_of_trans.
    2: { 
      apply transitive_restr.
      apply restr_eq_trans, sb_trans. 
    }
    arewrite (poloc G ∩ is_cpu × is_cpu ⊆ (ppo G ∪ (⦗is_w⦘ ⨾ (poloc G) ⨾ ⦗is_r⦘)) ∩ is_cpu × is_cpu).
    {
      unfold poloc.
      arewrite (sb G ∩ same_loc ∩ is_cpu × is_cpu ⊆ sb G ∩ is_cpu × is_cpu ∩ same_loc); [basic_solver|].
      rewrite sb_ppo_ext at 1. rewrite inter_union_l.
      rewrite inclusion_inter_l1.
      rewrite !inter_union_l.
      rewrite ppo_cpu_constraint.
      apply union_mori; basic_solver. }
    rewrite inter_union_l.
    rewrite seq_union_l. 
    rewrite ppo_cpu_constraint.
    rewrite vis_respects_ppo_cpu. 
    do 2 rewrite <- inter_union_l.
    rewrite EXT_ORDER at 1. 
    rewrite ct_begin with (r := (rfe G ∪ coe G ∪ fre G) ∩ is_cpu × is_cpu). rewrite EXT_ORDER at 2.
    rewrite seq_eqv_inter_ll.
    rewrite seq_eqv_inter_lr.
    do 2 rewrite seqA.
    
    arewrite (⦗is_r⦘ ⨾ (rfe G ∪ coe G ∪ fre G) ∩ is_cpu × is_cpu ⊆ fre G).
    { arewrite ((rfe G ∪ coe G ∪ fre G) ∩ is_cpu × is_cpu ⊆ (rfe G ∪ coe G ∪ fre G)).
      rewrite (wf_rfeD WFG), (wf_coeD WFG).
      rewrite <- seq_union_r. 

      case_union _ _ .
      seq_rewrite <- id_inter.
      arewrite ((is_r) ∩₁ is_w ≡₁ ∅); [| basic_solver]. 
      red. split; [| basic_solver]. red. ins. do 2 (red in H; desc).
      unfolder'; desf. }
    sin_rewrite w_sbloc_fr_implies_co. rewrite co_implies_vis_lt.
    arewrite (vis_lt' ∩ is_cpu × is_cpu ⊆ vis_lt').
    rewrite <- seq_union_r. rewrite inclusion_t_rt, unionK. rewrite <- ct_begin.
    unfold acyclic. rewrite ct_of_ct. fold (acyclic vis_lt').
    cdes vis_SPO. apply trans_irr_acyclic; auto.
Qed.

Lemma WFG_fpga: Wf_fpga G.
Proof.
  split; ins.
  all: try basic_solver.
  all: (unfold set_subset;
        intros;
        destruct H;
        destruct H;
        [unfolder';
          destruct x; vauto|];
        unfold dom_rel).
  { forward eapply (readpair_exists' x H H0) as E.
    desf.
    exists e'.
    apply seq_eqv_lr; splits; unfolder'; vauto; desf.
    intuition; vauto. }
  { forward eapply (writepair_exists' x H H0) as E.
    desf.
    exists e'.
    apply seq_eqv_lr; splits; unfolder'; vauto; desf.
    intuition; vauto. }
  { forward eapply (fenceonepair_exists' x H H0) as E.
    desf.
    exists e'.
    apply seq_eqv_lr; splits; unfolder'; vauto; desf.
    intuition; vauto. }
  forward eapply (fenceallpair_exists' x H H0) as E.
  desf.
  exists e'.
  apply seq_eqv_lr; splits; unfolder'; vauto; desf.
  intuition; vauto.
Qed.

Lemma TSO_op_implies_decl:
  (fun e => trace_elems tr (EventLab e)) ≡₁ acts G \₁ is_init /\ 
  Wf_fpga G /\ Wf G /\
  Ax86Consistent G.
Proof.
  splits.
  { simpl. unfold EG.
    rewrite set_minus_union_l, set_minusK, set_union_empty_l.
    unfold Eninit. eapply set_equiv_rel_Transitive; [apply set_equiv_refl| ].
    symmetry. apply empty_inter_minus_same. rewrite set_interC. apply Eninit_non_init. }
  { apply WFG_fpga. }
  { apply WFG. }
  split.
  { apply SCPL. }
  { apply propagation'. }
  { apply read_after_write'. }
  { apply read_after_fence'. }
  { apply no_read_from_future'. }
  { apply observe_same_channel'. }
  { apply fence_all_response'. }
  { apply fence_one_response'. }
  { apply fence_all_block'. }
  apply fence_one_block'.
Qed.


End SyLemmas.