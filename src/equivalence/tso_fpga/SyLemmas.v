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
Hypothesis BOUNDED_THREADS: exists n, forall e, Eninit e -> tid e < n.
Hypothesis NO_TID0: forall e, is_cpu e -> tid e <> 0. 
Hypothesis NO_TID1: forall e, is_cpu e -> tid e <> 1.

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
  assert (tid e1 <> 1). eapply NO_TID1. eauto.
  assert (tid e2 = 1).
  {
    unfold tid.
    destruct e2; auto;unfold Efpga in E2; desc; unfold is_fpga in E2; done.
  }
  lia.
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
      (OTHER: lbl_thread_opt lbl <> Some thread):
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
check (cpu_write' ∩₁ in_thread thread) lbl =
check (is_cpu_prop ∩₁ in_thread thread) lbl +
length (cpu_bufs st2 thread).
Proof.
destruct st1 as [mem1 buf1]. destruct st2 as [mem2 buf2]. simpl.
destruct (classic (lbl_thread_opt lbl = Some thread)) as [EQ | NEQ] .
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

Lemma upstream_size_inv st1 st2 lbl chan (STEP: TSOFPGA_step st1 lbl st2):
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

Lemma buffer_size_cpu thread i (DOM: NOmega.le (NOnum i) (trace_length tr)):
  count_upto (cpu_write' ∩₁ in_thread thread) i = count_upto (is_cpu_prop ∩₁ in_thread thread) i + length (cpu_bufs (states i) thread).
Proof.
  induction i.
  { simpl. unfold count_upto. rewrite seq0. simpl.
    pose proof TS0 as TS0. simpl in TS0. by rewrite <- TS0. }
  remember (states (S i)) as s. simpl.
  unfold count_upto. rewrite !seqS, !Nat.add_0_l, !map_app, !filterP_app, !length_app. simpl.
  fold (count_upto (cpu_write' ∩₁ in_thread thread) i).
  fold (count_upto (is_cpu_prop ∩₁ in_thread thread) i).
  specialize_full IHi.
  { apply NOmega.le_trans with (m := NOnum (S i)); vauto. } 
  fold (check (cpu_write' ∩₁ in_thread thread) (trace_nth i tr def_lbl)). 
  fold (check (is_cpu_prop ∩₁ in_thread thread) (trace_nth i tr def_lbl)). 
  remember (states i) as st_prev.
  rewrite IHi.
  rewrite <- !Nat.add_assoc.
  f_equal. 

  simpl in IHi. 
  apply buffer_size_inv.
  forward eapply (TSi i) with (d := def_lbl) as TSi; vauto.
Qed. 


Lemma buffer_size_fpga chan i (DOM: NOmega.le (NOnum i) (trace_length tr)):
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
  apply upstream_size_inv.
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

Definition same_thread x y :=
  let thread := lbl_thread_opt x in
  thread = lbl_thread_opt y /\ thread <> None.

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


Lemma EXACT_CPU_PROPS thread:
  trace_length (trace_filter (cpu_write' ∩₁ in_thread thread) tr) =
  trace_length (trace_filter (is_cpu_prop ∩₁ in_thread thread) tr).
Proof.
remember (trace_length (trace_filter (cpu_write' ∩₁ in_thread thread) tr)) as len_writes.
remember (trace_length (trace_filter (is_cpu_prop ∩₁ in_thread thread) tr)) as len_props. 
pose proof (NOmega_lt_trichotomy len_writes len_props). des; auto.
{ exfalso. destruct len_writes as [|n_writes]; auto.
  forward eapply (trace_nth_filter (is_cpu_prop ∩₁ in_thread thread) tr n_writes def_lbl) as [extra_prop_pos [DOM_EP [MATCH_PROP COUNT_PROPS]]].
  { vauto. }
  fold (count_upto (is_cpu_prop ∩₁ in_thread thread) extra_prop_pos) in COUNT_PROPS.
  forward eapply (filter_ends tr (cpu_write' ∩₁ in_thread thread) def_lbl) as [w_bound [DOM_WB WRITES_BOUND]]. 
  { by rewrite <- Heqlen_writes. }
  set (bound := max (extra_prop_pos + 1) w_bound).     
  forward eapply (buffer_size_cpu thread bound) as BUF_SIZE.
  { destruct tr; auto. simpl in *. subst bound.
    apply NPeano.Nat.max_lub_iff. split; lia. }
  simpl in BUF_SIZE. remember (states bound) as st.
  cut (count_upto (cpu_write' ∩₁ in_thread thread) bound <= n_writes /\
        count_upto (is_cpu_prop ∩₁ in_thread thread) bound > n_writes).
    
  { ins. desc. lia. }
  split.
  { cut (NOmega.le (NOnum (count_upto (cpu_write' ∩₁ in_thread thread) bound)) (NOnum n_writes)).
    { ins. }
    rewrite Heqlen_writes. unfold count_upto. apply count_le_filter.
    simpl. destruct (trace_length tr); vauto.
    subst bound. apply Nat.max_lub_iff. simpl in *. split; lia. }
  unfold gt. apply Nat.lt_le_trans with (m := count_upto (is_cpu_prop ∩₁ in_thread thread) (extra_prop_pos + 1)).
  { rewrite COUNT_PROPS.
    rewrite Nat.add_1_r, count_upto_next.
    rewrite check1; [lia| ].
    unfold trace_labels. rewrite <- MATCH_PROP.
    forward eapply (trace_nth_in (trace_filter (is_cpu_prop ∩₁ in_thread thread) tr) n_writes) with (d := def_lbl) as IN_FILTER. 
    { rewrite <- Heqlen_props. vauto. }
    vauto. 
    apply trace_in_filter in IN_FILTER. by desc. }
  apply count_upto_more. subst bound. apply Nat.le_max_l. }
exfalso. 
destruct len_props as [|n_props]; auto.

forward eapply (trace_nth_filter (cpu_write' ∩₁ in_thread thread) tr n_props def_lbl) as [extra_write_pos [DOM_EW [MATCH_WRITE COUNT_WRITES]]].
{ vauto. }
fold (count_upto (cpu_write' ∩₁ in_thread thread) extra_write_pos) in COUNT_WRITES.
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
  simpl in BUF_SIZE. cut (count_upto (cpu_write' ∩₁ in_thread thread) i > count_upto (is_cpu_prop ∩₁ in_thread thread) i); [ins; lia| ].
  unfold gt.
  apply Nat.le_lt_trans with (m := n_props).
  { forward eapply (count_le_filter tr (is_cpu_prop ∩₁ in_thread thread) i def_lbl) as COUNT_LE_FILTER; auto.
    rewrite <- Heqlen_props in COUNT_LE_FILTER. simpl in COUNT_LE_FILTER.
    by unfold count_upto. }
  apply Nat.lt_le_trans with (m := count_upto (cpu_write' ∩₁ in_thread thread) (extra_write_pos + 1)).
  2: { apply count_upto_more. lia. }
  rewrite Nat.add_1_r, count_upto_next. rewrite <- COUNT_WRITES.
  rewrite check1; [lia| ].
  unfold trace_labels. rewrite <- MATCH_WRITE.
  remember (cpu_write' ∩₁ in_thread thread) as F.
  remember (trace_nth n_props (trace_filter F tr) def_lbl) as elem. 
  forward eapply (proj1 (trace_in_filter elem F tr)); [| intuition]. 
  subst elem. apply trace_nth_in. vauto. }  

forward eapply (filter_ends tr (is_cpu_prop ∩₁ in_thread thread) def_lbl) as [props_end [DOM NOMORE_PROPS]]. 
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
  assert (same_thread (trace_labels w) ≡₁ in_thread thread).
  { rewrite H. simpl. unfold same_thread. simpl.
    unfold in_thread.
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
  assert (same_thread (trace_labels w) = in_thread thread) as RESTR_EQUIV. 
  { apply set_extensionality. rewrite TLAB. simpl.
    unfold same_thread, in_thread. simpl. red. splits; red; ins; desc; vauto. }
  rewrite RESTR_EQUIV in CORR.
  replace (count_upto (is_cpu_prop∩₁ in_thread thread) (p + 1)) with ((count_upto (is_cpu_prop∩₁ in_thread thread) p) + 1) in BUF_SIZE.
  2: { unfold count_upto.
       rewrite Nat.add_1_r with (n := p), seqS, Nat.add_0_l.
       rewrite map_app, filterP_app, length_app. simpl.
       rewrite RESTR_EQUIV in PROP.
       destruct (excluded_middle_informative ((is_cpu_prop∩₁ in_thread thread) (trace_nth p tr def_lbl))); vauto. }
  rewrite <- CORR in BUF_SIZE.
  cut (count_upto (cpu_write' ∩₁ in_thread thread) (p + 1) <= count_upto (cpu_write' ∩₁ in_thread thread) w).
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
    apply fpga_write_structure in f. destruct f as [chan [index [meta H0]]].
    rewrite H0 in PROP. red in PROP. desc. vauto. }
  exfalso. rename H into LT. 
  apply fpga_write_structure in f. destruct f as [chan [index [meta TLAB]]].
  forward eapply (buffer_size_fpga chan (p + 1)) as BUF_SIZE.
  { contra GE. forward eapply (proj2 (ge_default p)) as P_DEF. 
    { red. intros. apply GE. simpl. red in H. destruct tr; vauto.
      simpl in *. lia. }
    red in PROP. rewrite P_DEF in PROP.
    generalize PROP. unfolder'. intuition. }
  red in CORR.
  assert (same_chan (trace_labels w) = in_chan chan) as RESTR_EQUIV. 
  { apply set_extensionality. rewrite TLAB. simpl.
    unfold same_chan, in_thread. simpl. red. splits; red; ins; desc; vauto. }
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
Definition vis (e: Event) :=
  match (excluded_middle_informative (is_cpu_wr e)) with
  | left W => write2prop (trace_index e)
  | right _ => match (excluded_middle_informative (is_wr_resp e)) with
    | left W => write2prop (trace_index e)
    | right _ => (trace_index e)
    end
  end. 

Definition vis_lt := is_init × Eninit ∪ ⦗Eninit⦘ ⨾ (fun x y => vis x < vis y) ⨾ ⦗Eninit⦘. 

Lemma vis_SPO:
  strict_partial_order vis_lt. 
Proof.
  unfold vis_lt, map_rel. 
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

Lemma TI_LE_VIS e (ENINIT: Eninit e): trace_index e <= vis e.
Proof.
  unfold vis. simpl.
  destruct (excluded_middle_informative (is_cpu_wr e)).
  {
    apply Nat.lt_le_incl. apply w2p_later_cpu.
    unfold trace_labels. rewrite trace_index_simpl; auto.
  }
  destruct (excluded_middle_informative (is_wr_resp e)).
  2: { lia. }
  apply Nat.lt_le_incl. apply w2p_later_fpga.
  unfold trace_labels. rewrite trace_index_simpl; auto.
Qed.

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

Lemma r_vis e (Rr: is_cpu_rd e): vis e = trace_index e.
Proof.
  unfold vis.
  generalize Rr. unfolder'. destruct e; vauto.
  destruct e; ins.
  all: destruct (excluded_middle_informative _ ); intuition.
Qed. 

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


Definition rf' w r :=
  let (wp, rp, ups, downs, mem, bufs) := (state_before_event r) in
  match (excluded_middle_informative (is_cpu_wr w)) with
  | left W => 
    match filter (fun loc_val: Loc * Val => Nat.eqb (fst loc_val) (loc r))
                  (bufs (exact_tid r)) with
      | nil => latest_of_by (fun e => loc e = loc r /\ vis_lt' e r /\ EG e /\ is_w e) vis_lt' w
      | _ => latest_of_by (fun e => loc e = loc r /\ trace_before e r /\ exact_tid e = exact_tid r /\ Eninit e /\ is_w e) trace_before w
      end
  | right _ => latest_of_by (fun e => loc e = loc r /\ vis_lt' e r /\ EG e /\ is_w e ) vis_lt' w
  end.


Definition readpair' req resp := is_rd_req req /\ is_rd_resp resp /\ meta req = meta resp.
Definition writepair' req resp := is_wr_req req /\ is_wr_resp resp /\ meta req = meta resp.
Definition fenceonepair' req resp := is_fence_req_one req /\ is_fence_resp_one resp /\ meta req = meta resp.
Definition fenceallpair' req resp := is_fence_req_all req /\ is_fence_resp_all resp /\ meta req = meta resp.
Definition pair' req resp := readpair' req resp \/ writepair' req resp \/ fenceonepair' req resp \/ fenceallpair' req resp.
  

Definition nth_such n S i := count_upto S i = n /\ S (trace_labels i).

(* Lemma rmw_vis e (RMW: is_rmw e): vis e = trace_index e.
Proof.
  unfold vis.
  destruct (excluded_middle_informative (is_cpu_write' e)); auto.
  exfalso. do 2 red in i. desc. apply i0. red. vauto. 
Qed. *)

Lemma RESTR_EQUIV thread index lbl:
  same_thread (EventLab (ThreadEvent thread index lbl)) = in_thread thread.
Proof.
  ins. apply set_extensionality. 
  unfold same_thread, in_thread. simpl. red. splits; red; ins; desc; vauto.
Qed. 
    
Definition G :=
  {| acts := EG;
     co := ⦗EG ∩₁ is_w⦘ ⨾ restr_eq_rel SyEvents.loc vis_lt ⨾ ⦗EG ∩₁ is_w⦘;     
     rf := ⦗EG ∩₁ is_w⦘ ⨾ rf' ⨾ ⦗EG ∩₁ is_r⦘;
     readpair := ⦗EG ∩₁ is_rd_req⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_rd_resp⦘;
     writepair := ⦗EG ∩₁ is_wr_req⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_wr_resp⦘;
     fenceonepair := ⦗EG ∩₁ is_fence_req_one⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_fence_resp_one⦘;
     fenceallpair := ⦗EG ∩₁ is_fence_req_all⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_fence_resp_all⦘
  |}.


Lemma no_read_from_future': irreflexive (rf G ⨾ sb G).
Proof.
  rewrite rfi_union_rfe.
  arewrite (rfi G ⊆ sb G).
  rewrite seq_union_l.
  apply irreflexive_union.
  split.
  { rewrite rewrite_trans.
    all: admit. }
  (* доказать, что rfe из разных потоков *)

  


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


Lemma vis_lt_init_helper x y (SB: sb G x y): vis_lt x y \/ (Eninit x /\ Eninit y).
Proof.
unfold sb in SB. apply seq_eqv_lr in SB. destruct SB as [Ex [SBxy Ey]]. ins.  
do 2 red in Ex. des.
{ do 2 red in Ey. des; vauto.
  red in SBxy. destruct x, y; vauto. }
do 2 red in Ey. des.
{ red in SBxy. destruct x, y; vauto. }
vauto.
Qed.


Lemma vis_respects_sb_w: restr_rel is_w (sb G) ⊆ vis_lt.
Proof.
unfold restr_rel. red. ins. destruct H as [SBxy [Wx Wy]].
destruct (vis_lt_init_helper x y SBxy) as [|[E'x E'y]]; auto. 
red. red. right. apply seq_eqv_lr. splits; auto.
red in SBxy. apply seq_eqv_lr in SBxy. destruct SBxy as [_ [SBxy _]].
forward eapply (proj1 tb_respects_sb x y) as H; [basic_solver| ].
apply seq_eqv_lr in H. destruct H as [_ [[TBxy TIDxy] _]]. 
(* apply tb_respects_sb in SBxy. destruct SBxy as [TBxy TIDxy].  *)
red in TBxy.
unfold vis. 
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
    assert (exists thread, same_thread (EventLab x) = in_thread thread /\ same_thread (EventLab y) = in_thread thread).
    { pose proof (reg_write_structure _ c). desc. inv H. 
      pose proof (reg_write_structure _ c0). desc. inv H0. 
      red in TIDxy. simpl in TIDxy. inv TIDxy.
      exists thread0. 
      split; apply RESTR_EQUIV. }
    desc. rewrite H, H0 in *. 
    assert (count_upto (cpu_write' ∩₁ in_thread thread) (trace_index x) < count_upto (cpu_write' ∩₁ in_thread thread) (trace_index y)).
    { subst. apply Nat.lt_le_trans with (m := count_upto (cpu_write' ∩₁ in_thread thread) (trace_index x + 1)).
      2: { eapply count_upto_more. lia. }
      rewrite Nat.add_1_r, count_upto_next.
      rewrite check1; [lia|].
      unfold trace_labels. rewrite trace_index_simpl; auto. red. split; auto.
      rewrite <- H. unfold same_thread. generalize c. 
      destruct x; unfolder'; intuition; vauto.
    } 
    apply lt_diff in H1. desc. rewrite W_P_CORR0, W_P_CORR in H1. 
    destruct (NPeano.Nat.lt_ge_cases px py); auto. 
    remember (count_upto_more py px (is_cpu_prop ∩₁ in_thread thread) H2); lia. }
  destruct (NPeano.Nat.lt_ge_cases (write2prop (trace_index x)) (trace_index y)) as [LL | LE].
  exfalso.
  forward eapply (@reg_write_structure (EventLab x)) as H. 
  { vauto. }
  desc. inversion H. clear H.  
  destruct y.
  { exfalso. by apply (proj1 Eninit_non_init (InitEvent x0)). }
  destruct l; vauto.
  assert (thread0 = thread); [|subst thread0]. 
  { red in TIDxy. vauto. }
  remember (ThreadEvent thread index0 (Armw x0 vr vw)) as tlab. 
  assert (NOmega.lt_nat_l (trace_index tlab) (trace_length tr)) as DOM. 
  { contra GE. apply ge_default in GE.
    unfold trace_labels in GE. rewrite trace_index_simpl in GE; auto. 
    rewrite Heqtlab in GE. discriminate GE. }
  set (st := states (trace_index tlab)).
  forward eapply (TSi (trace_index tlab)) with (d := def_lbl) as TSi; eauto. 
  rewrite trace_index_simpl in TSi; auto.
  rewrite Heqtlab in TSi at 2. inversion TSi. subst. 
  remember (ThreadEvent thread index0 (Armw x0 (sh_mem x0) vw)) as e_rmw. 
  remember (ThreadEvent thread index (Astore loc val)) as e_w.
  forward eapply (@buffer_size thread (trace_index e_rmw)) as BUF_SIZE. 
  { destruct (trace_length tr); auto. simpl in *. lia. }
  simpl in BUF_SIZE. rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE.
  rewrite NO_BUF in BUF_SIZE. simpl in BUF_SIZE. rewrite Nat.add_0_r in BUF_SIZE.
  remember (write2prop (trace_index e_w)) as vis_w. 
  assert (count_upto (regular_write' ∩₁ same_thread (trace_labels (trace_index e_w))) (trace_index e_w) =
          count_upto (is_prop ∩₁ same_thread (trace_labels (trace_index e_w))) vis_w) as VIS_W.
  { subst vis_w. unfold write2prop in *. destruct (excluded_middle_informative _).
    2: { generalize n, X. rewrite trace_index_simpl'; auto. by unfolder'. }
    destruct (constructive_indefinite_description _ _). desc. simpl in *.
    lia. }
  replace (same_thread (trace_labels (trace_index e_w))) with (in_thread thread) in VIS_W.
  2: { rewrite trace_index_simpl'; auto. subst e_w. by rewrite RESTR_EQUIV. }
  assert (count_upto (regular_write' ∩₁ in_thread thread) (trace_index e_w) < count_upto (regular_write' ∩₁ in_thread thread) (trace_index e_rmw)) as MORE_WRITES.
  { unfold lt. rewrite <- Nat.add_1_r.
    rewrite <- (@check1 _ (regular_write' ∩₁ in_thread thread) (trace_labels ((trace_index e_w)))).
    2: { red. rewrite trace_index_simpl'; auto. by subst e_w. }
    rewrite <- count_upto_next. apply count_upto_more. lia. }
  assert (count_upto (is_prop ∩₁ in_thread thread) (trace_index e_rmw) <= count_upto (is_prop ∩₁ in_thread thread) vis_w) as MORE_PROPS.
  { apply count_upto_more. lia. }
  lia. 
}
destruct (excluded_middle_informative _) as [X | X]; destruct (excluded_middle_informative _) as [X' | X']; auto. 
3: { apply lt_trans with (m := trace_index y); auto. apply w2p_later.
      unfold trace_labels. rewrite trace_index_simpl; auto. }
{ unfold write2prop. destruct (excluded_middle_informative _); vauto.
  2: { unfold trace_labels in n. rewrite trace_index_simpl in n; vauto. }
  destruct (excluded_middle_informative _); vauto.
  2: { unfold trace_labels in n. rewrite trace_index_simpl in n; vauto. }
  destruct (constructive_indefinite_description _ _) as [px Px].
  destruct (constructive_indefinite_description _ _) as [py Py].
  simpl in *. desc.
  unfold trace_labels in *. rewrite !trace_index_simpl in *; auto.
  assert (exists thread, same_thread (inl x) = in_thread thread /\ same_thread (inl y) = in_thread thread).
  { pose proof (reg_write_structure _ r). desc. inv H. 
    pose proof (reg_write_structure _ r0). desc. inv H0. 
    red in TIDxy. simpl in TIDxy. inv TIDxy.
    exists thread0. 
    split; apply RESTR_EQUIV. }
  desc. rewrite H, H0 in *. 
  assert (count_upto (regular_write' ∩₁ in_thread thread) (trace_index x) < count_upto (regular_write' ∩₁ in_thread thread) (trace_index y)).
  { subst. apply Nat.lt_le_trans with (m := count_upto (regular_write' ∩₁ in_thread thread) (trace_index x + 1)).
    2: { eapply count_upto_more. lia. }
    rewrite Nat.add_1_r, count_upto_next.
    rewrite check1; [lia|].
    unfold trace_labels. rewrite trace_index_simpl; auto. red. split; auto.
    rewrite <- H. unfold same_thread. generalize r. destruct x. unfolder'. intuition. vauto. } 
  apply lt_diff in H1. desc. rewrite W_P_CORR0, W_P_CORR in H1. 
  destruct (NPeano.Nat.lt_ge_cases px py); auto. 
  pose proof (count_upto_more (is_prop ∩₁ in_thread thread) H2). lia. }
destruct (NPeano.Nat.lt_ge_cases (write2prop (trace_index x)) (trace_index y)) as [| LE]; auto.
exfalso.
forward eapply (@reg_write_structure (inl x)) as H. 
{ vauto. }
desc. inversion H. clear H.  
destruct y.
{ exfalso. by apply (proj1 Eninit_non_init (InitEvent x0)). }
destruct l; vauto.
assert (thread0 = thread); [|subst thread0]. 
{ red in TIDxy. vauto. }
remember (ThreadEvent thread index0 (Armw x0 vr vw)) as tlab. 
assert (NOmega.lt_nat_l (trace_index tlab) (trace_length tr)) as DOM. 
{ contra GE. apply ge_default in GE.
  unfold trace_labels in GE. rewrite trace_index_simpl in GE; auto. 
  rewrite Heqtlab in GE. discriminate GE. }
set (st := states (trace_index tlab)).
forward eapply (TSi (trace_index tlab)) with (d := def_lbl) as TSi; eauto. 
rewrite trace_index_simpl in TSi; auto.
rewrite Heqtlab in TSi at 2. inversion TSi. subst. 
remember (ThreadEvent thread index0 (Armw x0 (sh_mem x0) vw)) as e_rmw. 
remember (ThreadEvent thread index (Astore loc val)) as e_w.
forward eapply (@buffer_size thread (trace_index e_rmw)) as BUF_SIZE. 
{ destruct (trace_length tr); auto. simpl in *. lia. }
simpl in BUF_SIZE. rewrite <- H0 in BUF_SIZE. simpl in BUF_SIZE.
rewrite NO_BUF in BUF_SIZE. simpl in BUF_SIZE. rewrite Nat.add_0_r in BUF_SIZE.
remember (write2prop (trace_index e_w)) as vis_w. 
assert (count_upto (regular_write' ∩₁ same_thread (trace_labels (trace_index e_w))) (trace_index e_w) =
        count_upto (is_prop ∩₁ same_thread (trace_labels (trace_index e_w))) vis_w) as VIS_W.
{ subst vis_w. unfold write2prop in *. destruct (excluded_middle_informative _).
  2: { generalize n, X. rewrite trace_index_simpl'; auto. by unfolder'. }
  destruct (constructive_indefinite_description _ _). desc. simpl in *.
  lia. }
replace (same_thread (trace_labels (trace_index e_w))) with (in_thread thread) in VIS_W.
2: { rewrite trace_index_simpl'; auto. subst e_w. by rewrite RESTR_EQUIV. }
assert (count_upto (regular_write' ∩₁ in_thread thread) (trace_index e_w) < count_upto (regular_write' ∩₁ in_thread thread) (trace_index e_rmw)) as MORE_WRITES.
{ unfold lt. rewrite <- Nat.add_1_r.
  rewrite <- (@check1 _ (regular_write' ∩₁ in_thread thread) (trace_labels ((trace_index e_w)))).
  2: { red. rewrite trace_index_simpl'; auto. by subst e_w. }
  rewrite <- count_upto_next. apply count_upto_more. lia. }
assert (count_upto (is_prop ∩₁ in_thread thread) (trace_index e_rmw) <= count_upto (is_prop ∩₁ in_thread thread) vis_w) as MORE_PROPS.
{ apply count_upto_more. lia. }
lia. 
Qed.

Lemma Ax86ConsistentG: Ax86Consistent G.
Proof.
  split.
  {
    red. red.
    ins.
    destruct H.
    { admit. }
    
  }

Lemma TSO_op_implies_decl:
  (fun e => trace_elems tr (EventLab e)) ≡₁ acts G \₁ is_init /\ 
  Wf_fpga G /\
  Ax86Consistent G.
Proof.
  Admitted.


End SyLemmas.