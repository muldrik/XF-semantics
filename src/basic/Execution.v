Require Import Labels.
Require Import Events.
From hahn Require Import Hahn.
Require Import Lia.

Set Implicit Arguments.

Section Execution.


(* Notation "'WrReq'" := (fun a => is_true (is_wr_req a)).
Notation "'WrRsp'" := (fun a => is_true (is_wr_resp a)).
Notation "'RdReq'" := (fun a => is_true (is_rd_req a)).
Notation "'RdRsp'" := (fun a => is_true (is_rd_resp a)).
Notation "'FnReqOne'" := (fun a => is_true (is_fence_req_one a)).
Notation "'FnRspOne'" := (fun a => is_true (is_fence_resp_one a)).
Notation "'FnReqAll'" := (fun a => is_true (is_fence_req_all a)).
Notation "'FnRspAll'" := (fun a => is_true (is_fence_resp_all a)).
Notation "'CpuWrite'" := (fun a => is_true (is_cpu_wr a)).
Notation "'CpuRead'" := (fun a => is_true (is_cpu_rd a)).
Notation "'CpuFence'" := (fun a => is_true (is_cpu_fence a)). *)

Notation "'WrReq'" := is_wr_req.
Notation "'WrRsp'" := is_wr_resp.
Notation "'RdReq'" := is_rd_req.
Notation "'RdRsp'" := is_rd_resp.
Notation "'FnReqOne'" := is_fence_req_one.
Notation "'FnRspOne'" := is_fence_resp_one.
Notation "'FnReqAll'" := is_fence_req_all.
Notation "'FnRspAll'" := is_fence_resp_all.
Notation "'CpuWrite'" := is_cpu_wr.
Notation "'CpuRead'" := is_cpu_rd.
Notation "'CpuFence'" := is_cpu_fence.

Notation "'W'" := is_w.
Notation "'R'" := is_r.
Notation "'Req'" := is_req.
Notation "'Rsp'" := is_resp.
Notation "'Cpu'" := is_cpu.
Notation "'Fpga'" := is_fpga.


Definition same_ch := fun a b => chan_opt a = chan_opt b /\ chan_opt a <> None.
Definition same_loc := fun a b => loc a = loc b.
Definition same_meta := fun a b => meta a = meta b.


Record execution :=
  { acts : Event -> Prop ;
    rf : Event -> Event -> Prop ;
    co : Event -> Event -> Prop ; (* QQ: Что это? *)
    readpair : Event -> Event -> Prop ;
    writepair: relation Event ;
    fenceonepair: relation Event;
    fenceallpair: relation Event;
  }.

Ltac show_dom :=
  match goal with
    |- ?x ≡ _ =>
    rewrite <- restr_relE;
    split; [|solve [apply inclusion_restr]];
    try unfold x;
    repeat first [rewrite <- restr_ct |
                  rewrite restr_minus_alt |
                  rewrite restr_union |
                  rewrite restr_inter, inter_restr_absorb_r |
                  rewrite <- restr_seq |
                  rewrite restr_transp]
  end;
  repeat match goal with
           |- context[restr_rel ?D ?r] =>
           let X := fresh in
           assert (X: r ≡ ⦗D⦘ ⨾ r ⨾ ⦗D⦘) by auto with show_dom;
           rewrite <- restr_relE in X;
           rewrite <- X; clear X
         end; try done.


Variable G : execution.

Notation "'E'" := G.(acts).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co). (* PR: mo *)
Notation "'readpair'" := G.(readpair).
Notation "'writepair'" := G.(writepair).
Notation "'fenceonepair'" := G.(fenceonepair).
Notation "'fenceallpair'" := G.(fenceallpair).

Definition allpair := readpair ∪ writepair ∪ fenceonepair ∪ fenceallpair.

Definition rfe' := rf \ same_tid.

Definition sb := ⦗E⦘ ⨾ ext_sb ⨾ ⦗E⦘.

Definition poloc := sb ∩ same_loc.
Definition poch := sb ∩ same_ch.
Definition fr := rf⁻¹ ⨾ co \ ⦗fun _ => True⦘.
Definition fr' := (⦗R ∩₁ E⦘ ⨾ same_loc ⨾ ⦗W ∩₁ E⦘) \ (rf⁻¹ ⨾ (co⁻¹)^*).

Definition minus_event (A B: Event -> Prop) := fun a => A a /\ ~ B a.
Notation "'E' \ 'RdRsp'" := (minus_event E RdRsp).

Definition fre' := fr \ same_tid.
Definition rfr := ⦗fun x => ~ is_w x⦘ ⨾ rf⁻¹ ⨾ co.


Definition rfe := rf \ sb.
Definition coe := co \ sb.
Definition fre := fr \ sb.
Definition rfi := rf ∩ sb.
Definition coi := co ∩ sb.
Definition fri := fr ∩ sb.


Record Wf_fpga := {
  wf_readpairE: readpair ≡ ⦗E⦘ ⨾ readpair ⨾ ⦗E⦘ ;
  wf_readpairD: readpair ≡ ⦗RdReq⦘ ⨾ readpair ⨾ ⦗RdRsp⦘ ;
  wf_readpair_complete: E ∩₁ RdReq ⊆₁ dom_rel readpair ;
  wf_writepairE: writepair ≡ ⦗E⦘ ⨾ writepair ⨾ ⦗E⦘ ;
  wf_writepairD: writepair ≡ ⦗WrReq⦘ ⨾ writepair ⨾ ⦗WrRsp⦘ ;
  wf_writepair_complete: E ∩₁ WrReq ⊆₁ dom_rel writepair ;
  wf_fenceonepairE: fenceonepair ≡ ⦗E⦘ ⨾ fenceonepair ⨾ ⦗E⦘ ;
  wf_fenceonepairD: fenceonepair ≡ ⦗FnReqOne⦘ ⨾ fenceonepair ⨾ ⦗FnRspOne⦘ ;
  wf_fenceonepair_complete: E ∩₁ FnReqOne ⊆₁ dom_rel fenceonepair ;
  wf_fenceallpairE: fenceallpair ≡ ⦗E⦘ ⨾ fenceallpair ⨾ ⦗E⦘ ;
  wf_fenceallpairD: fenceallpair ≡ ⦗FnReqAll⦘ ⨾ fenceallpair ⨾ ⦗FnRspAll⦘ ;
  wf_fenceallpair_complete: E ∩₁ FnReqAll ⊆₁ dom_rel fenceallpair ;
}.

Record Wf :=
  { wf_index : forall a b,
    E a /\ E b /\ tid a = tid b /\ same_index a b /\ ~ is_init a -> a = b ;
    wf_rfE : rf ≡ ⦗E⦘ ⨾ rf ⨾ ⦗E⦘ ;
    wf_rfD : rf ≡ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘ ;
    wf_rfl : rf ⊆ same_loc ;
    wf_rfv : forall w r (RF: rf w r), valw w = valr r ;
    (* wf_rf_complete : E ∩₁ R ⊆₁ codom_rel rf ; *)
    wf_rff : functional rf⁻¹ ;
    wf_coE : co ≡ ⦗E⦘ ⨾ co ⨾ ⦗E⦘ ;
    wf_coD : co ≡ ⦗W⦘ ⨾ co ⨾ ⦗W⦘ ;
    wf_col : co ⊆ same_loc ;
    co_trans : transitive co ;
    wf_co_total : forall x, is_total (E ∩₁ W ∩₁ (fun a => loc a = x)) co ;
    co_irr : irreflexive co ;
    wf_initE : is_init ⊆₁ E ;
    wf_co_init : co ⨾ ⦗is_init⦘ ≡ ∅₂ ;
  }.


Definition fenceCpu := sb ⨾ ⦗CpuFence⦘ ⨾ sb.
Definition poFnRsp := (poch ⨾ ⦗FnRspOne⦘) ∪ (sb ⨾ ⦗FnRspAll⦘).
Definition fenceFpga := ⦗WrRsp⦘ ⨾ poFnRsp ⨾ sb ⨾ ⦗E \ RdRsp⦘.
Definition fence := fenceCpu ∪ fenceFpga.

Definition ppoCpu := (sb \ (W × R)) ∩ (Cpu × Cpu).
Definition ppoFpga := (⦗Rsp⦘ ⨾ poch ⨾ ⦗E \ RdRsp⦘) ∪ (⦗RdRsp⦘ ⨾ sb ⨾ ⦗E \ RdRsp⦘) ∪ allpair.
Definition ppo := ppoCpu ∪ ppoFpga.

(* add sb asyclic? *)
Record Ax86Consistent := {
    sc_per_loc: acyclic ((poloc ∪ rf ∪ co ∪ fr) ∩ (Cpu × Cpu));
    propagation: acyclic (ppo ∪ fence ∪ rfe ∪ fre ∪ co);
    read_after_write: irreflexive (fr ⨾ poch ⨾ readpair);
    read_after_fence: irreflexive (fr ⨾ poFnRsp ⨾ sb ⨾ readpair);
    no_read_from_future: irreflexive (rf ⨾ sb);
    observe_same_channel: irreflexive (fre ⨾ rfe ⨾ poch);
    fence_all_response: irreflexive (sb ⨾ fenceallpair ⨾ sb ⨾ writepair⁻¹);
    fence_one_response: irreflexive (poch ⨾ fenceonepair ⨾ sb ⨾ writepair⁻¹);
    fence_all_block: irreflexive (sb ⨾ writepair ⨾ sb ⨾ fenceallpair⁻¹);
    fence_one_block: irreflexive (poch ⨾ writepair ⨾ sb ⨾ fenceonepair⁻¹);
}.

Definition bounded_threads := exists n, forall x, E x -> match tid x with 
  | CpuTid t => t < n
  | _ => True
  end.
  
Definition rf_complete := E ∩₁ R  ⊆₁ codom_rel rf.
Definition mem_fair := fsupp co /\ fsupp fr.

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

Lemma LTS_trace_param' {State Label: Type} (lts: LTS State Label)
      st tr (LTS: LTS_trace_param lts st tr):
  LTS_init lts (st 0) /\
  (forall i,
      NOmega.lt_nat_l i (trace_length tr) ->
      forall d, LTS_step lts (st i) (trace_nth i tr d) (st (S i))).
Proof.
  destruct tr; simpl; vauto. red in LTS. desc. split; vauto.
Qed. 



Lemma sb_trans : transitive sb.
Proof using.
  unfold sb.
  rewrite <- restr_relE; apply transitive_restr, ext_sb_trans.
Qed.

Lemma sb_sb : sb ⨾ sb ⊆ sb.
Proof using.
  generalize sb_trans; basic_solver 21.
Qed.

Lemma sb_same_loc_trans: transitive (sb ∩ same_loc).
Proof using.
  apply restr_eq_trans, sb_trans.
Qed.

Definition hb := (sb ∪ rf)⁺.
Definition hb_sc := (sb ∪ rf ∪ co ∪ fr)⁺.
Definition eco := co ⨾ rf^? ∪ fr ⨾ rf^? ∪ rf.

Lemma hb_trans : transitive hb.
Proof using.
  unfold hb. apply transitive_ct.
Qed.

Lemma sb_in_hb : sb ⊆ hb.
Proof using.
  unfold hb. rewrite <- ct_step. eauto with hahn.
Qed.

Lemma sb_hb_cr_in_hb : sb ⨾ hb^? ⊆ hb.
Proof using. rewrite sb_in_hb. generalize hb_trans. basic_solver. Qed.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma sb_neq_loc_in_sb : sb \ same_loc ⊆ sb.
Proof using. basic_solver. Qed.

(******************************************************************************)
(** ** Same Location relations  *)
(******************************************************************************)

Implicit Type WF : Wf.

Lemma loceq_rf WF : funeq loc rf.
Proof using. apply WF. Qed.

Lemma loceq_co WF : funeq loc co.
Proof using. apply WF. Qed.

Hint Immediate loceq_rf loceq_co : core.

Lemma loceq_fr WF : funeq loc fr.
Proof using.
 eauto with hahn.
Qed.

Lemma loceq_rfr WF : funeq loc rfr.
Proof using.
  eauto with hahn.
Qed.

Lemma fr_fr' WF (C: rf_complete) : fr ≡ fr'.
Proof.
  split.
  { red; ins.
    unfold fr, fr' in *.
    destruct H.
    repeat destruct H.
    red; splits.
    { red in H.
      apply seq_eqv_lr.
      remember (loceq_rf WF x0 x H).
      remember (loceq_co WF x0 y H1).
      clear Heqe Heqe0.
      destruct WF.
      remember H as H'; clear HeqH'.
      apply wf_rfE0 in H.
      apply wf_rfD0 in H'.
      remember H1 as H1'; clear HeqH1'.
      apply wf_coE0 in H1.
      apply wf_coD0 in H1'.
      apply seq_eqv_lr in H, H1, H', H1'.
      splits; desf.
      red; lia. }
    red; ins.
    repeat destruct H2.
    red in H, H2.
    replace x1 with x0 in *.
    2: { fold (rf⁻¹ x x0) in H.
        fold (rf⁻¹ x x1) in H2.
        exact (wf_rff WF x x0 x1 H H2). }
    assert ((co⁻¹) x0 y).
    { destruct WF. 
      apply rt_of_trans in H3; vauto.
      2: { apply transitive_transp; basic_solver. }
      destruct H3.
      { subst. basic_solver. }
      auto. }
    red in H4.
    assert (antisymmetric co) by (apply trans_irr_antisymmetric; destruct WF; basic_solver).
    red in H5.
    remember (H5 x0 y H1 H4).
    destruct WF.
    subst.
    basic_solver. } 
  red; ins.
  red; red in H.
  red; destruct H.
  splits.
  2: { intro; red in H1; desf; subst; apply seq_eqv_lr in H. desf. red in H, H3; desf. red in H, H3; desf. }
  apply seq_eqv_lr in H.
  red in H0.
  destruct WF.
  assert (exists w, rf w x).
  { apply C. red; desf. cbv in *; desf. }
  desf.
  cut (co w y \/ (co⁻¹)＊ w y).
  2: { red in H2.
       cut (w = y \/ w <> y); [|by tauto].
       intro OR; destruct OR; [right; subst; apply rt_refl|].
       remember (wf_co_total0 (loc y)) as COT.
       forward eapply (COT w _ y _); auto.
       Unshelve.
       2: { assert (rf w x) as H1'; auto.
            apply wf_rfD0 in H1.
            apply wf_rfE0 in H1'.
            apply seq_eqv_lr in H1, H1'.
            split; desf.
            rewrite <- H2.
            destruct (wf_rfl0 w x H5); auto.
        }
       2: { destruct H3; split; desf. }
       ins; desf; auto.
       right.
       apply rt_step.
       auto.
   }
  ins.
  destruct H4.
  { red. exists w. splits; vauto. }
  exfalso; apply H0.
  red. exists w; splits; auto.
Qed.

Lemma wf_frl WF : fr ⊆ same_loc.
Proof using.
  red; ins.
  remember (loceq_fr WF H).
  unfold same_loc. exact e.
Qed.

Lemma wf_rfrl WF : rfr ⊆ same_loc.
Proof using.
  unfold rfr.
  rewrite (wf_rfl WF), (wf_col WF).
  unfolder; ins; desc; congruence.
Qed.


(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_sbE : sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘.
Proof using.
  unfold sb; basic_solver 42.
Qed.

Hint Resolve wf_sbE : show_dom.
Hint Immediate wf_rfE wf_coE : show_dom.

Lemma wf_frE WF : fr ≡ ⦗E⦘ ⨾ fr ⨾ ⦗E⦘.
Proof using. show_dom. Qed.
Hint Immediate wf_frE : show_dom.

Lemma wf_rfrE WF : rfr ≡ ⦗E⦘ ⨾ rfr ⨾ ⦗E⦘.
Proof using.
  apply dom_helper_2; unfold rfr.
  rewrite wf_rfE, wf_coE; ins.
  unfolder; ins; desf.
Qed.
Hint Immediate wf_rfrE : show_dom.

Lemma wf_hbE WF : hb ≡ ⦗E⦘ ⨾ hb ⨾ ⦗E⦘.
Proof using. show_dom. Qed.
Hint Immediate wf_frE : show_dom.

Lemma wf_hb_scE WF : hb_sc ≡ ⦗E⦘ ⨾ hb_sc ⨾ ⦗E⦘.
Proof using. show_dom. Qed.
Hint Immediate wf_hb_scE : show_dom.

Lemma wf_ct_rfE WF : (rf)⁺ ≡ ⦗E⦘ ⨾ (rf)⁺ ⨾ ⦗E⦘.
Proof using. show_dom. Qed.
Hint Immediate wf_ct_rfE : show_dom.

Lemma wf_ct_transp_rfE WF : (rf⁻¹)⁺ ≡ ⦗E⦘ ⨾ (rf^{-1})⁺ ⨾ ⦗E⦘.
Proof using. show_dom. Qed.
Hint Immediate wf_ct_transp_rfE : show_dom.

Lemma wf_sbhbcrE WF : sb ⨾ hb^? ⊆ ⦗acts G⦘ ⨾ sb ⨾ hb^? ⨾ ⦗acts G⦘.
Proof using. rewrite wf_sbE at 1. rewrite (wf_hbE WF) at 1. basic_solver 10. Qed.

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_frD WF : fr ≡ ⦗R⦘ ⨾ fr ⨾ ⦗W⦘.
Proof using.
  apply dom_helper_2; unfold fr.
  rewrite wf_rfD, wf_coD; ins.
  unfolder; ins; desf; intuition.
Qed.

Lemma wf_rfrD WF : rfr ≡ ⦗R \₁ W⦘ ⨾ rfr ⨾ ⦗W⦘.
Proof using.
  apply dom_helper_2; unfold rfr.
  rewrite wf_rfD, wf_coD; ins.
  unfolder; ins; desf.
Qed.


(******************************************************************************)
(** ** Irreflexive relations *)
(******************************************************************************)

Lemma sb_irr : irreflexive sb.
Proof using.
  unfold sb; unfolder; ins; desf.
  eby eapply ext_sb_irr.
Qed.

Lemma fr_irr WF : irreflexive fr.
Proof using.
  rewrite wf_frE; unfold fr; basic_solver.
Qed.

Lemma rfr_irr WF : irreflexive rfr.
Proof using.
  rewrite (wf_rfrD WF); ins; basic_solver.
Qed.

(******************************************************************************)
(** ** [fr] and [rfr] *)
(******************************************************************************)

Lemma rfr_in_fr WF :
  rfr ⊆ fr.
Proof using.
  rewrite wf_rfrD; ins;
    unfold fr, rfr; unfolder; ins; desf; splits; try intro; desf; eauto.
Qed.

Lemma read_not_write (x: Event):
  R x -> ~ W x.
Proof.
  intros; intro.
  unfold is_r, is_w in *; desf.
Qed.


Lemma frE WF (C : rf_complete):
  fr ≡ rfr ∪ ⦗R⦘ ⨾ co.
Proof using.
  rewrite wf_frE, wf_rfrE, wf_coE, wf_frD, wf_rfrD, wf_coD; ins.
  unfold fr, rfr; unfolder; split; ins; desf; clarify_not.
  {
    classical_left; clarify_not; eauto 10.
    cut (~ is_w x). eauto 20.
    intro.
    fold W in H7.
    eapply read_not_write; eauto.
  }
  splits; ins; eauto; try intro; desf.
  exfalso.
  by eapply read_not_write; eauto.
Qed.

Lemma w_fr_in_co WF (C : rf_complete) :
  ⦗is_w⦘ ⨾ fr ⊆ co.
Proof using. rewrite frE; auto. rewrite (wf_rfrD WF). basic_solver. Qed.

(******************************************************************************)
(** ** Acyclic relations *)
(******************************************************************************)

Lemma sb_acyclic : acyclic sb.
Proof using.
  apply trans_irr_acyclic; [apply sb_irr| apply sb_trans].
Qed.

Lemma co_acyclic WF: acyclic co.
Proof using.
  by apply trans_irr_acyclic; [apply co_irr| apply co_trans].
Qed.

(******************************************************************************)
(** ** init *)
(******************************************************************************)

Lemma init_w WF: is_init ⊆₁ W.
Proof using.
  unfolder; ins.
  unfold is_init in *; destruct x; desf.
Qed.

Lemma read_or_rmw_not_init WF a (A: R a) : ~ is_init a.
Proof using.
  intro.
  assert (W a) by (apply init_w; basic_solver).
  by eapply read_not_write; eauto.
Qed.

Lemma no_sb_to_init : sb ≡ sb ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
  split; [|basic_solver].
  unfold sb; rewrite ext_sb_to_non_init at 1; basic_solver.
Qed.

Lemma no_rf_to_init WF : rf ≡ rf ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
  split; [|basic_solver].
  rewrite (wf_rfD WF) at 1.
  rewrite (wf_rfE WF) at 1.
  generalize (read_or_rmw_not_init WF).
  basic_solver 42.
Qed.

Lemma no_hb_to_init WF : hb ≡ hb ⨾  ⦗fun x => ~ is_init x⦘.
Proof using.
  split; [|basic_solver].
  unfold hb.
  rewrite ct_end.
  rewrite (no_rf_to_init WF) at 2.
  rewrite no_sb_to_init at 2.
  basic_solver 42.
Qed.

Lemma init_same_loc a b
  (A: is_init a) (B: is_init b) (LOC: loc a = loc b):
  a = b.
Proof using.
  destruct a, b; desf.
  unfold loc in LOC.
    by cut (x = x0); [ins; subst|simpls].
Qed.

Lemma rf_init_r WF x y : rf x y -> is_init y -> False.
Proof using.
  ins; eapply (wf_rfD WF) in H; unfolder in *; desf.
  destruct y; ins.
Qed.

Lemma hb_init_r WF x y : hb x y -> is_init y -> False.
Proof.
  induction 1; unfold sb, ext_sb in *; unfolder in *;
    desf; eauto using rf_init_r.
Qed.

Lemma sb_hb_cr_init_empty WF : 
  (sb ⨾ hb^?) ⨾ ⦗is_init⦘ ⊆ ∅₂.
Proof using. rewrite sb_hb_cr_in_hb. generalize (hb_init_r WF). basic_solver. Qed.

Lemma co_init_l WF x y :
  is_init x -> is_w y -> (acts G \₁ is_init) y ->
  loc x = loc y -> co x y.
Proof.
  unfolder in *; ins; desc.
  assert (NEQ: x <> y) by (intro; desf).
  eapply wf_co_total in NEQ; eauto; unfolder; splits; ins; desf.
  - edestruct (proj1 (wf_co_init WF)). apply seq_eqv_r. split; eauto.  
  - apply wf_initE; ins.
  - destruct x; ins.
Qed.

Lemma rf_in_hb : rf ⊆ hb.
Proof using.
  unfold hb. rewrite <- ct_step. eauto with hahn.
Qed.


(******************************************************************************)
(** ** More properties *)
(******************************************************************************)

Lemma sb_semi_total_l x y z
  WF (N: ~ is_init x) (NEQ: y <> z) (XY: sb x y) (XZ: sb x z):
  sb y z \/ sb z y.
Proof using.
  unfold sb in *; unfolder in *; desf.
  cut (ext_sb y z \/ ext_sb z y); [basic_solver 12|].
  eapply ext_sb_semi_total_l; eauto.
  intro A.
  assert (y = z).
  eapply WF; splits; eauto.
    by unfold ext_sb in *; destruct y,z; ins; desf; desf.
    by unfold ext_sb in *; destruct y,z; ins; desf; desf.
  eauto.
Qed.

Lemma sb_semi_total_r x y z
  WF (N: ~ is_init z) (NEQ: y <> z) (XY: sb y x) (XZ: sb z x):
  sb y z \/ sb z y.
Proof using.
cut ((sb ∪ sb⁻¹) y z); [basic_solver|].
unfold sb in *; unfolder in *; desf.
destruct (classic (is_init y)).
unfold ext_sb; basic_solver.
cut (ext_sb y z \/ ext_sb z y); [basic_solver|].
eapply ext_sb_semi_total_r; eauto.
intro A.
assert (y = z).
eapply WF; splits; eauto.
by unfold ext_sb in *; destruct y,z; ins; desf; desf.
eauto.
Qed.

Lemma sb_tid_init x y (SB : sb x y): tid x = tid y \/ is_init x.
Proof using.
generalize ext_sb_tid_init; unfold sb in *.
unfolder in *; basic_solver.
Qed.

Lemma sb_tid_init': sb ≡ sb ∩ same_tid ∪ ⦗is_init⦘ ⨾ sb.
Proof using.
  split; [|basic_solver].
  unfold sb.
  rewrite ext_sb_tid_init' at 1.
  basic_solver 42.
Qed.


Lemma tid_sb WF: ⦗E⦘ ⨾ same_tid ⨾  ⦗E⦘ ⊆ sb^? ∪ sb⁻¹ ∪ (is_init × is_init).
Proof using.
  unfold sb.
  rewrite tid_ext_sb.
  unfolder; intuition.
  unfold same_tid, same_index in *.
  destruct x, y; ins; desf; eauto.
  repeat left; apply WF; splits; ins.
  repeat left; apply WF; splits; ins.
Qed.

Lemma tid_ninit_sb WF : ⦗E⦘ ⨾ same_tid ⨾ ⦗set_compl is_init⦘ ⨾ ⦗E⦘ ⊆ sb^? ∪ sb⁻¹.
Proof using.
  rewrite seq_eqvC; sin_rewrite tid_sb; ins.
  rewrite seq_union_l; apply inclusion_union_l; basic_solver.
Qed.

Lemma init_ninit_sb (WF : Wf) x y (INIT : is_init x) (ININE : E x) (INE : E y)
      (NINIT : ~ is_init y): sb x y.
Proof using.
  unfold sb, ext_sb; basic_solver.
Qed.

Lemma same_thread WF x y (X : E x) (Y : E y)
      (NINIT : ~ is_init x) (ST : tid x = tid y):
  sb^? x y \/ sb y x.
Proof using.
  eapply tid_ninit_sb; ins; unfolder; splits; ins.
  destruct x, y; ins; desf.
Qed.

Lemma sb_immediate_adjacent WF:
 ⦗set_compl is_init⦘ ⨾ immediate sb ≡ ⦗set_compl is_init⦘ ⨾ (adjacent sb ∩ sb).
Proof using.
apply immediate_adjacent.
- unfolder; ins; desf; destruct (classic (x=y)); auto.
  forward (apply (@sb_semi_total_r z y x)); eauto; tauto.
- unfolder; ins; desf; destruct (classic (x=y)); auto.
  forward (apply (@sb_semi_total_l z y x)); eauto; tauto.
- apply sb_trans.
- apply sb_irr.
Qed.

Lemma co_co WF: co ⨾ co ⊆ co.
Proof using. apply rewrite_trans, WF. Qed.

Lemma rel_ninit_l r (SUB: r ⊆ E × E) :
  ⦗E \₁ is_init⦘ ⨾ r ≡ ⦗set_compl is_init⦘ ⨾ r.
Proof using.
  unfolder in *; intuition; firstorder.
Qed.

Lemma sb_ninit_l :
  ⦗E \₁ is_init⦘ ⨾ sb ≡ ⦗set_compl is_init⦘ ⨾ sb.
Proof using.
  unfolder in *; intuition; firstorder.
Qed.

Lemma sb_ninit : sb ⨾ ⦗E \₁ is_init⦘  ≡ sb.
Proof using.
  unfold sb, ext_sb, is_init; unfolder; intuition; desf.
Qed.

Lemma rf_ninit WF : rf ⨾ ⦗E \₁ is_init⦘ ≡ rf.
Proof using.
  unfolder; intuition; desf.
  apply wf_rfE in H; unfolder in *; ins; desf.
  apply wf_rfD in H; unfolder in *; ins.
  unfold is_init, is_r in *; desf.
Qed.

Lemma co_ninit WF : co ⨾ ⦗E \₁ is_init⦘ ≡ co.
Proof using.
  unfolder; intuition; desf.
  apply wf_coE in H; unfolder in *; ins; desf.
  eapply wf_co_init; unfolder; eauto.
Qed.

Lemma fr_ninit WF : fr ⨾ ⦗E \₁ is_init⦘ ≡ fr.
Proof using.
  by unfold fr; rewrite <- seq_eqv_minus_lr, seqA, co_ninit.
Qed.

Lemma get_elem_cpu WF thread index :
  exists ! eo,
    match eo with
      None => forall l, ~ E (ThreadEvent thread index l)
    | Some (ThreadEvent t i l) =>
      E (ThreadEvent t i l) /\ t = thread /\ i = index
    | Some (InitEvent _) => False
    | Some (FpgaEvent l i m) => False
    end.
Proof using.
  ins; tertium_non_datur (exists lab, E (ThreadEvent thread index lab)) as [X|X]; desc.
  exists (Some (ThreadEvent thread index lab)); split; ins; desf; desf;
      [|by edestruct H; eauto].
    now f_equal; eapply (wf_index WF); splits; ins.
  exists None; split; try red; ins; desf; desf; exfalso; eauto.
Qed.

Lemma get_elem_fpga WF index:
  exists ! eo,
    match eo with
      None => forall l meta, ~ E (FpgaEvent l index meta)
    | Some (ThreadEvent t i l) => False
    | Some (InitEvent _) => False
    | Some (FpgaEvent l i m) => 
      E (FpgaEvent l i m) /\ i = index
    end.
Proof using.
  ins; tertium_non_datur (exists lab meta, E (FpgaEvent lab index meta)) as [X|X]; desc.
  exists (Some (FpgaEvent lab index meta)); split; ins; desf; desf;
      [|by edestruct H; eauto].
    now f_equal; eapply (wf_index WF); splits; ins.
  exists None; split; try red; ins; desf; desf; exfalso; eauto.
Qed.

Lemma get_elem WF thread index :
  exists ! eo,
    match eo with
      None => match thread with 
                CpuTid t => forall l, ~ E (ThreadEvent t index l)
              | FpgaTid => forall l meta, ~ E (FpgaEvent l index meta)
              | InitTid => True
              end
    | Some (ThreadEvent t i l) =>
      E (ThreadEvent t i l) /\ (CpuTid t) = thread /\ i = index
    | Some (InitEvent _) => False
    | Some (FpgaEvent l i m) => 
      E (FpgaEvent l i m) /\ i = index /\ thread = FpgaTid
    end.
Proof using.
  ins.
  destruct thread as [t| |].
  { remember (get_elem_cpu WF t index) as X.
    destruct X as [X Y]. destruct Y.
    exists X. split; ins; desf; desf; eauto. }
  { remember (get_elem_fpga WF index) as X.
    destruct X as [X Y]. destruct Y.
    exists X. split; ins; desf; desf; eauto. }
  exists None. split; ins; desf; desf; eauto.
Qed.

Lemma fsupp_sb WF : fsupp (⦗set_compl is_init⦘ ⨾ sb).
Proof using.
  unfold sb, ext_sb; unfolder; ins.
  destruct y.
  3: { exists nil; ins; desf. } 
  { assert (X := get_elem_cpu WF thread); desc.
  eapply unique_choice in X; desc.
  exists (map_filter f (List.seq 0 index)); ins; desf; desf.
  rewrite in_map_filter; exists index0; specialize (X index0).
  rewrite in_seq0_iff; desf; desf; split; ins; [|edestruct X; edone].
  by f_equal; eapply (wf_index WF); splits; ins. }
  { assert (X := get_elem_fpga WF); desc.
  eapply unique_choice in X; desc.
  exists (map_filter f (List.seq 0 index)); ins; desf; desf.
  rewrite in_map_filter; exists index0; specialize (X index0).
  rewrite in_seq0_iff; desf; desf; split; ins; [|edestruct X; edone].
  by f_equal; eapply (wf_index WF); splits; ins. }
Qed.

Lemma fsupp_rf WF : fsupp rf.
Proof using. destruct WF; eauto with hahn. Qed.

Lemma fsupp_co (F : mem_fair) : fsupp co.
Proof using. apply F. Qed.

Lemma fsupp_fr (F : mem_fair) : fsupp fr.
Proof using. apply F. Qed.

Lemma fsupp_rfr WF (F : mem_fair) : fsupp rfr.
Proof using.
  rewrite rfr_in_fr; ins; apply F.
Qed.

Hint Immediate fsupp_sb fsupp_rf fsupp_co fsupp_fr fsupp_rfr : core.

Lemma fsupp_eco WF (FAIR : mem_fair) : fsupp eco.
Proof using. eauto 8 with hahn. Qed.

Hint Immediate fsupp_eco : core.

Lemma fsupp_hb WF (FAIR : mem_fair)
        (IRRhb: irreflexive hb)
        (THREADS: has_finite_antichains (E \₁ is_init) (⦗set_compl is_init⦘ ⨾ sb)) :
  fsupp (⦗set_compl is_init⦘ ⨾ hb).
Proof using.
  rewrite <- rel_ninit_l; [|rewrite wf_hbE; unfolder; tauto].
  unfold hb.
  arewrite (⦗E \₁ is_init⦘ ⨾ (sb ∪ rf)⁺ ≡
             (⦗E \₁ is_init⦘ ⨾ (sb ∪ rf))⁺)
    by rewrite ct_rotl, seq_union_l, sb_ninit, rf_ninit, ct_end.
  rewrite seq_union_r.
  eapply fsupp_ct, fsupp_union; ins; eauto.
  - by rewrite 2!inclusion_seq_eqv_l.
  - apply union_doma; apply seq_doma, eqv_doma.
  - by rewrite <- inclusion_union_r1, sb_ninit_l.
  - rewrite sb_ninit_l; eauto.
  - by rewrite inclusion_seq_eqv_l; eauto.
Qed.


Lemma dupE A (l : list A) (DUP: ~ NoDup l) :
  exists l1 a l2 l3, l = l1 ++ a :: l2 ++ a :: l3.
Proof using.
  induction l; ins.
  rewrite nodup_cons in *; clarify_not.
    by apply in_split in DUP; desf; exists nil; ins; eauto.
  specialize (IHl DUP); desf; eexists (_ :: _); ins; eauto.
Qed.


(* Lemma has_finite_antichains_sb WF (B: bounded_threads) :
  has_finite_antichains (E \₁ is_init) (⦗set_compl is_init⦘ ⨾ sb).
Proof using.
  (* destruct B as [n THR]; exists n; red; ins; unfolder in *.
  cut (exists a b, a <> b /\ In a l /\ In b l /\ tid a = tid b).
  { intro X; desc.
    destruct (INCL _ X0); destruct (INCL _ X1); desc.
    eapply same_thread in X2; unfolder in X2; desf.
    exists a, b; splits; eauto.
    exists b, a; splits; eauto. }
  assert (M: incl (map tid l) (cons FpgaTid (map CpuTid (List.seq 0 n)))).
    red; ins; rewrite in_map_iff in *. desf.
    by apply in_seq0_iff, THR, INCL.
  destruct (classic (NoDup (map tid l))).
  { eapply NoDup_incl_length in M; ins.
    rewrite length_map, length_seq in *; lia. }
  apply dupE in H; desf.
  apply map_eq_app_inv in H; desf.
  destruct l2'; ins; desf.
  apply map_eq_app_inv in H0; desf.
  destruct l2'0; ins; desf.
  exists e0, e; splits; eauto with hahn.
  intro; desf; rewrite nodup_app, nodup_cons in *; desf; eauto with hahn.
Qed.
*)

(* Hint Resolve has_finite_antichains_sb : core. *)

(* Lemma countable_ninit WF : countable (E \₁ is_init).
Proof using.
  (* assert (X := unique_choice _ (fun ti => get_elem WF (nat_fst ti) (nat_snd ti)));
    desc.
  assert (F := unique_choice _ (fun ti => get_elem_fpga WF ti));
    desc. *)
  assert (X := unique_choice _ (fun ti => get_elem WF (fst ti) (snd ti)));
    desc.
  assert (default: Event) by vauto.
  apply surjection_countable with
      (f := fun n => match f n with Some e => e | None => default end).
  unfolder; ins; desf; destruct a; ins.
  { exists (nat_tup thread index); specialize (X (nat_tup thread index)); desf; desf.
    rewrite nat_fst_tup, nat_snd_tup in *; eapply (wf_index WF); splits; ins.
    eby edestruct X; rewrite nat_fst_tup, nat_snd_tup. }
  exists index; specialize (F index); desf; desf.
    eapply (wf_index WF); splits; ins.
Qed.

Lemma exec_exists_enum WF (FAIR: mem_fair)
      (r : relation Event) (IRR: irreflexive r)
      (TRANS: transitive r) (FSUPP: fsupp (⦗set_compl is_init⦘ ⨾ r)) :
  exists nu,
    enumerates nu (E \₁ is_init) /\
    (forall i (LTi: lt_size i (E \₁ is_init))
            j (LTj: lt_size j (E \₁ is_init))
             (REL: r (nu i) (nu j)), i < j).
Proof using.
  forward apply countable_ninit as X; ins.
  eapply countable_ext with (s := E \₁ is_init) in X; eauto.
  2: split; [ by rewrite inclusion_seq_eqv_l |
              by unfolder; split; desf; eauto ].
  desf; [by destruct X; repeat constructor|].
  exists f; split; ins; eapply X0; eauto.
  unfolder; split; ins.
  intro NINIT; rewrite enumeratesE in X; desc.
  eapply RNG in LTi; unfolder in LTi; desf.
Qed. *) *)


(******************************************************************************)
(** ** external-internal restrictions *)
(******************************************************************************)

(* Definition rfe := rf \ sb. *)
(* Definition coe := co \ sb. *)
(* Definition fre := fr \ sb. *)
(* Definition rfi := rf ∩ sb. *)
(* Definition coi := co ∩ sb. *)
(* Definition fri := fr ∩ sb. *)

Lemma ri_union_re r : r ≡ r ∩ sb ∪ r \ sb.
Proof using. unfolder; split; ins; desf; tauto. Qed.

Lemma rfi_union_rfe : rf ≡ rfi ∪ rfe.
Proof using. apply ri_union_re. Qed.
Lemma coi_union_coe : co ≡ coi ∪ coe.
Proof using. apply ri_union_re. Qed.
Lemma fri_union_fre : fr ≡ fri ∪ fre.
Proof using. apply ri_union_re. Qed.

Lemma ri_dom r d1 d2 (DOM: r ≡ ⦗d1⦘ ⨾ r ⨾ ⦗d2⦘) : r ∩ sb ⊆ ⦗d1⦘ ⨾ r ∩ sb ⨾ ⦗d2⦘.
Proof using. rewrite DOM at 1; basic_solver. Qed.
Lemma re_dom r d1 d2 (DOM: r ≡ ⦗d1⦘ ⨾ r ⨾ ⦗d2⦘) : r \ sb ⊆ ⦗d1⦘ ⨾ (r \ sb) ⨾ ⦗d2⦘.
Proof using. rewrite DOM at 1; basic_solver. Qed.

Lemma wf_rfiE WF: rfi ≡ ⦗E⦘ ⨾ rfi ⨾ ⦗E⦘.
Proof using. show_dom. Qed.
Lemma wf_coiE WF: coi ≡ ⦗E⦘ ⨾ coi ⨾ ⦗E⦘.
Proof using. show_dom. Qed.
Lemma wf_friE WF: fri ≡ ⦗E⦘ ⨾ fri ⨾ ⦗E⦘.
Proof using. show_dom. Qed.
Lemma wf_rfeE WF: rfe ≡ ⦗E⦘ ⨾ rfe ⨾ ⦗E⦘.
Proof using. show_dom. Qed.
Lemma wf_coeE WF: coe ≡ ⦗E⦘ ⨾ coe ⨾ ⦗E⦘.
Proof using. show_dom. Qed.
Lemma wf_freE WF: fre ≡ ⦗E⦘ ⨾ fre ⨾ ⦗E⦘.
Proof using. show_dom. Qed.
Lemma wf_rfiD WF : rfi ≡ ⦗W⦘ ⨾ rfi ⨾ ⦗R⦘.
Proof using. split; [|basic_solver]. apply ri_dom, (wf_rfD WF). Qed.
Lemma wf_coiD WF : coi ≡ ⦗W⦘ ⨾ coi ⨾ ⦗W⦘.
Proof using. split; [|basic_solver]. apply ri_dom, (wf_coD WF). Qed.
Lemma wf_friD WF : fri ≡ ⦗R⦘ ⨾ fri ⨾ ⦗W⦘.
Proof using. split; [|basic_solver]. apply ri_dom, (wf_frD WF). Qed.
Lemma wf_rfeD WF : rfe ≡ ⦗W⦘ ⨾ rfe ⨾ ⦗R⦘.
Proof using. split; [|basic_solver]. apply re_dom, (wf_rfD WF). Qed.
Lemma wf_coeD WF : coe ≡ ⦗W⦘ ⨾ coe ⨾ ⦗W⦘.
Proof using. split; [|basic_solver]. apply re_dom, (wf_coD WF). Qed.
Lemma wf_freD WF : fre ≡ ⦗R⦘ ⨾ fre ⨾ ⦗W⦘.
Proof using. split; [|basic_solver]. apply re_dom, (wf_frD WF). Qed.

(******************************************************************************)
(** ** properties of external/internal relations *)
(******************************************************************************)

Lemma seq_ii r1 r2 r3 (A: r1 ⨾ r2 ⊆ r3): r1 ∩ sb ⨾ r2 ∩ sb ⊆ r3 ∩ sb.
Proof using.
generalize sb_trans.
unfolder in *; basic_solver 21.
Qed.

Lemma re_ri WF  r r' (IRR: irreflexive r)  (IRR2: irreflexive (r ⨾ sb))
  (N: r ⊆ r ⨾  ⦗ fun x => ~ is_init x ⦘): (r \ sb) ⨾ (r' ∩ sb) ⊆ r ⨾  r' \ sb.
Proof using.
rewrite N at 1.
unfolder; ins; desf; splits; eauto.
intro.
eapply sb_semi_total_r with (x:=y) (y:=x) in H1; eauto.
by desf; revert IRR2; basic_solver.
eby intro; subst; eapply IRR.
Qed.

Lemma ri_re WF  r r' (IRR: irreflexive r')  (IRR2: irreflexive (r' ⨾ sb)):
 ⦗ fun x => ~ is_init x ⦘ ⨾ (r ∩ sb) ⨾ (r' \ sb) ⊆ r ⨾  r' \ sb.
Proof using.
unfolder; ins; desf; splits; eauto.
intro.
eapply sb_semi_total_l with (x:=x) (y:=z) (z:=y) in H4; eauto.
by desf; revert IRR2; basic_solver.
eby intro; subst; eapply IRR.
Qed.

Lemma rfi_in_sbloc WF : rf ∩ sb ⊆ restr_eq_rel loc sb.
Proof using. rewrite wf_rfl; basic_solver 12. Qed.
Lemma coi_in_sbloc WF : co ∩ sb ⊆ restr_eq_rel loc sb.
Proof using. rewrite wf_col; basic_solver 12. Qed.
Lemma fri_in_sbloc WF : fr ∩ sb ⊆ restr_eq_rel loc sb.
Proof using. rewrite (funeq_same_loc fr (loceq_fr WF)).
unfolder; unfold Events.same_loc in *.
ins; desf; splits; eauto; congruence.
Qed.
Lemma rfi_in_sbloc' WF : rfi ⊆ sb ∩ same_loc.
Proof using. generalize (wf_rfl WF); unfold rfi; basic_solver 12. Qed.
Lemma coi_in_sbloc' WF : coi ⊆ sb ∩ same_loc.
Proof using. generalize (wf_col WF); unfold coi; basic_solver 12. Qed.
Lemma fri_in_sbloc' WF : fri ⊆ sb ∩ same_loc.
Proof using. generalize (wf_frl WF); unfold fri; basic_solver 12. Qed.

End Execution.

(******************************************************************************)
(** ** Tactics *)
(******************************************************************************)
#[global]
Hint Unfold rfe coe fre rfi coi fri : ie_unfolderDb.
Tactic Notation "ie_unfolder" :=  repeat autounfold with ie_unfolderDb in *.

