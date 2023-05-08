Require Import Events.
Require Import Execution.
Require Import Labels.
Require Import TSOFPGA.
Require Import Lia.
Require Import Arith.
Require Import IndefiniteDescription.
Require Import PropExtensionality.
Require Import List.
Require Import AuxProp.
Require Import AuxRel.
Import ListNotations.
From hahn Require Import Hahn.

Section CounterExample.

Definition w1 := FpgaEvent (Fpga_write_req 1 0 1) 0 0.
Definition f1 := FpgaEvent (Fpga_fence_req_one 1) 1 1.
Definition f2 := FpgaEvent (Fpga_fence_req_one 2) 2 2.
Definition w2 := FpgaEvent (Fpga_write_req 2 0 2) 3 3.
Definition f2_resp := FpgaEvent (Fpga_fence_resp_one 2) 4 2.
Definition w2_resp := FpgaEvent (Fpga_write_resp 2 0 2) 5 3.
Definition w1_resp := FpgaEvent (Fpga_write_resp 1 0 1) 6 0.
Definition f1_resp := FpgaEvent (Fpga_fence_resp_one 1) 7 1.

Definition event_list := [w1; f1; f2; w2; w1_resp; f1_resp; f2_resp; w2_resp].
Definition EG := fun e => In e event_list \/ is_init e.

Definition exec_rf := fun (e1 e2: Event) => False.
Definition exec_co := fun e1 e2 => 
    ((is_init e1 /\ e2 = w1_resp) \/
    (e1 = w2_resp /\ e2 = w1_resp) \/
    (is_init e1 /\ e2 = w2_resp)) /\ same_loc e1 e2.

Definition G :=
  {| acts := EG;
     co := exec_co;
     rf := exec_rf;
     readpair := ⦗EG ∩₁ is_rd_req⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_rd_resp⦘;
     writepair := ⦗EG ∩₁ is_wr_req⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_wr_resp⦘;
     fenceonepair := ⦗EG ∩₁ is_fence_req_one⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_fence_resp_one⦘;
     fenceallpair := ⦗EG ∩₁ is_fence_req_all⦘ ⨾ req_resp_pair ⨾ ⦗EG ∩₁ is_fence_resp_all⦘
     |}.

Ltac unfolder'' := unfolder; unfolder'; unfold EG, exec_rf, exec_co, is_init, same_loc in *; simpl in *.

Lemma WFG: Wf G.
Proof.
    split; ins; desf.
    all: try by (unfolder''; split; ins; desf; auto 20).
    all: try by (unfolder''; ins; desf; auto 20).
Qed.

Lemma WF_FPGA_G: Wf_fpga G.
Proof.
    split; ins; desf.
    all: try basic_solver.
    (* - red; split; red. ins. apply seq_eqv_lr in H. apply seq_eqv_lr; unfolder''; desf. intuition. eauto 10. *)
    all: try by (unfolder''; ins; desf).
    - unfolder''. ins; desf.
        { exists w1_resp; intuition; desf; unfold w1, w1_resp in *; desf. }
        { exists w2_resp. intuition; desf; unfold w2, w2_resp in *; desf. } 
    - unfolder''. ins; desf.
        { exists f1_resp; intuition; desf; unfold f1, f1_resp in *; desf. }
        { exists f2_resp. intuition; desf; unfold f2, f2_resp in *; desf. }
Qed.

Ltac unfolder''' := unfold poloc, fr, rf, co, sb, exec_rf, exec_co, same_loc, is_init, is_cpu, ext_sb in *.
Ltac unfold_nodes := unfold w1, w2, f1, f2, w1_resp, w2_resp, f1_resp, f2_resp in *.

Lemma rf_empty: rf G ⊆ ∅₂.
Proof.
simpl; vauto.
Qed.

Lemma fr_empty: fr G ⊆ ∅₂.
Proof.
    red; ins; red in H.
    repeat destruct H.
Qed.

Lemma ppoCpu_empty: ppoCpu G ⊆ ∅₂.
Proof.
    red; ins; red in H.
    destruct H.
    destruct H, H0.
    apply seq_eqv_lr in H.
    desf; simpl in *.
    unfold EG, is_cpu in *; simpl in *; desf.
Qed.

Lemma fence_empty: fence G ⊆ ∅₂.
Proof.
    red; ins; red in H.
    destruct H.
    { red in H; destruct H. destruct H. destruct H0.
      destruct H0.
      red in H0; destruct H0; subst.
      apply seq_eqv_lr in H.
      simpl in *; destruct H; unfold EG, is_cpu_fence in *; simpl in *; desf. }
    red in H.
    repeat destruct H.
    destruct H0.
    destruct H.
    destruct H0.
    destruct H0.
    repeat destruct H2.
    (* unfold poFnRsp in *. *)
    apply seq_eqv_lr in H0.
    desf; simpl in *.
    red in H3; desf.
    destruct H.
    { destruct H as [x0' [POCH FN_ONE]].
      repeat destruct FN_ONE; subst.
      destruct POCH as [SB SCH].
      apply seq_eqv_lr in SB.
      destruct SB as [EGX [SB _]].
      simpl in *.
      unfold is_fence_resp_one in *.
      unfold ext_sb in *.
      unfold EG in H0; simpl in *; desf;
      unfold_nodes;
      unfold same_ch, chan_opt, fpga_chan_opt in *;
      unfold EG in EGX; simpl in *; desf; unfold_nodes; desf;
      unfold EG in H3; simpl in *; desf; unfold_nodes; desf; lia. }

    destruct H as [x0' [SB FN_ALL]].
    repeat destruct FN_ALL; subst.
    apply seq_eqv_lr in SB.
    destruct SB as [EGX [SB _]].
    simpl in *.
    unfold is_fence_resp_all in *.
    unfold ext_sb in *.
    unfold EG in H0; simpl in *; desf;
    unfold_nodes;
    unfold same_ch, chan_opt, fpga_chan_opt in *;
    unfold EG in EGX; simpl in *; desf; unfold_nodes; desf;
    unfold EG in H3; simpl in *; desf; unfold_nodes; desf; lia.
Qed.


(* Lemma ppoFpga_lemma: ppoFpga G ⊆ ⦗fun e => e <> r0_resp⦘ ⨾ (ppoFpga G) ⨾ ⦗fun e => e <> r0_resp⦘ ∪ (fun e1 e2 => e1 = r0 /\ e2 = r0_resp).
Proof.
  red; ins; desf.
  remember H as H'.
  clear HeqH'.
  red in H.
  destruct H as [[POCH | SB] | PAIR].
  { apply seq_eqv_lr in POCH.
    left; apply seq_eqv_lr.
    destruct POCH as [RSP [[SB SCH] NOTR]].
    apply seq_eqv_lr in SB.
    simpl in *; desf.
    unfold ext_sb, is_resp, minus_event, is_rd_resp in *.
    splits; vauto;
    intro; subst;
    unfold EG in *; simpl in *; desf; unfold_nodes; desf; lia.
   }
  { apply seq_eqv_lr in SB.
    left; apply seq_eqv_lr.
    destruct SB as [RSP [SB NOTR]].
    apply seq_eqv_lr in SB.
    simpl in *; desf.
    unfold ext_sb, is_resp, minus_event, is_rd_resp in *.
    splits; vauto;
    intro; subst;
    unfold EG in *; simpl in *; desf; unfold_nodes; desf; lia.
   }
   red in PAIR.
   destruct PAIR as [[[RP | P] | P] | P].
   { right. simpl in *. apply seq_eqv_lr in RP.
     desf; unfold EG in *; unfolder'; simpl in *; desf. }
    all: 
    (left; simpl in *; apply seq_eqv_lr in P;
    desf; apply seq_eqv_lr; splits; vauto; intro; subst;
    unfold EG in *; unfolder'; simpl in *; desf).
Qed. *)

Lemma fenceallpair_empty: fenceallpair G ⊆ ∅₂.
Proof.
  red; ins; apply seq_eqv_lr in H.
  desf; unfolder''; desf.
Qed.

Lemma Consistent: Ax86Consistent G.
Proof.
    split.
    {
        cut ((poloc G ∪ rf G ∪ co G ∪ fr G) ∩ is_cpu × is_cpu ⊆ ∅₂).
        { ins. rewrite H. red. rewrite tc_empty. basic_solver. }
        repeat (rewrite inter_union_l).
        red; ins; desf. destruct H. destruct H. destruct H.
        destruct H. red in H. 
        - destruct H, H0. unfolder'''. apply seq_eqv_lr in H. simpl in *. unfold EG in *. simpl in *; desf.
        - destruct H, H0. unfolder'''. simpl in *. unfold EG in *. simpl in *; desf.
        - destruct H, H0. unfolder'''. simpl in *. unfold EG in *. simpl in *; desf.
        - destruct H, H0. red in H. do 3 (destruct H). red in H. simpl in *. unfolder'''. simpl in *. unfold EG in *. simpl in *; desf. }
    {
        unfold ppo.
        rewrite ppoCpu_empty.
        rewrite fence_empty.
        arewrite (rfe G ⊆ rf G).
        arewrite (fre G ⊆ fr G).
        rewrite fr_empty.
        rewrite rf_empty.
        rewrite !(union_false_l).
        rewrite !union_false_r.
        arewrite (ppoFpga G ∪ co G ⊆ co G ∪ ppoFpga G).
        
        apply acyclic_union.
        { apply (co_acyclic WFG). }
        rewrite (wf_coD WFG).
        apply acyclic_disj.
        red; ins.
        admit.
       }
    all: try by (rewrite fr_empty; repeat (rewrite seq_false_l); basic_solver).
    { rewrite rf_empty.
      basic_solver. }
    { arewrite (fre G ⊆ fr G); rewrite fr_empty; basic_solver. }
    { rewrite fenceallpair_empty; basic_solver. }
    2: { rewrite fenceallpair_empty; basic_solver. }
    { red; ins.
      destruct H as [x0 [POCH [x1 [FENCE [x2 [SB PAIR]]]]]].
      apply seq_eqv_lr in FENCE.
      apply seq_eqv_lr in PAIR.
      apply seq_eqv_lr in SB.
      destruct POCH as [SB' SCH].
      apply seq_eqv_lr in SB'.
      simpl in *.
      desf.
      destruct FENCE, FENCE1.
      unfold EG in H1, SB1.
      simpl in *.
      red in H0, FENCE0, H2.
      red in SB0.
      destruct PAIR, PAIR1.
      unfold w1, w1_resp, f1, f1_resp, w2, w2_resp, f2, f2_resp, is_init in *.
      destruct x0, x1; desf; try lia.
      { destruct FENCE0; subst.
        unfold EG in SB'0, SB'1.
        simpl in *.
        desf.
        unfold f2 in *.
        desf.
        unfold EG in SB'.
        simpl in *.
        unfold ext_sb, same_ch, chan_opt, fpga_chan_opt in *;  simpl in *;  desf.
        unfold w2 in *; desf. lia. }
      destruct FENCE0; subst.
      unfold EG in SB'0, SB'1.
      simpl in *.
      desf.
      unfold f2 in *.
      desf.
      unfold EG in SB'.
      simpl in *.
      unfold ext_sb, same_ch, chan_opt, fpga_chan_opt in *;  simpl in *;  desf.
      unfold w2 in *; desf; lia. }
    { red; ins.
      destruct H as [x0 [POCH [x1 [PAIR [x2 [SB FENCE]]]]]].
      apply seq_eqv_lr in FENCE.
      apply seq_eqv_lr in PAIR.
      apply seq_eqv_lr in SB.
      destruct POCH as [SB' SCH].
      apply seq_eqv_lr in SB'.
      simpl in *.
      desf.
      destruct FENCE, FENCE1.
      unfold EG in H1, SB1.
      simpl in *.
      red in H0, FENCE0, H2.
      red in SB0.
      destruct PAIR, PAIR1.
      unfold w1, w1_resp, f1, f1_resp, w2, w2_resp, f2, f2_resp, is_init in *.
      destruct x0, x1; desf; try lia.
      { unfold ext_sb in *.
        unfold EG in SB'; simpl in *; desf.
        unfold ext_sb, same_ch, chan_opt, fpga_chan_opt in *;  simpl in *;  desf.
        unfold EG in SB'1; simpl in *; desf.
        unfold w1 in *; desf; lia. }
      unfold ext_sb in *.
      unfold EG in SB'; simpl in *; desf.
      unfold ext_sb, same_ch, chan_opt, fpga_chan_opt in *;  simpl in *;  desf.
      unfold EG in SB'1; simpl in *; desf.
      unfold w2, f2 in *; desf.
      unfold EG in H5; simpl in *; desf.
      unfold w2_resp in *; desf. lia. }
Admitted.

Lemma Valid_execution:
  Wf_fpga G /\ Wf G /\
  Ax86Consistent G.
Proof.
  splits.
  - apply WF_FPGA_G.
  - apply WFG.
  - apply Consistent.
Qed.

End CounterExample.