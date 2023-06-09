Require Import Events.
Require Import Labels.
Require Import Execution.
Require Import List.
From hahn Require Import Hahn. 
Require Import Lia.

Section TSOFPGA.

Definition shared_memory := Loc -> Val.  
Definition buffer := list (Loc * Val).

Inductive latest_buffered (buf: buffer) (loc: Loc) (opt_val: option Val) : Prop :=
  | no_loc_buffer
      (EMPTY_BUF: filter (fun loc_val: Loc * Val => Nat.eqb (fst loc_val) loc) buf = nil)
      (NO_LATEST: opt_val = None)
  | latest_loc
      val
      (LATEST_VALUE: opt_val = Some val)
      (LATEST_BUF:
         let buf_thread_loc := filter (fun loc_val: Loc * Val => Nat.eqb (fst loc_val) loc) buf in
         Some (loc, val) = nth_error buf_thread_loc (length buf_thread_loc - 1)). 


Inductive WritePoolEntry :=
| store_wp (c:Chan) (l: Loc) (v: Val)
| fence_ch_wp (c:Chan)
| fence_all_wp.

Inductive UpstreamEntry :=
| store_up (l: Loc) (v: Val)
| read_up (l: Loc).


Inductive SyLabel := 
  | EventLab (e: Event)
  | CpuFlush (thread: nat)
  | FpgaMemRead (c: Chan) (l: Loc) (v: Val) (m: Mdata)
  | FpgaMemFlush (c: Chan) (l: Loc) (v: Val) (m: Mdata)
  | FpgaReadToUpstream (c: Chan) (l: Loc) (m: Mdata).


Definition RPool := list (Chan * Loc * Mdata).
Definition WPool := list (WritePoolEntry * Mdata).
Definition UpsBuf := list (UpstreamEntry * Mdata).
Definition UpsBufs := Chan -> UpsBuf.
Definition DownsBuf := list (Loc * Val * Mdata).
Definition DownsBufs := Chan -> DownsBuf.

Record SyState := mkState {
  w_pool: WPool;
  r_pool: RPool;
  up_bufs: UpsBufs;
  down_bufs: DownsBufs;
  sh_mem: shared_memory;
  cpu_bufs: nat -> buffer
}.



Inductive match_ev (e : Event) (l : SyLabel) : Prop :=
| ME_cpu t i cpuE (EQe : e = ThreadEvent t i cpuE)
          (EQl : l = EventLab e)
| ME_fpga fpgaE i mdata (EQe : e = FpgaEvent fpgaE i mdata)
          (EQl : l = EventLab e).

(* Definiton chan a := match a with
  | ThreadEvent _ _ _ => 0
  | FpgaEvent e _ => fpga_chan e
end. *)


Inductive TSOFPGA_step: SyState -> SyLabel -> SyState -> Prop :=
| fpga_write_req w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs loc val channel meta index:
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (FpgaEvent (Fpga_write_req channel loc val) index meta))
                 (mkState (w_pool ++ cons ((store_wp channel loc val), meta) nil) r_pool up_bufs down_bufs sh_mem cpu_bufs)
| fpga_read_req w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs loc channel meta index:
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (FpgaEvent (Fpga_read_req channel loc) index meta))
                 (mkState w_pool (r_pool ++ cons (channel, loc, meta) nil) up_bufs down_bufs sh_mem cpu_bufs)
| fpga_fence_req_one w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs channel meta index:
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (FpgaEvent (Fpga_fence_req_one channel) index meta))
                 (mkState (w_pool ++ cons ((fence_ch_wp channel), meta) nil) r_pool up_bufs down_bufs sh_mem cpu_bufs)
| fpga_fence_req_all w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs meta index:
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (FpgaEvent (Fpga_fence_req_all) index meta))
                 (mkState (w_pool ++ cons ((fence_all_wp), meta) nil) r_pool up_bufs down_bufs sh_mem cpu_bufs)
| fpga_flush_write w_pool head tail r_pool up_bufs down_bufs sh_mem cpu_bufs loc val channel meta index
      (WRITE_POOL: w_pool = head ++ cons ((store_wp channel loc val), meta) tail)
      (NO_FENCE_ONE: forall meta', ~ In ((fence_ch_wp channel), meta') head)
      (NO_FENCE_ALL: forall meta', ~ In ((fence_all_wp), meta') head):
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (FpgaEvent (Fpga_write_resp channel loc val) index meta))
                 (mkState (head ++ tail) r_pool (upd up_bufs channel (up_bufs channel ++ cons (store_up loc val, meta) nil)) down_bufs sh_mem cpu_bufs)
| fpga_mem_write w_pool r_pool up_bufs up_buf' down_bufs sh_mem cpu_bufs loc val channel meta
      (UPSTREAM: up_bufs channel = cons ((store_up loc val), meta) up_buf'):
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (FpgaMemFlush channel loc val meta)
                 (mkState w_pool r_pool (upd up_bufs channel up_buf') down_bufs (upd sh_mem loc val) cpu_bufs)
| fpga_fence_resp_one channel meta w_pool w_pool' r_pool up_bufs down_bufs sh_mem cpu_bufs index
      (NO_UPSTREAM: up_bufs channel = nil)
      (WRITE_POOL: w_pool = cons ((fence_ch_wp channel), meta) w_pool'):
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (FpgaEvent (Fpga_fence_resp_one channel) index meta))
                 (mkState w_pool' r_pool up_bufs down_bufs sh_mem cpu_bufs)
| fpga_fence_resp_all w_pool w_pool' r_pool up_bufs down_bufs sh_mem cpu_bufs meta index
      (NO_UPSTREAMS: forall c, up_bufs c = nil)
      (WRITE_POOL: w_pool = cons ((fence_all_wp), meta) w_pool'):
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (FpgaEvent (Fpga_fence_resp_all) index meta))
                 (mkState w_pool' r_pool up_bufs down_bufs sh_mem cpu_bufs)
| fpga_flush_read w_pool r_pool head tail up_bufs down_bufs sh_mem cpu_bufs loc channel meta
      (READ_POOL: r_pool = head ++ cons (channel, loc, meta) tail) :
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (FpgaReadToUpstream channel loc meta)
                 (mkState w_pool (head ++ tail) (upd up_bufs channel (up_bufs channel ++ cons(read_up loc, meta) nil)) down_bufs sh_mem cpu_bufs)
| fpga_mem_read w_pool r_pool up_bufs up_buf' down_bufs sh_mem cpu_bufs loc val channel meta
      (UPSTREAM: up_bufs channel = cons ((read_up loc), meta) up_buf')
      (SH_MEM: sh_mem loc = val):
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (FpgaMemRead channel loc val meta)
                 (mkState w_pool r_pool (upd up_bufs channel up_buf') (upd down_bufs channel (down_bufs channel ++ cons (loc, val, meta) nil)) sh_mem cpu_bufs)
| fpga_read_resp w_pool r_pool up_bufs down_bufs down_buf' sh_mem cpu_bufs loc val channel meta index
      (DOWNSTREAM: down_bufs channel = cons (loc, val, meta) down_buf'):
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (FpgaEvent (Fpga_read_resp channel loc val) index meta))
                 (mkState w_pool r_pool up_bufs (upd down_bufs channel down_buf') sh_mem cpu_bufs)
| cpu_write w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs loc val thread index:
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (ThreadEvent thread index (Cpu_store loc val)))
                 (mkState w_pool r_pool up_bufs down_bufs sh_mem (upd cpu_bufs thread (cpu_bufs thread ++ cons (loc, val) nil)))
| cpu_propagate w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs cpu_buf' loc val thread
      (CPU_BUF: cpu_bufs thread = cons (loc, val) cpu_buf'):
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (CpuFlush (thread))
                 (mkState w_pool r_pool up_bufs down_bufs (upd sh_mem loc val) (upd cpu_bufs thread cpu_buf'))
| cpu_read_buf w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs loc val thread index
      (CPU_BUF: latest_buffered (cpu_bufs thread) loc (Some val)):
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (ThreadEvent thread index (Cpu_load loc val)))
                 (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
| cpu_read_mem w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs loc val thread index
      (CPU_BUF: latest_buffered (cpu_bufs thread) loc None)
      (SH_MEM: sh_mem loc = val):
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (ThreadEvent thread index (Cpu_load loc val)))
                 (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
| cpu_fence w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs thread index
      (NO_WB: cpu_bufs thread = nil):
    TSOFPGA_step (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs)
                 (EventLab (ThreadEvent thread index (Cpu_fence)))
                 (mkState w_pool r_pool up_bufs down_bufs sh_mem cpu_bufs).


Definition Minit : SyState := mkState 
  nil
  nil
  (fun _ => nil)
  (fun _ => nil)
  (fun _ => 0)
  (fun _ => nil).

Definition TSOFPGA_lts :=
  {| LTS_init := eq Minit ;
     LTS_step := TSOFPGA_step ;
     LTS_final := ∅ |}.

Definition TSO_trace_wf (t: trace SyLabel) :=
  forall i j d thread index1 index2 lbl1 lbl2
    (LTij: i < j)
    (LTj : NOmega.lt_nat_l j (trace_length t))
    (TR_I: trace_nth i t d = EventLab (ThreadEvent thread index1 lbl1))
    (TR_J: trace_nth j t d = EventLab (ThreadEvent thread index2 lbl2)),
    index1 < index2.
  
Definition FPGA_trace_wf (t: trace SyLabel) :=
  forall i j d index1 index2 lbl1 lbl2 meta1 meta2
    (LTij: i < j)
    (LTj : NOmega.lt_nat_l j (trace_length t))
    (TR_I: trace_nth i t d = EventLab (FpgaEvent lbl1 index1 meta1))
    (TR_J: trace_nth j t d = EventLab (FpgaEvent lbl2 index2 meta2)),
    index1 < index2.

Definition def_lbl: SyLabel := EventLab (InitEvent 0). 

(* Two requests with the same meta must be a pair. This prohibits meta duplication *)
Definition FPGA_trace_pair_unique_wf (t: trace SyLabel) :=
  forall i j index1 index2 fpgaE1 fpgaE2 meta
    (LTij: i < j)
    (LTj : NOmega.lt_nat_l j (trace_length t))
    (TR_I: trace_nth i t def_lbl = EventLab (FpgaEvent fpgaE1 index1 meta))
    (TR_J: trace_nth j t def_lbl = EventLab (FpgaEvent fpgaE2 index2 meta)),
    req_resp_pair (FpgaEvent fpgaE1 index1 meta) (FpgaEvent fpgaE2 index2 meta).



(* The next three conditions cannot be guaranteed by standard fairness in infinite executions *)
(* The operational semantics require changes in order to convert them to standard fairness *)
Definition FPGA_writepair_exists_wf (t: trace SyLabel) := 
  forall i d e1
    (TR_I: trace_nth i t d = EventLab e1)
    (IS_REQ: is_wr_req e1),
  exists j e2, i < j /\ (NOmega.lt_nat_l j (trace_length t)) /\
    trace_nth j t def_lbl = EventLab e2 /\ 
    req_resp_pair e1 e2.

Definition FPGA_fenceonepair_exists_wf (t: trace SyLabel) := 
  forall i d e1
    (TR_I: trace_nth i t d = EventLab e1)
    (IS_REQ: is_fence_req_one e1),
  exists j e2, i < j /\ (NOmega.lt_nat_l j (trace_length t)) /\
    trace_nth j t def_lbl = EventLab e2 /\ 
    req_resp_pair e1 e2.

Definition FPGA_fenceallpair_exists_wf (t: trace SyLabel) := 
  forall i d e1
    (TR_I: trace_nth i t d = EventLab e1)
    (IS_REQ: is_fence_req_all e1),
  exists j e2, i < j /\ (NOmega.lt_nat_l j (trace_length t)) /\
    trace_nth j t def_lbl = EventLab e2 /\ 
    req_resp_pair e1 e2.

Record TSOFPGA_trace_wf (t: trace SyLabel) :=
  {
    TSO_TR_WF : TSO_trace_wf t;
    FPGA_TR_WF : FPGA_trace_wf t;
    PAIR_UNIQUE : FPGA_trace_pair_unique_wf t; 
    WRITEPAIR_EXISTS: FPGA_writepair_exists_wf t;
    FENCEONEPAIR_EXISTS: FPGA_fenceonepair_exists_wf t;
    FENCEALLPAIR_EXISTS: FPGA_fenceallpair_exists_wf t;
  }.    

Definition TSO_hb G := ((ppo G ∪ rfe G ∪ co G ∪ fr G) ∩ (is_cpu × is_cpu))^+. 

(* Record pairs_wf := {
  PAIR_UNIQ : meta_pair_unique;
  REQ_E_RESP : req_exists_resp;
}. *)

(* Experimental *)

Definition is_external (lbl: SyLabel) :=
  match lbl with
  | EventLab (ThreadEvent _ _ _) => True
  | EventLab (FpgaEvent _ _ _) => True
  | _ => False
  end.

Definition proj_ev (lbl: SyLabel) :=
  match lbl with
  | EventLab ev => ev
  | _ => InitEvent 0
  end.


Definition lbl_thread (lbl: SyLabel) :=
  match lbl with
  | EventLab e => tid e
  | FpgaMemFlush _ _ _ _ => FpgaTid
  | FpgaMemRead _ _ _ _ => FpgaTid
  | FpgaReadToUpstream _ _ _ => FpgaTid
  | CpuFlush thread => CpuTid thread
  end.

Definition lbl_chan_opt (lbl: SyLabel) :=
  match lbl with
  | EventLab (FpgaEvent (Fpga_write_req c _ _) _ _) => Some c
  | EventLab (FpgaEvent (Fpga_write_resp c _ _) _ _) => Some c
  | EventLab (FpgaEvent (Fpga_read_req c _) _ _) => Some c
  | EventLab (FpgaEvent (Fpga_read_resp c _ _) _ _) => Some c
  | EventLab (FpgaEvent (Fpga_fence_req_one c) _ _) => Some c
  | EventLab (FpgaEvent (Fpga_fence_resp_one c) _ _) => Some c
  | FpgaMemFlush c _ _ _ => Some c
  | FpgaMemRead c _ _ _ => Some c
  | FpgaReadToUpstream c _ _ => Some c
  (* | EventLab (FpgaEvent (Fpga_fence_req_all) _ _) => Some 0
  | EventLab (FpgaEvent (Fpga_fence_resp_all) _ _) => Some 0 *)
  | _ => None
  end.

Definition in_cpu_thread thread := fun lbl => lbl_thread lbl = CpuTid thread.

Definition in_chan chan := fun lbl => lbl_chan_opt lbl = Some chan.

Definition is_fpga_lab (lbl: SyLabel) :=
  match lbl with
  | EventLab (FpgaEvent _ _ _) => True
  | FpgaMemFlush _ _ _ _ => True
  | FpgaMemRead _ _ _ _ => True
  | FpgaReadToUpstream _ _ _ => True
  | _ => False
  end.

Definition is_cpu_prop (lbl: SyLabel) := match lbl with
  | CpuFlush _ => True
  | _ => False
  end.

Definition is_fpga_prop (lbl: SyLabel) := match lbl with
  | FpgaMemFlush _ _ _ _ => True
  | _ => False
  end.

Definition is_fpga_memread (lbl: SyLabel) := match lbl with
  | FpgaMemRead _ _ _ _ => True
  | _ => False
  end.

Definition is_prop := is_cpu_prop ∪₁ is_fpga_prop.

Definition cpu_write' (lbl: SyLabel) := match lbl with
  | EventLab (ThreadEvent _ _ (Cpu_store _ _)) => True
  | _ => False
end.

Definition cpu_read' (lbl: SyLabel) := match lbl with
  | EventLab (ThreadEvent _ _ (Cpu_load _ _)) => True
  | _ => False
end.

Definition fpga_write' (lbl: SyLabel) := match lbl with
  | EventLab (FpgaEvent (Fpga_write_resp _ _ _) _ _) => True
  | _ => False
end.

Definition fpga_read_resp' (lbl: SyLabel) := match lbl with
  | EventLab (FpgaEvent (Fpga_read_resp _ _ _) _ _) => True
  | _ => False
end.

Definition fpga_read_req' (lbl: SyLabel) := match lbl with
  | EventLab (FpgaEvent (Fpga_read_req _ _) _ _) => True
  | _ => False
end.


Definition fpga_write_req' (lbl: SyLabel) := match lbl with
  | EventLab (FpgaEvent (Fpga_write_req _ _ _) _ _) => True
  | _ => False
end.

Definition fpga_mem_read' (lbl: SyLabel) := match lbl with
  | FpgaMemRead _ _ _ _=> True
  | _ => False
end.

Definition fpga_read_ups' (lbl: SyLabel) := match lbl with
  | FpgaReadToUpstream _ _ _ => True
  | _ => False
end.

Definition meta_l (lbl: SyLabel) := match lbl with
  | EventLab e => meta e
  | FpgaMemFlush _ _ _ m => m
  | FpgaMemRead _ _ _ m => m
  | FpgaReadToUpstream _ _ m => m
  | CpuFlush _ => 0
  end.

Definition loc_l (lbl: SyLabel) := match lbl with
  | EventLab e => loc e
  | FpgaMemFlush _ l _ _ => l
  | FpgaMemRead _ l _ _ => l
  | FpgaReadToUpstream _ l _ => l
  | CpuFlush _ => 0
  end.

Definition val_l (lbl: SyLabel) := match lbl with
  | EventLab (ThreadEvent _ _ (Cpu_store _ v)) => v
  | EventLab (ThreadEvent _ _ (Cpu_load _ v)) => v
  | EventLab (FpgaEvent (Fpga_write_resp _ _ v) _ _) => v
  | EventLab (FpgaEvent (Fpga_read_resp _ _ v) _ _) => v
  | EventLab (FpgaEvent (Fpga_write_req _ _ v) _ _) => v
  | FpgaMemFlush _ _ v _ => v
  | FpgaMemRead _ _ v _ => v
  | _ => 0
  end.

Definition fpga_up_prop := fpga_read_ups' ∪₁ fpga_write'.
Definition fpga_any_mem_prop := fpga_mem_read' ∪₁ is_fpga_prop.
Definition write' := cpu_write' ∪₁ fpga_write'.

Definition enabled_cpu st tid := exists st', TSOFPGA_step st (CpuFlush tid) st'. 
Definition TSO_fair tr st :=
  forall i tid
    (DOM_EXT: NOmega.le (NOnum i) (trace_length tr)) (* le accounts for the final state if any*)
    (ENABLED: enabled_cpu (st i) tid),
  exists j, i <= j /\ (NOmega.lt_nat_l j (trace_length tr)) /\
       trace_nth j tr def_lbl = CpuFlush tid.

Definition enabled_readpool st chan loc meta := exists st', TSOFPGA_step st (FpgaReadToUpstream chan loc meta) st'.
Definition readpool_fair tr st :=
  forall i chan loc meta
    (DOM_EXT: NOmega.le (NOnum i) (trace_length tr)) (* le accounts for the final state if any*)
    (ENABLED: enabled_readpool (st i) chan loc meta),
  exists j, i <= j /\ (NOmega.lt_nat_l j (trace_length tr)) /\
       trace_nth j tr def_lbl = FpgaReadToUpstream chan loc meta.

Definition mem_flush_fair_alt tr := forall chan,
  trace_length (trace_filter (fpga_write' ∩₁ in_chan chan) tr) =
  trace_length (trace_filter (is_fpga_prop ∩₁ in_chan chan) tr).

Definition downstream_fair_alt tr := forall chan,
  trace_length (trace_filter (fpga_read_resp' ∩₁ in_chan chan) tr) =
  trace_length (trace_filter (fpga_mem_read' ∩₁ in_chan chan) tr).

Definition mem_read_fair_alt tr := forall chan,
  trace_length (trace_filter (fpga_read_ups' ∩₁ in_chan chan) tr) =
  trace_length (trace_filter (fpga_mem_read' ∩₁ in_chan chan) tr).

Definition upstream_combined_fair_alt tr := forall chan,
  trace_length (trace_filter (fpga_up_prop ∩₁ in_chan chan) tr) =
  trace_length (trace_filter (fpga_any_mem_prop ∩₁ in_chan chan) tr).

Definition enabled_mem_flush st chan loc val meta := exists st', TSOFPGA_step st (FpgaMemFlush chan loc val meta) st'.
Definition mem_flush_fair tr st :=
  forall i chan loc val meta
    (DOM_EXT: NOmega.le (NOnum i) (trace_length tr)) (* le accounts for the final state if any*)
    (ENABLED: enabled_mem_flush (st i) chan loc val meta),
  exists j, i <= j /\ (NOmega.lt_nat_l j (trace_length tr)) /\
       trace_nth j tr def_lbl = FpgaMemFlush chan loc val meta.


Definition enabled_memread st chan loc val meta := exists st', TSOFPGA_step st (FpgaMemRead chan loc val meta) st'.
Definition memread_fair tr st :=
  forall i chan loc val meta
    (DOM_EXT: NOmega.le (NOnum i) (trace_length tr)) (* le accounts for the final state if any*)
    (ENABLED: enabled_memread (st i) chan loc val meta),
  exists j, i <= j /\ (NOmega.lt_nat_l j (trace_length tr)) /\
       trace_nth j tr def_lbl = FpgaMemRead chan loc val meta.

Definition enabled_memwrite st chan loc val meta := exists st', TSOFPGA_step st (FpgaMemFlush chan loc val meta) st'.
Definition memwrite_fair tr st :=
  forall i chan loc val meta
    (DOM_EXT: NOmega.le (NOnum i) (trace_length tr)) (* le accounts for the final state if any*)
    (ENABLED: enabled_memwrite (st i) chan loc val meta),
  exists j, i <= j /\ (NOmega.lt_nat_l j (trace_length tr)) /\
       trace_nth j tr def_lbl = FpgaMemFlush chan loc val meta.

End TSOFPGA.

Ltac unfolder' := unfold set_compl, cross_rel, fpga_up_prop, fpga_any_mem_prop, write', cpu_write', cpu_read', fpga_write', fpga_read_ups', fpga_read_req', fpga_write_req', fpga_read_resp', fpga_mem_read', is_cpu_wr, set_minus, set_inter, set_union, is_init, is_prop, is_fpga_prop, is_cpu_prop, def_lbl, in_cpu_thread, lbl_thread, same_loc, loc, tid, is_req, is_rd_req, is_r, is_w, is_resp, is_rd_resp, is_wr_req, is_wr_resp, is_fence_req_one, is_fence_resp_one, is_fence_req_all, is_fence_resp_all, req_resp_pair in *.

Section TSOFPGA_Facts.

Lemma reg_write_structure tlab (W: cpu_write' tlab):
  exists thread index loc val, tlab = EventLab (ThreadEvent thread index (Cpu_store loc val)).
Proof.
  unfolder'. 
  destruct tlab eqn:WW.
  2: { vauto. }
  destruct e. 
  all: try (destruct e; intuition; eauto).
  all: try vauto.
Qed.

Lemma fpga_read_req_structure tlab (R: fpga_read_req' tlab):
  exists chan index meta loc, tlab = EventLab (FpgaEvent (Fpga_read_req chan loc) index meta).
Proof.
  unfolder'. 
  destruct tlab eqn:WW; vauto.
  destruct e; vauto.
  destruct e; vauto.
  exists c, index, m, x.
  auto.
Qed.

Lemma fpga_write_req_structure tlab (W: fpga_write_req' tlab):
  exists chan index meta loc val, tlab = EventLab (FpgaEvent (Fpga_write_req chan loc val) index meta).
Proof.
  unfolder'. 
  destruct tlab eqn:WW; vauto.
  destruct e; vauto.
  destruct e; vauto.
  exists c, index, m, x, v.
  auto.
Qed.

Lemma fpga_write_structure tlab (W: fpga_write' tlab):
  exists chan loc val index meta, tlab = EventLab (FpgaEvent (Fpga_write_resp chan loc val) index meta).
Proof.
  unfolder'. 
  destruct tlab eqn:WW; vauto.
  destruct e; vauto.
  destruct e; vauto.
  exists c, x, v, index, m.
  auto.
Qed.

Lemma fpga_read_structure tlab (R: fpga_read_resp' tlab):
  exists chan index meta loc val, tlab = EventLab (FpgaEvent (Fpga_read_resp chan loc val) index meta).
Proof.
  unfolder'.
  destruct tlab eqn:WW; vauto.
  destruct e; vauto.
  destruct e; vauto.
  exists c, index, m, x, v.
  reflexivity.
Qed.

Lemma fpga_memread_structure tlab (R: fpga_mem_read' tlab):
  exists chan loc val meta, tlab = FpgaMemRead chan loc val meta.
Proof.
  unfolder'.
  destruct tlab eqn:WW; vauto; eauto.
Qed.

Lemma fpga_rflush_structure tlab (R: fpga_read_ups' tlab):
  exists chan loc meta, tlab = FpgaReadToUpstream chan loc meta.
Proof.
  unfolder'.
  destruct tlab eqn:WW; vauto; eauto.
Qed.

Lemma fpga_memflush_structure tlab (R: is_fpga_prop tlab):
  exists chan loc val meta, tlab = FpgaMemFlush chan loc val meta.
Proof.
  unfolder'.
  destruct tlab eqn:WW; vauto; eauto.
Qed.

Lemma init_non_r r (Rr: is_r r) (INIT: is_init r): False.
Proof. generalize Rr, INIT. unfolder'. by destruct r. Qed. 

End TSOFPGA_Facts.
