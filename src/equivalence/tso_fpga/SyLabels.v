Section SyLabels.

Definition Chan := nat.
Inductive Tid :=
    | CpuTid (n : nat)
    | FpgaTid
    | InitTid.

Definition Loc := nat.
Definition Val := nat.

Definition Mdata := nat.

End SyLabels.