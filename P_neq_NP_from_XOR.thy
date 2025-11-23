theory P_neq_NP_from_LR
  imports SubsetSum_CookLevin
begin

definition P_eq_NP :: bool where
  "P_eq_NP ⟷ (∀L::language. (L ∈ 𝒫) = (L ∈ 𝒩𝒫))"

text ‹
  Global meta-assumptions wrapping the LR-read lower bound into a
  conditional P ≠ NP statement.

  We fix an NP-side encoding @{term enc0} for SUBSET-SUM and assume:

    • @{term "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"} (NP membership),

    • If @{term "SUBSETSUM_lang enc0 ∈ 𝒫"}, then there exists a
      Cook–Levin machine @{term M} with some CL encoding @{term enc_CL}
      and an equation-based solver structure
      (@{locale Eq_ReadLR_SubsetSum_Solver}), such that the machine runs
      in polynomial time,

    • Any such equation-based, polynomial-time solver satisfies the
      LR-Read structural property (@{locale LR_Read_TM}).

  Under these assumptions we derive @{term "¬ P_eq_NP"}.
›

locale Global_LR_Assumptions =
  fixes enc0 :: "int list ⇒ int ⇒ string"   (* NP-side SUBSET-SUM encoding *)
  assumes SUBSETSUM_in_NP_global:
    "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  (* P ⇒ existence of an equation-based, polytime SUBSET-SUM solver *)
  assumes P_impl_eq_readlr_CL_global:
    "SUBSETSUM_lang enc0 ∈ 𝒫 ⟹
       ∃M q0 enc_CL lhs rhs L_zone R_zone.
         Eq_ReadLR_SubsetSum_Solver M q0 enc_CL lhs rhs L_zone R_zone ∧
         polytime_CL_machine M enc_CL"
  (* Bridge: any such solver satisfies the LR_Read_TM structural axiom *)
  assumes eq_to_LR_Read_TM_global:
    "⋀M q0 enc_CL lhs rhs L_zone R_zone.
       Eq_ReadLR_SubsetSum_Solver M q0 enc_CL lhs rhs L_zone R_zone ⟹
       polytime_CL_machine M enc_CL ⟹
       LR_Read_TM M q0 enc_CL"

context Global_LR_Assumptions
begin

lemma no_polytime_LR_CL:
  shows "¬ (∃M q0 enc_CL.
             polytime_CL_machine M enc_CL ∧
             LR_Read_TM M q0 enc_CL)"
proof
  assume ex:
    "∃M q0 enc_CL.
       polytime_CL_machine M enc_CL ∧
       LR_Read_TM M q0 enc_CL"
  then obtain M q0 enc_CL where
    poly: "polytime_CL_machine M enc_CL" and
    lr:   "LR_Read_TM M q0 enc_CL"
    by blast

  interpret LR: LR_Read_TM M q0 enc_CL
    by (rule lr)

  from poly obtain c d where
    cpos: "c > 0" and
    bound_all: "∀as s. steps_CL M (enc_CL as s)
                       ≤ nat (ceiling (c * (real (length as)) ^ d))"
    unfolding polytime_CL_machine_def by blast

  have family_bound:
    "∃(c::real)>0. ∃d::nat.
       ∀as s. distinct_subset_sums as ⟶
         steps_CL M (enc_CL as s)
           ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using cpos bound_all by blast

  from LR.no_polytime_CL_on_distinct_family family_bound
  show False by blast
qed

theorem P_neq_NP_from_LR:
  "¬ P_eq_NP"
proof
  assume eq: P_eq_NP

  (* From P = NP and SUBSETSUM_lang enc0 ∈ NP, we get SUBSETSUM_lang enc0 ∈ P. *)
  have inP_SUBSETSUM: "SUBSETSUM_lang enc0 ∈ 𝒫"
    using eq SUBSETSUM_in_NP_global
    unfolding P_eq_NP_def by metis

  (* By the modelling assumption, this yields an equation-based, polytime CL solver. *)
  from P_impl_eq_readlr_CL_global[OF inP_SUBSETSUM]
  obtain M q0 enc_CL lhs rhs L_zone R_zone where
    solver: "Eq_ReadLR_SubsetSum_Solver M q0 enc_CL lhs rhs L_zone R_zone" and
    poly:   "polytime_CL_machine M enc_CL"
    by blast

  (* Bridge: such a solver satisfies the LR_Read_TM structural axiom. *)
  from eq_to_LR_Read_TM_global[OF solver poly]
  have lr: "LR_Read_TM M q0 enc_CL" .

  (* Package it as a witness for the existential that no_polytime_LR_CL forbids. *)
  have ex_solver:
    "∃M q0 enc_CL.
       polytime_CL_machine M enc_CL ∧
       LR_Read_TM M q0 enc_CL"
    using poly lr by blast

  from no_polytime_LR_CL ex_solver
  show False by blast
qed

end  (* context Global_LR_Assumptions *)

text ‹Non-locale exported version:

  If some encoding @{term enc0} and assumptions
  @{term "Global_LR_Assumptions enc0"} hold, then P ≠ NP.
›

theorem P_neq_NP_from_LR_global:
  assumes "Global_LR_Assumptions enc0"
  shows "¬ P_eq_NP"
proof -
  interpret Global_LR_Assumptions enc0 by fact
  from P_neq_NP_from_LR show ?thesis .
qed

end  (* theory *)
