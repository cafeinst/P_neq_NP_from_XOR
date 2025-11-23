theory P_neq_NP_from_XOR
  imports SubsetSum_CookLevin
begin

text ‹
  This theory packages global meta-assumptions needed to turn the
  LR-read lower bound for SUBSET-SUM into a conditional proof that
  @{term "¬ P_eq_NP"}, following the structure developed in
  theory ‹SubsetSum_CookLevin›.

  We work with an abstract NP-side encoding @{term enc0} and assume:

    • SUBSETSUM_lang enc0 ∈ NP,
    • If SUBSETSUM_lang enc0 ∈ P, then there is an equation-based
      Cook–Levin solver for SUBSET-SUM (with some CL encoding enc),
    • Any such equation-based, polynomial-time solver induces an
      LR_Read_TM instance (bridge assumption).
›

locale Global_XOR_Assumptions =
  fixes enc0 :: "int list ⇒ int ⇒ string"  (* NP-level SUBSET-SUM encoding *)
  assumes xor_read_axiom_global:
    "⋀M q0 enc A B A_zone B_zone as s.
       hard_pair_distinct as s ⟹
       XOR_Solver_CL M q0 enc A B A_zone B_zone ⟹
       polytime_CL_machine M enc ⟹
       read0_CL M (enc as s) ∩ A_zone as s ≠ {} ∧
       read0_CL M (enc as s) ∩ B_zone as s ≠ {}"
  assumes eq_to_LR_Read_TM_global:
    "⋀M q0 enc lhs rhs L_zone R_zone.
       Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ⟹
       polytime_CL_machine M enc ⟹
       LR_Read_TM M q0 enc"
  assumes SUBSETSUM_in_NP_global:
    "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
  assumes P_impl_eq_readlr_CL_global:
    "SUBSETSUM_lang enc0 ∈ 𝒫 ⟹
       ∃M q0 enc lhs rhs L_zone R_zone.
         Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ∧
         polytime_CL_machine M enc"

context Global_XOR_Assumptions
begin

text ‹First, reprove: there is no polynomial-time equation-based
  Cook–Levin solver for SUBSET-SUM.›

lemma no_polytime_eq_readlr_solver:
  "¬ (∃M q0 enc lhs rhs L_zone R_zone.
        Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ∧
        polytime_CL_machine M enc)"
proof
  assume ex:
    "∃M q0 enc lhs rhs L_zone R_zone.
       Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ∧
       polytime_CL_machine M enc"
  then obtain M q0 enc lhs rhs L_zone R_zone where
    solver: "Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone" and
    poly:   "polytime_CL_machine M enc"
    by blast

  text ‹The bridge assumption gives us an LR_Read_TM instance
    for this particular machine M and encoding enc.›
  from eq_to_LR_Read_TM_global[OF solver poly]
  have lr: "LR_Read_TM M q0 enc" .

  interpret LR: LR_Read_TM M q0 enc
    by (rule lr)

  text ‹From polynomial-time on all inputs we get polynomial-time
    on the distinct-subset-sums family.›

  from poly obtain c d where
    cpos: "c > 0" and
    bound_all: "∀as s. steps_CL M (enc as s)
                       ≤ nat (ceiling (c * (real (length as)) ^ d))"
    unfolding polytime_CL_machine_def by blast

  have family_bound:
    "∃(c::real)>0. ∃d::nat.
       ∀as s. distinct_subset_sums as ⟶
         steps_CL M (enc as s)
           ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using cpos bound_all by blast

  text ‹But LR_Read_TM tells us no such polynomial bound exists
    on the distinct-subset-sums family.›

  from LR.no_polytime_CL_on_distinct_family family_bound
  show False by blast
qed

text ‹Now the conditional P ≠ NP statement under the global assumptions.›

theorem P_neq_NP_from_XOR:
  "¬ P_eq_NP"
proof
  assume eq: P_eq_NP

  text ‹From P = NP and SUBSETSUM_lang enc0 ∈ NP, we get
    SUBSETSUM_lang enc0 ∈ P.›
  have inP_SUBSETSUM: "SUBSETSUM_lang enc0 ∈ 𝒫"
    using eq SUBSETSUM_in_NP_global
    unfolding P_eq_NP_def by metis

  text ‹By the modelling assumption, this yields an equation-based
    Cook–Levin solver for SUBSET-SUM (with some CL encoding enc).›
  from P_impl_eq_readlr_CL_global[OF inP_SUBSETSUM]
  obtain M q0 enc lhs rhs L_zone R_zone where
    solver: "Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone" and
    poly:   "polytime_CL_machine M enc"
    by blast

  text ‹Package this solver as a witness for the existential that
    ‹no_polytime_eq_readlr_solver› rules out.›
  have ex_solver:
    "∃M q0 enc lhs rhs L_zone R_zone.
       Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ∧
       polytime_CL_machine M enc"
    using solver poly by blast

  from no_polytime_eq_readlr_solver ex_solver
  show False by blast
qed

end  (* context Global_XOR_Assumptions *)

text ‹Finally, export a non-locale version:
  If some encoding ‹enc0› and assumptions ‹Global_XOR_Assumptions enc0› hold,
  then P ≠ NP.
›

theorem P_neq_NP_from_XOR_global:
  assumes "Global_XOR_Assumptions enc0"
  shows "¬ P_eq_NP"
proof -
  interpret Global_XOR_Assumptions enc0 by fact
  from P_neq_NP_from_XOR show ?thesis .
qed

end  (* theory *)
