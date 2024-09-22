theory FTDL_local2 
  imports Main FTDL FTDL_correct
begin

definition act_cond2::"entity_name \<Rightarrow> entity list \<Rightarrow> bool"where"
act_cond2 en es = (act_state es \<and> name_uni es \<and>
                           act_condlist en es)"

definition excl_cond1::"task \<Rightarrow> behavior \<Rightarrow> behavior \<Rightarrow> bool"where"
excl_cond1 t beh1 beh2 = (no_eq_beh beh1 beh2 \<and>prop_T t \<and>
                           include_beh t beh1 \<and> include_beh t beh2)"

definition excl_cond2::"task \<Rightarrow> task \<Rightarrow> entity \<Rightarrow> behavior \<Rightarrow> behavior \<Rightarrow> bool"where"
excl_cond2 t1 t2 e beh1 beh2 = (prop_T t1 \<and> prop_T t2 \<and> prop_E e \<and>
                      eq_beh beh1 beh2 \<and>
                      include_beh t1 beh1 \<and> include_beh t2 beh2 \<and>
                      beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e)"

definition excl_cond3::"task \<Rightarrow> task \<Rightarrow> entity \<Rightarrow> behavior \<Rightarrow> behavior \<Rightarrow> bool"where"
excl_cond3 t1 t2 e beh1 beh2 = (prop_T t1 \<and> prop_T t2 \<and> prop_E e \<and>
                      no_eq_beh beh1 beh2 \<and>
                      include_beh t1 beh1 \<and> include_beh t2 beh2 \<and>
                      beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e)"

definition success_activation::"entity_name \<Rightarrow> entity list \<Rightarrow> bool"where"
success_activation en es = success_act en (entity_activation en es)"

definition exe_request ::"behavior \<Rightarrow> behavior \<Rightarrow> entity \<Rightarrow> bool"where"
exe_request beh1 beh2 e = (exe_req beh2 (is_executing beh1 e) = False)"

definition entity_beh::"behavior \<Rightarrow> entity \<Rightarrow> bool"where"
entity_beh beh e = (entity_behavior beh e = heb_expand beh e)"


locale FTDL = 
  fixes Entity_beh    :: "'b \<Rightarrow> 'e \<Rightarrow> bool"
  fixes Act_cond           :: "'en \<Rightarrow> 'e list \<Rightarrow> bool"
  fixes Success_activation :: "'en \<Rightarrow> 'e list \<Rightarrow> bool"
  fixes Exe_beh            :: "'b \<Rightarrow> 'DVE \<Rightarrow> 'DVE"
  fixes Choose_cond        :: "task_name \<Rightarrow> 't list \<Rightarrow> bool"
  fixes Choose_task        :: "'de \<Rightarrow> task_name \<Rightarrow> 't list \<Rightarrow> task"
  fixes Get_behlist        :: "'t list \<Rightarrow> 'b list"
  fixes Cont_beh           :: "'b \<Rightarrow> 'b list \<Rightarrow> bool"
  fixes Excl_cond1         :: "'t \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  fixes Excl_cond2         :: "'t \<Rightarrow> 't \<Rightarrow> 'e \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  fixes Excl_cond3         :: "'t \<Rightarrow> 't \<Rightarrow> 'e \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  fixes Exe_request        :: "'b \<Rightarrow> 'b \<Rightarrow> 'e \<Rightarrow> bool"
  fixes Execute_multitasks :: "'tl \<Rightarrow> 'DVE \<Rightarrow> 'DVE"
 
  assumes entity_beh:     "Entity_beh beh e"
  assumes act_entity:     "Act_cond en (e#es) \<Longrightarrow> Success_activation en (e#es)"
  assumes choose_task:    "Choose_cond tn ts \<Longrightarrow> fst(Choose_task de tn ts) = tn"
  assumes excl_Cond1 :    "Excl_cond1 t beh1 beh2 \<Longrightarrow>
                           (Cont_beh beh1 (Get_behlist [t]) \<and> Cont_beh beh2 (Get_behlist [t])) = False"
  assumes excl_Cond2:     "Excl_cond2 t1 t2 e beh1 beh2\<Longrightarrow>
                           Get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> Exe_request beh1 beh2 e"
  assumes excl_Cond3:     "Excl_cond3 t1 t2 e beh1 beh2 \<Longrightarrow>
                           Get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> Exe_request beh1 beh2 e"

interpretation S: FTDL
  where Entity_beh = entity_beh and Act_cond = act_cond2 and Success_activation = success_activation
and Exe_beh = exe_beh
and Choose_cond = choose_condlist   and Choose_task = choose_task and Execute_multitasks = execute_multitasks
 and Get_behlist = get_behlist and Excl_cond1 =excl_cond1 and Excl_cond2 = excl_cond2 and Excl_cond3 = excl_cond3
and Cont_beh = cont_beh and Exe_request = exe_request


proof (standard, goal_cases)
  case (1 beh e)
  then show ?case
    apply (simp add: entity_beh_def)
    by (simp add: beh_Correct) 
next
  case (2 e es en)
  then show ?case
    apply (simp add: act_cond2_def)
    using "2" act_Ent act_cond2_def success_activation_def by blast
next
  case (3 tn ts de)
  then show ?case
    by (simp add: choose_Correct) 
next
  case (4 beh1 beh2 t)
  then show ?case
    using excl_Cond1 excl_cond1_def by blast

next
  case (5 t1 t2 e beh1 beh2)
  then show ?case
    using excl_Cond22 excl_cond2_def exe_request_def by blast

next
  case (6 t1 t2 e beh1 beh2)
  then show ?case
    by (meson excl_Cond33 excl_cond3_def exe_request_def)
qed


(*

proof (standard, goal_cases)
  
*)









end