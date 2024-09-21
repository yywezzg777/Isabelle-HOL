theory FTDL_local 
  imports Main FTDL FTDL_correct
begin



locale FTDL = 
  fixes Entity_behavior    :: "behavior \<Rightarrow> entity \<Rightarrow> entity"
  fixes Entity_activation  :: "entity_name \<Rightarrow> DVE \<Rightarrow> DVE"
  fixes Exe_beh            ::"behavior \<Rightarrow> entity list \<Rightarrow> entity list"
  fixes Choose_task        :: "dynamic_entity \<Rightarrow> task_name \<Rightarrow> task list \<Rightarrow> task" 
  fixes Execute_multitasks :: "task list \<Rightarrow> DVE \<Rightarrow> DVE"
  fixes Modify_tasklist    :: "task list \<Rightarrow> DVE \<Rightarrow> task list"
  fixes Modify_DVE         :: "task list \<Rightarrow> DVE \<Rightarrow> DVE"
  fixes Get_behlist        :: "task list \<Rightarrow> behavior list"
 
  assumes entity_behavior:"Entity_behavior beh e = heb_expand beh e"
  assumes act_ENT:        "act_state (e#es)\<Longrightarrow>name_uni (e#es) \<Longrightarrow>
                           act_condlist en (e#es) \<Longrightarrow> success_act en (Entity_activation en (e#es))"
  assumes choose_task:    "choose_condlist tn ts \<Longrightarrow> fst(Choose_task de tn ts) = tn"
  assumes excl_Cond1 :    "no_eq_beh beh1 beh2 \<Longrightarrow>prop_T t \<Longrightarrow>
                           include_beh t beh1 \<and> include_beh t beh2 \<Longrightarrow>
                           (cont_beh beh1 (Get_behlist [t]) \<and> cont_beh beh2 (Get_behlist [t])) = False"
  assumes excl_Cond2:"prop_T t1 \<and> prop_T t2 \<and> prop_E e \<Longrightarrow>
                      eq_beh beh1 beh2 \<Longrightarrow>
                      include_beh t1 beh1 \<and> include_beh t2 beh2 \<Longrightarrow>
                      beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e \<Longrightarrow>
                      Get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> exe_req beh2 (is_executing beh1 e) = False"
  assumes excl_Cond3:"prop_T t1 \<and> prop_T t2 \<and> prop_E e \<Longrightarrow>
                      no_eq_beh beh1 beh2 \<Longrightarrow>
                      include_beh t1 beh1 \<and> include_beh t2 beh2 \<Longrightarrow>
                      beh_obj beh1 e \<and> beh_obj beh2 e \<and> beh_re beh1 e \<Longrightarrow>
                      Get_behlist [t1,t2] = [beh1,beh2] \<Longrightarrow> exe_req beh2 (is_executing beh1 e) = False"

interpretation S: FTDL
  where Entity_behavior = entity_behavior and Entity_activation = entity_activation 
  and Exe_beh = exe_beh and Choose_task = choose_task and Execute_multitasks = execute_multitasks
  and Modify_tasklist = modify_tasklist and Modify_DVE = modify_DVE and Get_behlist = get_behlist


proof (standard, goal_cases)
  case (1 beh e)
  then show ?case
    by (simp add: beh_Correct) 
next
  case (2 e es en)
  then show ?case
    using act_Ent by blast 
next
  case (3 tn ts de)
  then show ?case
    by (simp add: choose_Correct) 
next
  case (4 beh1 beh2 t)
  then show ?case
    using excl_Cond1 by blast 
next
  case (5 t1 t2 e beh1 beh2)
  then show ?case
    using excl_Cond22 by blast 
next
  case (6 t1 t2 e beh1 beh2)
  then show ?case
    using excl_Cond33 by blast 
qed


(*

proof (standard, goal_cases)
  
*)









end